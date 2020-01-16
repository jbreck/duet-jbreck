open Core
open Apak
open CfgIr
open Srk

include Log.Make(struct let name = "chorac" end)

module RG = Interproc.RG
module G = RG.G

module K = NewtonDomain.K
module KK = NewtonDomain.KK

module Ctx = NewtonDomain.Ctx

module Var = Cra.V
module VarSet = BatSet.Make(Cra.V)

module A = Interproc.MakePathExpr(K)

module IntPair = struct
  type t = int * int [@@deriving ord]
  let equal (x,y) (x',y') = (x=x' && y=y')
  let hash = Hashtbl.hash
end
module IntPairMap = BatMap.Make(IntPair)
module IntPairSet = BatSet.Make(IntPair)

module AuxVarModuleC = struct
  type val_t = Cra.value
  type val_sym = { 
      value: Cra.value; 
      symbol: Srk.Syntax.symbol
  }
  let make_aux_variable name = 
    let new_var = Core.Var.mk (Core.Varinfo.mk_global name (Core.Concrete (Core.Int 32))) in 
    let new_var_val = Cra.VVal new_var in 
    (* NOTE: in the following line, the function symbol_of puts a symbol into the hash table *)
    let new_var_sym = Cra.V.symbol_of new_var_val in 
    {value  = new_var_val;
     symbol = new_var_sym}
  type height_model_type = 
      (* Root to baseline of tree *)
      | RB of val_sym 
      (* Root to baseline, root to midline, midline to baseline *)
      (*   where the midline is defined as the depth of the shallowest leaf *)
      | RB_RM_MB of val_sym * val_sym * val_sym 

  let is_var_global x = 
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false (* false *)

  let post_symbol =
    Memo.memo (fun sym ->
      match Var.of_symbol sym with
      | Some var ->
        Srk.Syntax.mk_symbol Cra.srk ~name:(Var.show var ^ "'") (Var.typ var :> Srk.Syntax.typ)
      | None -> assert false)

  type srk_ctx_magic = Cra.Ctx.t
  let srk = Cra.srk

end

let procedure_names_map = ref IntPairMap.empty

module ProcModuleC = struct
  module ProcMap = IntPairMap

  let proc_name_triple_string (entry,exit) = 
    if ProcMap.mem (entry,exit) !procedure_names_map then 
      let name = ProcMap.find (entry,exit) !procedure_names_map in
      Format.sprintf "(%d,%d,\"%s\")" entry exit name
    else
      Format.sprintf "(%d,%d,?)" entry exit
  
  let proc_name_string (entry,exit) = 
    if ProcMap.mem (entry,exit) !procedure_names_map then 
      let name = ProcMap.find (entry,exit) !procedure_names_map in
      Format.sprintf "%s" name
    else
      Format.sprintf "<unknown procedure(%d,%d)>" entry exit
end

module ChoraC = ChoraCore.MakeChoraCore(ProcModuleC)(AuxVarModuleC)

open ChoraC

(* ugly: copied from newtonDomain just for debugging *)
let print_indented ?(level=`info) indent k =
  logf ~level:level "%a"
  (fun f () -> Format.printf "%s"
    (SrkUtil.mk_show (fun formatter tr ->
      Format.pp_open_vbox formatter indent;
      Format.pp_print_break formatter 0 0;
      Format.fprintf formatter "%a" K.pp tr;
      Format.pp_close_box formatter ()) k)) ()

let log_tr_proc ?(level=`info) formatter p_entry p_exit tr = 
  logf ~level formatter (proc_name_triple_string (p_entry,p_exit));
  print_indented 17 tr;
  logf ~level "@."

(* ---------------------------------- *)
(*    Begin stuff from old pathexpr   *)

module NPathexpr = struct
  open BatHashcons
  
  type 'a open_pathexpr =
    [ `Edge of int * int
    | `Mul of 'a * 'a
    | `Add of 'a * 'a
    | `Star of 'a
    | `Zero
    | `One ]
  
  type 'a algebra = 'a open_pathexpr -> 'a
  
  type pe =
    | Edge of int * int
    | Mul of t * t
    | Add of t * t
    | Star of t
    | One
    | Zero
  and t = pe hobj
  
  module HC = BatHashcons.MakeTable(struct
      type t = pe
      let equal x y = match x, y with
        | One, One | Zero, Zero -> true
        | Edge (s, t), Edge (s', t') -> s = s' && t = t'
        | Mul (s, t), Mul (s', t') -> s.tag = s'.tag && t.tag = t'.tag
        | Add (s, t), Add (s', t') -> s.tag = s'.tag && t.tag = t'.tag
        | Star t, Star t' -> t.tag = t'.tag
        | _ -> false
      let hash = function
        | Edge (x, y) -> Hashtbl.hash (0, x, y)
        | Mul (x, y) -> Hashtbl.hash (1, x.tag, y.tag)
        | Add (x, y) -> Hashtbl.hash (2, x.tag, y.tag)
        | Star x -> Hashtbl.hash (3, x.tag)
        | Zero -> Hashtbl.hash 4
        | One -> Hashtbl.hash 5
    end)
  module HT = BatHashtbl.Make(struct
      type t = pe hobj
      let equal s t = s.tag = t.tag
      let hash t = t.hcode
    end)
  
  type context = HC.t
  type 'a table = 'a HT.t
  
  let mk_one pe = HC.hashcons pe One
  let mk_zero pe = HC.hashcons pe Zero
  let mk_mul pe x y = match x.obj, y.obj with
    | Zero, _ | _, Zero -> mk_zero pe
    | One, _ -> y
    | _, One -> x
    | _, _ ->
      HC.hashcons pe (Mul (x, y))
  let mk_add pe x y = match x.obj, y.obj with
    | Zero, _ -> y
    | _, Zero -> x
    | _, _ -> HC.hashcons pe (Add (x, y))
  let mk_star pe x = HC.hashcons pe (Star x)
  
  let mk_star_simplify pe x = match x.obj with
    | Zero -> mk_one pe
    | One -> mk_one pe
    | _ -> HC.hashcons pe (Star x)
  
  let mk_edge pe src tgt = HC.hashcons pe (Edge (src, tgt))
  
  let rec pp formatter pathexpr =
    let open Format in
    match pathexpr.obj with
    | Edge (x, y) -> fprintf formatter "@[%d->%d@]" x y
    | Mul (x, y) -> fprintf formatter "@[(%a)@ . (%a)@]" pp x pp y
    | Add (x, y) -> fprintf formatter "@[%a@ + %a@]" pp x pp y
    | Star x -> fprintf formatter "@[(%a)*@]" pp x
    | Zero -> fprintf formatter "0"
    | One -> fprintf formatter "1"
  
  let mk_table ?(size=991) () = HT.create size      
  let mk_context ?(size=991) () = HC.create size
  
  let eval ?(table=HT.create 991) (f : 'a open_pathexpr -> 'a) =
    let rec go expr =
      if HT.mem table expr then
        HT.find table expr
      else
        let result =
          match expr.obj with
          | One -> f `One
          | Zero -> f `Zero
          | Mul (x, y) -> f (`Mul (go x, go y))
          | Add (x, y) -> f (`Add (go x, go y))
          | Star x -> f (`Star (go x))
          | Edge (s, t) -> f (`Edge (s, t)) 
        in
        HT.add table expr result;
        result
    in
    go
  
  let forget table p =
    let safe = eval (function
        | `One | `Zero -> true
        | `Edge (s, t) -> p s t
        | `Mul (x, y) | `Add (x, y) -> x && y
        | `Star x -> x)
    in
    HT.filteri_inplace (fun k _ -> safe k) table
end

(*     End stuff from old pathexpr    *)
(* ---------------------------------- *)



(* ---------------------------------- *)
(*   Begin stuff from old icraRegexp  *)

module IcraPathExpr = struct
  open BatHashcons

  type var_t = int * int (* entry and exit verts of procedure *) 
  
  type ('a,'b) open_pathexpr = (* Untensored open path expressions *)
    [ `IDetensor of 'a * 'b
    | `IProject of 'a
    | `IVar of var_t              (* A (possibly indirectly) recursive procedure call *)
    | `IConstantEdge of int * int (* NOTE: Only use this for non-recursive edges!! *)
    | `IMul of 'a * 'a
    | `IAdd of 'a * 'a
    | `IStar of 'a
    | `IZero
    | `IOne ]
 
  type ('a,'b) open_pathexprT = (* Tensored open path expressions *)
    [ `ITensor of 'a * 'a
    | `IProjectT of 'b
    | `IMulT of 'b * 'b 
    | `IAddT of 'b * 'b
    | `IStarT of 'b
    | `IZeroT
    | `IOneT ]

  type ('a,'b) algebra = (('a,'b) open_pathexpr -> 'a) * (('a,'b) open_pathexprT -> 'b)
  
  type pe =                      (* Untensored path expressions *)
    | IDetensor of t * tT
    | IProject of t
    | IVar of var_t              (* A (possibly indirectly) recursive procedure call *)
    | IConstantEdge of int * int (* NOTE: Only use this for non-recursive edges!! *)
    | IMul of t * t
    | IAdd of t * t
    | IStar of t
    | IOne
    | IZero
  and t = pe hobj
  and peT =                      (* Tensored path expressions *)
    | ITensor of t * t
    | IProjectT of tT
    | IMulT of tT * tT
    | IAddT of tT * tT
    | IStarT of tT
    | IOneT
    | IZeroT
  and tT = peT hobj
  ;;

  module HC = BatHashcons.MakeTable(struct
    type t = pe
    let equal x y = match x, y with
      | IDetensor (u, t), IDetensor (u', t') -> u.tag = u'.tag && t.tag = t'.tag
      | IProject s, IProject s' -> s.tag = s'.tag
      | IVar (s,t), IVar(s',t') -> s = s' && t = t'
      | IConstantEdge (s, t), IConstantEdge (s', t') -> s = s' && t = t'
      | IMul (s, t), IMul (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | IAdd (s, t), IAdd (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | IStar s, IStar s' -> s.tag = s'.tag
      | IOne, IOne -> true
      | IZero, IZero -> true
      | _ -> false
    let hash = function
      | IDetensor (u, t) -> Hashtbl.hash (0, u.tag, t.tag)
      | IProject x -> Hashtbl.hash (1, x.tag)
      | IVar (s,t) -> Hashtbl.hash (2, s, t)
      | IConstantEdge (x, y) -> Hashtbl.hash (3, x, y)
      | IMul (x, y) -> Hashtbl.hash (4, x.tag, y.tag)
      | IAdd (x, y) -> Hashtbl.hash (5, x.tag, y.tag)
      | IStar x -> Hashtbl.hash (6, x.tag)
      | IOne -> Hashtbl.hash 7
      | IZero -> Hashtbl.hash 8
  end)

  module HCT = BatHashcons.MakeTable(struct
    type t = peT
    let equal x y = match x, y with
      | ITensor (s, t), ITensor (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | IProjectT s, IProjectT s' -> s.tag = s'.tag
      | IMulT (s, t), IMulT (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | IAddT (s, t), IAddT (s', t') -> s.tag = s'.tag && t.tag = t'.tag
      | IStarT s, IStarT s' -> s.tag = s'.tag
      | IOneT, IOneT -> true
      | IZeroT, IZeroT -> true
      | _ -> false
    let hash = function
      | ITensor (u, t) -> Hashtbl.hash (0, u.tag, t.tag)
      | IProjectT x -> Hashtbl.hash (1, x.tag)
      | IMulT (x, y) -> Hashtbl.hash (2, x.tag, y.tag)
      | IAddT (x, y) -> Hashtbl.hash (3, x.tag, y.tag)
      | IStarT x -> Hashtbl.hash (4, x.tag)
      | IOneT -> Hashtbl.hash 5
      | IZeroT -> Hashtbl.hash 6
  end)

  module HT = BatHashtbl.Make(struct
      type t = pe hobj
      let equal s t = s.tag = t.tag
      let hash t = t.hcode
    end)

  module HTT = BatHashtbl.Make(struct
      type t = peT hobj
      let equal s t = s.tag = t.tag
      let hash t = t.hcode
    end)

  type context = { uctx : HC.t; 
                   tctx : HCT.t; }

  type ('a,'b) table = { utbl : 'a HT.t; 
                         ttbl : 'b HTT.t; }

  let mk_one ctx = HC.hashcons ctx.uctx IOne
  let mk_zero ctx = HC.hashcons ctx.uctx IZero
  let mk_detensor ctx u t = match u.obj, t.obj with
    | IZero, _ -> mk_zero ctx
    | _, IZeroT -> mk_zero ctx
    | _, IOneT -> u
    | _, _ -> (HC.hashcons ctx.uctx (IDetensor (u,t)));;
  let mk_project ctx x = match x.obj with  
    | IZero -> mk_zero ctx
    | IOne -> mk_one ctx
    | _ -> HC.hashcons ctx.uctx (IProject x)
  let mk_mul ctx x y = match x.obj, y.obj with
    | IZero, _ -> mk_zero ctx
    | _, IZero -> mk_zero ctx
    | IOne, _ -> y
    | _, IOne -> x
    | _, _ -> HC.hashcons ctx.uctx (IMul (x, y))
  let mk_add ctx x y = match x.obj, y.obj with
    | IZero, _ -> y
    | _, IZero -> x
    | _, _ -> HC.hashcons ctx.uctx (IAdd (x, y))
  let mk_star ctx x = match x.obj with
    | IZero -> mk_one ctx
    | IOne -> mk_one ctx
    (* Could add (1+x)* rules here *)
    | _ -> HC.hashcons ctx.uctx (IStar x)
  let mk_constant_edge ctx src tgt = HC.hashcons ctx.uctx (IConstantEdge (src, tgt))
  let mk_var ctx src tgt = HC.hashcons ctx.uctx (IVar (src, tgt))

  let mk_oneT ctx = HCT.hashcons ctx.tctx IOneT
  let mk_zeroT ctx = HCT.hashcons ctx.tctx IZeroT
  let mk_tensor ctx x y = match x.obj, y.obj with
    | IZero, _ -> mk_zeroT ctx
    | _, IZero -> mk_zeroT ctx
    | IOne, IOne -> mk_oneT ctx
    | _, _ -> HCT.hashcons ctx.tctx (ITensor (x, y))
  let mk_projectT ctx x = match x.obj with  
    | IZeroT -> mk_zeroT ctx
    | IOneT -> mk_oneT ctx
    | _ -> HCT.hashcons ctx.tctx (IProjectT x)
  let rec mk_mulT ctx x y = match x.obj, y.obj with (* FIXME Make sure I don't make mul backwards somehow *)
    | IZeroT, _ -> mk_zeroT ctx
    | _, IZeroT -> mk_zeroT ctx
    | IOneT,  _ -> y
    | _, IOneT -> x
  (*| ITensor(w,x), ITensor(y,z) -> mk_tensor ctx (mk_mul ctx y w) (mk_mul ctx x z)
    | IMulT(d,ITensor(w,x)), ITensor(y,z) -> mk_mulT ctx d (mk_tensor ctx (mk_mul ctx y w) (mk_mul ctx x z))
    | ITensor(w,x), IMulT(ITensor(y,z),c) -> mk_mulT ctx (mk_tensor ctx (mk_mul ctx y w) (mk_mul ctx x z)) c *)
    | _, _ -> HCT.hashcons ctx.tctx (IMulT (x, y))
  let mk_addT ctx x y = match x.obj, y.obj with
    | IZeroT, _ -> y
    | _, IZeroT -> x
    | _, _ -> HCT.hashcons ctx.tctx (IAddT (x, y))
  let rec mk_starT ctx x = match x.obj with
    | IZeroT -> mk_oneT ctx
    | IOneT -> mk_oneT ctx
    (* Could add (1+x)* rules here *)
    | _ -> HCT.hashcons ctx.tctx (IStarT x)

  let rec pp formatter pathexpr =
    let open Format in
    match pathexpr.obj with
    | IDetensor (u, t) -> fprintf formatter "@[[[%a] |>< [%a]]@]" pp u ppT t
    | IVar (s, t) -> fprintf formatter "@[Var[%d,%d]@]" s t 
    | IProject x -> fprintf formatter "@[Proj[%a]@]" pp x
    | IConstantEdge (x, y) -> fprintf formatter "@[%d->%d@]" x y
    | IMul (x, y) -> fprintf formatter "@[(%a)@ . (%a)@]" pp x pp y
    | IAdd (x, y) -> fprintf formatter "@[%a@ + %a@]" pp x pp y
    | IStar x -> fprintf formatter "@[(%a)*@]" pp x
    | IZero -> fprintf formatter "0"
    | IOne -> fprintf formatter "1"
  and ppT formatter pathexpr =
    let open Format in
    match pathexpr.obj with
    | ITensor (x, y) -> fprintf formatter "@[[[%a] (.) [%a]]@]" pp x pp y
    | IProjectT x -> fprintf formatter "@[ProjT[%a]@]" ppT x
    | IMulT (x, y) -> fprintf formatter "@[(%a)@ .T (%a)@]" ppT x ppT y
    | IAddT (x, y) -> fprintf formatter "@[%a@ +T %a@]" ppT x ppT y
    | IStarT x -> fprintf formatter "@[(%a)*T @]" ppT x
    | IZeroT -> fprintf formatter "0T"
    | IOneT -> fprintf formatter "1T"
  
  let mk_table ?(size=991) () = { utbl = HT.create size; ttbl = HTT.create size }
  let mk_context ?(size=991) () = { uctx = HC.create size; tctx = HCT.create size }
 

  let evaluators table (ff : ('a,'b) algebra) =
    let (f,fT) = ff in 
    let rec go expr =
      if HT.mem table.utbl expr then
        HT.find table.utbl expr
      else
        let result =
          match expr.obj with
          | IDetensor (u,t) -> f (`IDetensor (go u, goT t))
          | IProject x -> f (`IProject (go x))
          | IVar v -> f (`IVar v)
          | IConstantEdge (s, t) -> f (`IConstantEdge (s, t)) 
          | IMul (x, y) -> f (`IMul (go x, go y))
          | IAdd (x, y) -> f (`IAdd (go x, go y))
          | IStar x -> f (`IStar (go x))
          | IOne -> f `IOne
          | IZero -> f `IZero
        in
        HT.add table.utbl expr result;
        result
    and goT expr =
      if HTT.mem table.ttbl expr then
        HTT.find table.ttbl expr
      else
        let result =
          match expr.obj with
          | ITensor (x,y) -> fT (`ITensor (go x, go y))
          | IProjectT x -> fT (`IProjectT (goT x))
          | IOneT -> fT `IOneT
          | IZeroT -> fT `IZeroT
          | IMulT (x, y) -> fT (`IMulT (goT x, goT y))
          | IAddT (x, y) -> fT (`IAddT (goT x, goT y))
          | IStarT x -> fT (`IStarT (goT x))
        in
        HTT.add table.ttbl expr result;
        result
    in (go, goT)

  let eval ?(table={utbl=HT.create 991;ttbl=HTT.create 991}) 
           (ff : ('a,'b) algebra) =
      let (go,_) = evaluators table ff in go

  let evalT ?(table={utbl=HT.create 991;ttbl=HTT.create 991}) 
           (ff : ('a,'b) algebra) =
      let (_,goT) = evaluators table ff in goT

  let forget table pce pv =
    let safe_pair = 
      ((function
        | `IDetensor (u,t) -> u && t
        | `IProject x -> x
        | `IVar v -> pv v 
        | `IConstantEdge (s, t) -> pce s t
        | `IMul (x, y) -> x && y
        | `IAdd (x, y) -> x && y
        | `IStar x -> x
        | `IZero -> true
        | `IOne -> true), 
       (function 
        | `ITensor (x,y) -> x && y
        | `IProjectT x -> x
        | `IMulT (x, y) -> x && y
        | `IAddT (x, y) -> x && y
        | `IStarT x -> x
        | `IZeroT -> true
        | `IOneT -> true))
    in
    HT.filteri_inplace (fun k _ -> (eval safe_pair) k) table.utbl;
    HTT.filteri_inplace (fun k _ -> (evalT safe_pair) k) table.ttbl


  (* Note: the factoring and substitution operations below bypass memoization *)
  let rec factorAux ctx x ehc =
    let e = ehc.obj in
    match e with
    | IOne -> ((mk_one ctx), (mk_zeroT ctx))
    | IVar v -> if (v = x) then ((mk_zero ctx), (mk_oneT ctx)) else (ehc, (mk_zeroT ctx))
    | IZero -> ((mk_zero ctx), (mk_zeroT ctx))
    | IConstantEdge (vs,vt) -> (ehc, (mk_zeroT ctx))
    | IProject child ->
      let u, t = (factorAux ctx x child) in
      (mk_project ctx u, mk_projectT ctx t)
    | IAdd (lChild, rChild) ->
      let lu,lt = (factorAux ctx x lChild) in
      let ru,rt = (factorAux ctx x rChild) in
              ((mk_add ctx lu ru), (mk_addT ctx lt rt))
    | IMul (lChild, rChild) ->
      let lu,lt = (factorAux ctx x lChild) in
      let ru,rt = (factorAux ctx x rChild) in
              ((mk_mul ctx lu ru)
               ,
               (mk_addT ctx  
                 (mk_mulT ctx lt (mk_tensor ctx (mk_one ctx) ru))
                 (mk_mulT ctx rt (mk_tensor ctx lChild (mk_one ctx)))))
    | IStar (child) -> (ehc, (mk_zeroT ctx))
    | IDetensor (uChild,tChild) ->
      let uu,ut = (factorAux ctx x uChild) in
          ((mk_detensor ctx uu tChild),
           (mk_mulT ctx ut tChild))
  
  (*  Given a variable x and a regular expression e, *)
  (*   produce a new expression ( u \detensorproduct t* ) *)
  let isolate ctx x e =
    let uhc, thc = factorAux ctx x e in
    mk_detensor ctx uhc (mk_starT ctx thc)
  
  (*  ---- general substitution functions ---- *)
  
  (*  Substitute s for x in e *)
  let rec subst ctx s x ehc =
    let e = ehc.obj in
    match e with
    | IDetensor (uChild,tChild) -> mk_detensor ctx (subst ctx s x uChild) (substT ctx s x tChild)
    | IProject (child) -> mk_project ctx (subst ctx s x child)
    | IVar v -> 
        let (xa,xb) = x in 
        let (va,vb) = v in 
        Printf.printf " Subst checking (%d,%d) against (%d,%d)\n" xa xb va vb;
        if (x = v) then s else ehc
    | IConstantEdge (vs,vt) -> ehc
    | IAdd (lChild, rChild) -> mk_add ctx (subst ctx s x lChild) (subst ctx s x rChild)
    | IMul (lChild, rChild) -> mk_mul ctx (subst ctx s x lChild) (subst ctx s x rChild)
    | IStar (child) -> mk_star ctx (subst ctx s x child)
    | IZero -> ehc
    | IOne -> ehc
  
  (*  Substitute s for the variable x in e, where x is interpreted as the number *)
  (*    of some untensored variable, so, we will not substitute for occurrences of *)
  (*    the tensored variable with numbre x. *)
  and substT ctx s x ehc =
    let e = ehc.obj in
    match e with
    | IProjectT (child) -> mk_projectT ctx (substT ctx s x child)
    | IAddT (lChild, rChild) -> mk_addT ctx (substT ctx s x lChild) (substT ctx s x rChild)
    | IMulT (lChild, rChild) -> mk_mulT ctx (substT ctx s x lChild) (substT ctx s x rChild)
    | IStarT (child) -> mk_starT ctx (substT ctx s x child)
    | ITensor (lChild,rChild) -> mk_tensor ctx (subst ctx s x lChild) (subst ctx s x rChild)
    | IZeroT -> ehc
    | IOneT -> ehc
  
end

(*    End stuff from old icraRegexp   *)
(* ---------------------------------- *)




(* ---------------------------------- *)
(* Begin stuff from old weightedGraph *)
(*             preamble               *)

module type Weight = WeightedGraph.Weight
(*module M = BatMap.Make(IntPair)*)
module M = WeightedGraph.M

module U = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)

type 'a weighted_graph = 'a WeightedGraph.weighted_graph



let project = K.exists Cra.V.is_global



(* .................................. *)
(*          proper contents           *)


module MakeBottomUpRecGraph (W : Weight) = struct
  open WeightedGraph

  (*include WeightedGraph.MakeRecGraph(W)*)
  module CallSet = BatSet.Make(IntPair)
  module VertexSet = SrkUtil.Int.Set

  module CallGraph = struct
    type t = CallSet.t M.t
    module V = IntPair
    let iter_vertex f callgraph =
      M.iter (fun k _ -> f k) callgraph
    let iter_succ f callgraph v =
      CallSet.iter f (M.find v callgraph)
    let add_vertex callgraph v =
      if M.mem v callgraph then
        callgraph
      else
        M.add v CallSet.empty callgraph
    let add_edge callgraph u v =
      let callgraph = add_vertex callgraph v in
      if M.mem u callgraph then
        M.add u (CallSet.add v (M.find u callgraph)) callgraph
      else
        M.add u (CallSet.singleton v) callgraph
    let empty = M.empty
  end

  let fold_reachable_edges f g v acc =
    let visited = ref VertexSet.empty in
    let rec go u acc =
      U.fold_succ (fun v acc ->
          let acc = f u v acc in
          if not (VertexSet.mem v !visited) then begin
            visited := VertexSet.add v (!visited);
            go v acc
          end else
            acc)
        g.graph
        u
        acc
    in
    go v acc

  type recgraph = (W.t label) weighted_graph

  type query =
    { summaries : W.t M.t; (* Map calls to weights that summarize all paths in
                              the call *)
      labels : (W.t label) M.t; (* Interpretation for all path expression edges *)
      graph : NPathexpr.t t; (* Path expression weighted graph *)
      table : W.t NPathexpr.table; (* Path expression memo table  *)
      context : NPathexpr.context (* Path expression context *) }


  type t = recgraph

  let label_algebra =
    let add x y = match x, y with
      | Weight x, Weight y -> Weight (W.add x y)
      | _, _ -> invalid_arg "No weight operations for call edges"
    in
    let mul x y = match x, y with
      | Weight x, Weight y -> Weight (W.mul x y)
      | _, _ -> invalid_arg "No weight operations for call edges"
    in
    let star = function
      | Weight x -> Weight (W.star x)
      | _ -> invalid_arg "No weight operations for call edges"
    in
    let zero = Weight W.zero in
    let one = Weight W.one in
    { add; mul; star; zero; one }

  let empty = empty label_algebra

  let weight_algebra f = function
    | `Edge (s, t) -> f s t
    | `Mul (x, y) -> W.mul x y
    | `Add (x, y) -> W.add x y
    | `Star x -> W.star x
    | `Zero -> W.zero
    | `One -> W.one

  let pathexp_algebra context =
    { mul = NPathexpr.mk_mul context;
      add = NPathexpr.mk_add context;
      star = NPathexpr.mk_star_simplify context;
      zero = NPathexpr.mk_zero context;
      one = NPathexpr.mk_one context }

  (* For each (s,t) call reachable from [src], add an edge from [src] to [s]
     with the path weight from [src] to to the call.  *)
  let add_call_edges query src =
    let weight_algebra =
      weight_algebra (fun s t ->
          match M.find (s, t) query.labels with
          | Weight w -> w
          | Call (en, ex) -> M.find (en, ex) query.summaries)
    in
    fold_reachable_edges
      (fun u v query' ->
         match M.find (u, v) query'.labels with
         | Call (call, _) ->
           let weight =
             path_weight query.graph src u
             |> NPathexpr.eval ~table:query.table weight_algebra
             |> W.project
           in
           if M.mem (src, call) query'.labels then
             match M.find (src, call) query'.labels with
             | Weight w ->
               let label = Weight (W.add w weight) in
               let labels' =
                 M.add (src, call) label query'.labels
               in
               { query' with labels = labels' }
             | _ -> assert false
           else
             let graph' =
               add_edge query'.graph src (NPathexpr.mk_edge query.context src call) call
             in
             let labels' = M.add (src, call) (Weight weight) query'.labels in
             { query' with graph = graph';
                           labels = labels' }
         | _ -> query')
      query.graph
      src
      query


  module CallGraphSCCs = Graph.Components.Make(CallGraph)

  type scc = 
    { (* path_graph : NPathexpr.t weighted_graph; *)
     procs : (int * int * NPathexpr.t) list }
  
  (* This non-linear version of mk_query must be called with a 
        summarizer function that knows how to summarize a
        strongly connected component of the call graph *)
  let mk_query ?(delay=1) rg summarizer =
    let table = NPathexpr.mk_table () in
    let context = NPathexpr.mk_context () in
    let calls = (* All calls that appear on a call edge *)
      fold_edges (fun (_, label, _) callset ->
          match label with
          | Weight _ -> callset
          | Call (en, ex) -> CallSet.add (en, ex) callset)
        rg
        CallSet.empty
    in
    let path_graph =
      { graph = rg.graph;
        labels = M.mapi (fun (u,v) _ -> NPathexpr.mk_edge context u v) rg.labels;
        algebra = pathexp_algebra context }
    in

    if CallSet.is_empty calls then
      { summaries = M.empty;
        table;
        graph = path_graph;
        context;
        labels = rg.labels }
    else begin
      (* call_pathexpr is a map from (s,t) pairs to the path expressions
          of all paths from s to t; in these path expressions, each edge,
          say from u to v, is represented as (mk_edge ctx (u,v))-- as 
          constructed in path_graph above-- that is, edges don't have
          weights (with type W.t) on them, and call edges aren't treated
          specially. *)
      let call_pathexpr =
        CallSet.fold (fun (src, tgt) pathexpr ->
            M.add (src, tgt) (path_weight path_graph src tgt) pathexpr)
          calls
          M.empty
      in
      (* Create a fresh call vertex to serve as entry.  It will have an edge
           to every other call *)
      let callgraph_entry =
        let (s, t) = CallSet.min_elt calls in
        (s-1, s-1)
      in
      let callgraph_sccs =
        (* pe_procs takes a node of a path expression and returns a CallSet.t
              which is the set of calls that are under that node; it is 
              intended to be given as a parameter to eval, which will walk
              over a path expression, calling pe_procs on each node *)
        let pe_procs = function
          | `Edge (s, t) ->
            begin match M.find (s, t) rg.labels with
              | Call (en, ex) -> CallSet.singleton (en, ex)
              | _ -> CallSet.empty
            end
          | `Mul (x, y) | `Add (x, y) -> CallSet.union x y
          | `Star x -> x
          | `Zero | `One -> CallSet.empty
        in
        let table = NPathexpr.mk_table () in
        (* Edges added by the following action may no longer be necessary: *)
        
        let initial_callgraph =
          CallSet.fold (fun call callgraph ->
              CallGraph.add_edge callgraph callgraph_entry call)
            calls
            CallGraph.empty
        in 
        (* If there is a call to (s,t) between s' and t', add a dependence
           edge from (s',t') to (s,t) *)
        let callgraph =
          M.fold (fun proc pathexpr callgraph ->
              CallSet.fold (fun target callgraph ->
                  CallGraph.add_edge callgraph target proc)
                (NPathexpr.eval ~table pe_procs pathexpr)
                callgraph)
            call_pathexpr
            (*CallGraph.empty*) initial_callgraph (* Use CallGraph.empty here? *)
        in      
        List.rev (CallGraphSCCs.scc_list callgraph) (* = callgraph_sccs *)
        in 
      (*Format.printf "Number of SCCs in call graph is %d.@." (List.length callgraph_sccs);*)
      let summaries = ref (M.map (fun _ -> W.zero) call_pathexpr) in
      let rec summarize_sccs scc_list =
        match scc_list with 
        | [] -> ()
        | callgraph_scc :: rest ->
          (*if is_within_scc callgraph_entry then *)
          if List.mem callgraph_entry callgraph_scc then  
            summarize_sccs rest else
          begin
            (* Idea: should we not give back SCCs that have no calls in them? *)
            (* Idea: should we really give a separate recgraph back for each SCC? *)
            (* let this_scc = 
              { path_graph = path_graph; procs = callgraph_scc } in *)
            let this_scc = 
              { procs = List.map 
                        (fun (u,v) -> (u,v,M.find (u,v) call_pathexpr)) 
                        callgraph_scc } in
            (* Call the client's summarizer to summarize the current SCC *)
            let new_summary_list = 
                (*summarizer this_scc path_weight_internal context (pathexp_algebra context)*)
                summarizer this_scc path_graph context !summaries
            in
            List.iter (fun (s, t, summary) -> 
                    summaries := M.add (s,t) summary !summaries) 
              new_summary_list;
            summarize_sccs rest
          end
      in
      summarize_sccs callgraph_sccs;
      let query =
        { summaries = !summaries;
          table;
          graph = path_graph;
          context;
          labels = rg.labels }
      in
      (* For each (s,t) call containing a call (s',t'), add an edge from s to s'
         with the path weight from s to call(s',t'). *)
      let final_query = (CallSet.fold
        (fun (src, tgt) query' -> add_call_edges query' src)
        calls
        query)
      in 
      final_query
    end

    let path_weight query src tgt =
      if M.mem (src, tgt) query.summaries then 
        M.find (src, tgt) query.summaries 
      else
      (* For each (s,t) call edge reachable from src, add corresponding edge
         from src to s with the path weight from src to s *)
      let query' = add_call_edges query src in
      let weight =
        weight_algebra (fun s t ->
            match M.find (s, t) query'.labels with
            | Weight w -> w
            | Call (en, ex) -> M.find (en, ex) query'.summaries)
      in
      path_weight query'.graph src tgt
      |> NPathexpr.eval weight
      (*|> eval ~table:query.table weight*)
  
end

(* -------------------------------- *)
(* End stuff from old weightedGraph *)


module BURG = MakeBottomUpRecGraph(struct
  include K
  let project = project
end)

let to_transition_formula tr =
  let (tr_symbols, post_def) =
    BatEnum.fold (fun (symbols, post_def) (var, term) ->
        let pre_sym = Var.symbol_of var in
        let post_sym = post_symbol pre_sym in
        let post_term = Srk.Syntax.mk_const srk post_sym in
        ((pre_sym,post_sym)::symbols,
          (Srk.Syntax.mk_eq srk post_term term)::post_def))
      ([], [])
      (K.transform tr)
  in
  let body =
    SrkSimplify.simplify_terms srk (Srk.Syntax.mk_and srk ((K.guard tr)::post_def))
  in
  (tr_symbols, body)

let to_transition_formula_with_unmodified tr all_vars =
  let tr_symbols, body = to_transition_formula tr in
  let tr_symbol_set = List.fold_left (fun s (pre_sym,post_sym) ->
      Srk.Syntax.Symbol.Set.add pre_sym s)
    Srk.Syntax.Symbol.Set.empty 
    tr_symbols
  in
  let all_symbols = VarSet.fold (fun v s -> 
      Srk.Syntax.Symbol.Set.add (Cra.V.symbol_of v) s)
    all_vars
    Srk.Syntax.Symbol.Set.empty 
  in
  let unmodified_symbols = 
    Srk.Syntax.Symbol.Set.diff all_symbols tr_symbol_set in
  let unmodified_inclusive_body = Srk.Syntax.mk_and srk
    (body::(List.map 
      (fun sym -> Srk.Syntax.mk_eq srk
        (Srk.Syntax.mk_const srk sym)
        (Srk.Syntax.mk_const srk (post_symbol sym)))
      (Srk.Syntax.Symbol.Set.elements unmodified_symbols))) in
  let inclusive_symbols = 
    Srk.Syntax.Symbol.Set.fold 
      (fun sym symlist -> (sym, (post_symbol sym))::symlist)
      unmodified_symbols 
      tr_symbols in
  (inclusive_symbols, unmodified_inclusive_body)

let of_transition_formula tr_symbols fmla = 
    let transform =
      List.fold_left (fun tr (pre, post) ->
          match Var.of_symbol pre with
          | Some v -> (v, Srk.Syntax.mk_const srk post)::tr
          | None -> assert false)
        []
        tr_symbols
    in
    K.construct fmla transform

let debug_print_depth_wedge tr = 
  (* NOTE: now applying project *)
  let (tr_symbols, body) = to_transition_formula (project tr) in
  let projection x = 
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
    || 
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false (* false *)
  in 
  logf ~level:`always "  %t" 
    (fun f -> Wedge.pp f (Wedge.abstract ~exists:projection srk body))

let debug_print_wedge_of_transition ?(levelParam=None) tr = 
  let level = match levelParam with 
              | None -> if !chora_print_wedges then `always else `info 
              | Some lev -> lev
    in
  let (tr_symbols, body) = to_transition_formula tr in
  let projection x = 
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
    || 
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false (* false *)
  in 
  logf ~level:level "  %t@." 
    (fun f -> Wedge.pp f (Wedge.abstract ~exists:projection srk body))

let assign_value_to_literal value literal = 
  K.assign value (Srk.Syntax.mk_real srk (Srk.QQ.of_int literal))

(*let assume_value_eq_literal value literal = 
  let var = Cra.V.symbol_of value in 
  K.assume (Srk.Syntax.mk_eq srk 
    (Srk.Syntax.mk_const srk var)
    (Srk.Syntax.mk_real srk (Srk.QQ.of_int literal)))*)

let assume_literal_leq_value literal value = 
  let var = Cra.V.symbol_of value in 
  K.assume (Srk.Syntax.mk_leq srk 
    (Srk.Syntax.mk_real srk (Srk.QQ.of_int literal))
    (Srk.Syntax.mk_const srk var))

let increment_variable value = 
  K.assign
    value 
    (Srk.Syntax.mk_add 
      srk
      [(Srk.Syntax.mk_const srk (Cra.V.symbol_of value));
       (Srk.Syntax.mk_real srk (Srk.QQ.of_int 1))])

(* ZZZ *)

let top_down_formula_to_wedge top_down_formula sym = 
  let projection x =
    x = sym ||
    match Cra.V.of_symbol x with
    | Some v -> Core.Var.is_global (Cra.var_of_value v)
    | None -> false
  in
  let wedge = Wedge.abstract ~exists:projection srk top_down_formula in
  let level = if !chora_debug_squeeze then `always else `info in
  logf ~level " incorporating squeezed depth formula: %t" 
    (fun f -> Wedge.pp f wedge);
  Wedge.to_formula wedge
  (*let wedge_as_formula = Wedge.to_formula wedge in 
  Srk.Syntax.mk_and srk [top_down_formula; wedge_as_formula]*)

let top_down_formula_to_symbolic_bounds phi sym = 
  let level = if !chora_debug_squeeze then `always else `info in
  logf ~level " squeezing depth-bound formula to symbolic bounds formula...";
  let exists x =
    x = sym ||
    match Cra.V.of_symbol x with
    | Some v -> Core.Var.is_global (Cra.var_of_value v)
    | None -> false
    (*true*)
  in
  let symbol_term = Syntax.mk_const srk sym in
  let debug_list part = 
     logf ~level "      -- inner bound list [";
     List.iter (fun elt -> logf ~level "       %a" (Syntax.Term.pp srk) elt) part;
     logf ~level "      -- inner bound list ]"
  in
  let debug_list_list parts = 
     logf ~level "   -- outer bound list [";
     List.iter (fun part -> debug_list part) parts;
     logf ~level "   -- outer bound list ]"
  in
  let safer_disjoin parts = 
    match parts with 
    | [] -> Syntax.mk_true srk
    | _ -> Syntax.mk_or srk parts
  in
  let to_formula parts = 
    let (lower,upper) = parts in
    (*| None -> Syntax.mk_false srk
      | Some (lower, upper) ->*)
    logf ~level " lower bounds: ";
    debug_list_list lower;
    logf ~level " upper bounds: ";
    debug_list_list upper;
    let lower_bounds =
      lower
      |> List.map (fun case ->
          case |> List.map (fun lower_bound -> Syntax.mk_leq srk lower_bound symbol_term)
          |> Syntax.mk_and srk)
      |> safer_disjoin
    in
    let upper_bounds =
      upper
      |> List.map (fun case ->
          case |> List.map (fun upper_bound -> Syntax.mk_leq srk symbol_term upper_bound)
          |> Syntax.mk_and srk)
      |> safer_disjoin
    in
    Syntax.mk_and srk [lower_bounds; upper_bounds]
  in
  logf ~level " sbf-squeeze input: %a " (Syntax.Formula.pp srk) phi;
  let formula_parts_wrapped = 
      Wedge.symbolic_bounds_formula_list ~exists srk phi sym in
  match formula_parts_wrapped with
  | `Sat (formula_parts) -> 
      let formula = to_formula formula_parts in 
      logf ~level " sbf-squeeze output: %a " (Syntax.Formula.pp srk) formula;
      formula
  | `Unsat ->
      logf ~level:`always " WARNING: sbf-squeeze got unsatisfiable depth formula!";
      Syntax.mk_true srk

  (* OLD CODE *)
  (*
  match Wedge.symbolic_bounds_formula ~exists srk phi sym with
  | `Sat (lower, upper) ->
    let lower_bound_formula = 
      begin match lower with
        | Some lower ->
          logf ~level " squeeze: %a <= height" (Syntax.pp_expr_unnumbered srk) lower;
          Syntax.mk_leq srk lower (Syntax.mk_const srk sym)
        | None -> 
          logf ~level " squeeze: no lower bound on height";
          Syntax.mk_true srk
      end
    in
    let upper_bound_formula =
      begin match upper with
        | Some upper ->
          logf ~level " squeeze: height <= %a" (Syntax.pp_expr_unnumbered srk) upper;
          Syntax.mk_leq srk (Syntax.mk_const srk sym) upper
        | None ->
          logf ~level " squeeze: no upper bound on height";
          Syntax.mk_true srk
      end
    in
    Syntax.mk_and srk [lower_bound_formula; upper_bound_formula]
  | `Unsat ->
    logf ~level:`always " squeeze: phi_td is infeasible";
    Syntax.mk_true srk
  *)
 
let make_top_down_weight_multi procs (ts : K.t Cra.label Cra.WG.t) 
      is_scc_call lower_summaries base_case_map height 
      scc_local_footprint scc_global_footprint scc_footprint
      (* for debugging:  program_vars *) =
  (* Note: this height variable really represents depth *)
  let set_height_zero = assign_value_to_literal height.value 0 in 
  let increment_height = increment_variable height.value in 
  let assume_height_non_negative = assume_literal_leq_value 0 height.value in
  let top_graph = ref BURG.empty in
  let dummy_exit_node = ref 0 in (* A dummy exit node representing having finished a base case *)
  let havoc_locals = K.havoc (VarSet.to_list scc_local_footprint) in 
  let havoc_loc_and_inc = K.mul havoc_locals increment_height in 
  let top = K.havoc (VarSet.to_list scc_footprint) in 
  let havoc_globals = project top in 
  List.iter (fun (p_entry,p_exit,pathexpr) ->
      let add_edges_alg = function
        | `Edge (s, t) ->
          dummy_exit_node := min !dummy_exit_node (min s t);
          begin match WeightedGraph.edge_weight ts s t with
            | Call (en, ex) -> 
              if not (is_scc_call s t) then 
                (* A call to a procedure that's in a lower SCC *)
                let low = M.find (en,ex) lower_summaries in
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight low) t
              else begin
                (* A call from this SCC back into this SCC *)
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight havoc_loc_and_inc) en;
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight havoc_globals) t
              end
            | Weight w -> (* Regular (non-call) edge *)
              top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight w) t
          end
        | _ -> () (* Add, Mul, Star, etc. *) in
      NPathexpr.eval add_edges_alg pathexpr) procs;
  dummy_exit_node := !dummy_exit_node - 1; (* Minimum vertex number minus one *)
  List.iter (fun (p_entry,p_exit,_) ->
      (* Note: this use of top is a hack; this top isn't really top; it's really
           havoc-all-program-vars.  For one thing, it doesn't havoc the height variable H,
           which is good, because that's the main thing we want to get out of this analysis. *)
      let base_case_weight = ProcMap.find (p_entry,p_exit) base_case_map in 
      let weight = K.mul base_case_weight top in
      top_graph := Srk.WeightedGraph.add_edge !top_graph p_entry (Weight weight) !dummy_exit_node)
    procs;
  let td_formula_map = (List.fold_left (fun td_formula_map (p_entry,p_exit,pathexpr) ->
      match WeightedGraph.path_weight !top_graph p_entry !dummy_exit_node with
      | Weight cycles ->
        let td_summary = K.mul set_height_zero cycles in
        let td_summary = K.mul td_summary assume_height_non_negative in
        let td_summary = project td_summary in (* FIXME Not sure this is needed *)
        logf ~level:`info "  multi_phi_td%s = [" (proc_name_triple_string (p_entry,p_exit));
        print_indented 15 td_summary; logf ~level:`info "  ]\n";
        (*(if !chora_print_depth_bound_wedges then
        begin
          logf ~level:`always "  wedge[phi_td%t] is [" (proc_name_triple_string (p_entry,p_exit));
          debug_print_depth_wedge td_summary;
          logf ~level:`always "  ]";
        end);*)
        let _, top_down_formula = to_transition_formula td_summary in
        logf ~level:`info "@.  tdf%s: %a" (proc_name_triple_string (p_entry,p_exit))
            (Srk.Syntax.Formula.pp srk) top_down_formula;
        let post_height_sym = post_symbol height.symbol in
        let post_height_gt_zero = Syntax.mk_lt srk 
          (Syntax.mk_zero srk)
          (Syntax.mk_const srk post_height_sym) in
        let post_height_eq_zero = Syntax.mk_eq srk 
          (Syntax.mk_zero srk)
          (Syntax.mk_const srk post_height_sym) in
        let base_case_weight = ProcMap.find (p_entry,p_exit) base_case_map in 
        (*let _, base_case_formula = to_transition_formula base_case_weight in*)
        let _, base_case_formula = 
          to_transition_formula_with_unmodified base_case_weight scc_global_footprint in 
        (*let to_be_squeezed = top_down_formula in (* naive version *) *)
        let to_be_squeezed = 
          (* sophisticated version: assume H' >= 0 inside squeezed version *) 
          Syntax.mk_and srk [post_height_gt_zero; top_down_formula] in
        let symbolic_bounds_top_down_formula = 
          if !chora_squeeze_sb || !chora_debug_squeeze
          then top_down_formula_to_symbolic_bounds to_be_squeezed post_height_sym
          else Syntax.mk_true srk in
        let wedge_top_down_formula = 
          if !chora_squeeze_wedge || !chora_debug_squeeze
          then top_down_formula_to_wedge to_be_squeezed post_height_sym
          else Syntax.mk_true srk in
        (*let incorporate_tdf fmla = 
          Syntax.mk_and srk [fmla; top_down_formula] in*)
        let incorporate_tdf fmla = 
            begin
              let case_split = 
                  Syntax.mk_or srk 
                    [(Syntax.mk_and srk [post_height_eq_zero; base_case_formula]);
                     (Syntax.mk_and srk [post_height_gt_zero; fmla])] in
              if !chora_squeeze_conjoin
              then Syntax.mk_and srk [top_down_formula; case_split]
              else case_split
            end
          in
        let final_top_down_formula = 
          if !chora_squeeze_sb
          then (if !chora_squeeze_wedge 
                then
                  failwith "ERROR: don't use -chora-squeeze and -chora-squeeze-sb simultaneously"
                else
                  incorporate_tdf symbolic_bounds_top_down_formula)
          else (if !chora_squeeze_wedge 
                then incorporate_tdf wedge_top_down_formula
                else top_down_formula) in 
        ProcMap.add (p_entry,p_exit) final_top_down_formula td_formula_map
      | _ -> failwith "A call was found in td_summary")
    ProcMap.empty procs) in
  td_formula_map;;

(*
let make_top_down_weight_oneproc p_entry path_weight_internal top scc_call_edges = 
  let height_var_sym_pair = make_aux_variable "H" in
  (*let height_var = Core.Var.mk (Core.Varinfo.mk_global "H" (Core.Concrete (Core.Int 32))) in 
  let height_var_val = Cra.VVal height_var in 
  let height_var_sym = Cra.V.symbol_of height_var_val in *)
  let set_height_zero = assign_value_to_literal height_var_sym_pair.value 0 in 
  let increment_height = increment_variable height_var_sym_pair.value in 
  let weight_of_call_top cs ct cen cex = project top in 
  logf ~level:`info "  fragments = [";
  let sum_of_fragments = IntPairSet.fold (fun (s,t) running_total -> 
    let fragment_weight = path_weight_internal p_entry s weight_of_call_top in
    (* (logf ~level:`info "  << %t >> \n" (fun f -> NPathexpr.pp f fragment_weight)) *)
    (* Format.fprintf Format.std_formatter "<<( %a )>> \n" K.pp fragment_weight *)
    print_indented 15 fragment_weight;
    logf ~level:`info "";
    K.add running_total fragment_weight
    ) scc_call_edges K.zero in
  logf ~level:`info "  ]";
  let top_down_summary = K.mul set_height_zero (K.star (K.mul increment_height sum_of_fragments)) in
  logf ~level:`info "  phi_td = [";
  print_indented 15 top_down_summary;
  logf ~level:`info "  ]\n";
  let top_down_symbols, top_down_formula = to_transition_formula top_down_summary in  
  logf ~level:`info "@.  tdf: %a"
      (Srk.Syntax.Formula.pp srk) top_down_formula;
  let is_post_height (pre_sym,post_sym) = (pre_sym == height_var_sym_pair.symbol) in 
  let post_height_sym = snd (List.find is_post_height top_down_symbols) in
  top_down_formula, post_height_sym;;
*)

let get_procedure_summary query rg procedure = 
  let entry = (RG.block_entry rg procedure).did in
  let exit = (RG.block_exit rg procedure).did in
  BURG.path_weight query entry exit

let print_procedure_summary procedure summary = 
  let level = if !chora_print_summaries then `always else `info in
  logf ~level:level "---------------------------------";
  logf ~level:level " -- Procedure summary for %a = " Varinfo.pp procedure;
  print_indented ~level:level 0 summary;
  logf ~level:level "";
  if !chora_print_wedges then 
    (let level = if !chora_print_wedges then `always else `info in
     logf ~level:level " -- Procedure summary wedge for %a = @." Varinfo.pp procedure;
     debug_print_wedge_of_transition summary)
  else ()

let resource_bound_analysis rg query =
  let cost_opt =
    let open CfgIr in
    let file = get_gfile () in
    let is_cost v = (Varinfo.show v) = "__cost" in
    try
      Some (Cra.VVal (Core.Var.mk (List.find is_cost file.vars)))
    with Not_found -> None
  in
  match cost_opt with 
  | None -> 
    (logf ~level:`info "Could not find __cost variable";
    if !chora_print_summaries || !chora_print_wedges then
        RG.blocks rg |> BatEnum.iter (fun procedure ->
        let summary = get_procedure_summary query rg procedure in 
        print_procedure_summary procedure summary))
  | Some cost ->
    begin
      let cost_symbol = Cra.V.symbol_of cost in
      let exists x =
        match Cra.V.of_symbol x with
        | Some v -> Core.Var.is_global (Cra.var_of_value v)
        | None -> false
      in
      Format.printf "===== Resource-Usage Bounds =====\n";
      RG.blocks rg |> BatEnum.iter (fun procedure ->
          let summary = get_procedure_summary query rg procedure in
          print_procedure_summary procedure summary;
          Format.printf "---- Bounds on the cost of %a@." Varinfo.pp procedure;
          if K.mem_transform cost summary then begin
            (*logf ~level:`always "Procedure: %a" Varinfo.pp procedure;*)
            (* Option 1, original version *)
            (* replace cost with 0, add constraint cost = rhs *)
            let guard =
              let subst x =
                if x = cost_symbol then
                  Ctx.mk_real QQ.zero
                else
                  Ctx.mk_const x
              in
              let rhs =
                Syntax.substitute_const srk subst (K.get_transform cost summary)
              in
              Ctx.mk_and [Syntax.substitute_const srk subst (K.guard summary);
                          Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
            in
            (* Option 2 *)
            (* Same as above, but now avoid setting pre-state cost to zero *)
            (*let guard =
              let rhs = K.get_transform cost summary
              in
              Ctx.mk_and [K.guard summary; Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
            in*)
            (* Option 3, the version from ICRA's code *)
            (*let guard =
              let rhs =
                if K.mem_transform cost summary then
                  K.get_transform cost summary
                else
                  Ctx.mk_const (Cra.V.symbol_of cost)
              in
              Ctx.mk_and [K.guard summary;
                          Ctx.mk_eq (Ctx.mk_const cost_symbol) rhs ]
            in*)
            let func = (* added by Jason *)
              let vertex = (RG.block_entry rg procedure).did in 
              let name_varinfo = 
                (Interproc.RG.vertices rg)
                |> BatEnum.find (fun (block, v) -> vertex = v.did)
                |> fst in
              let open CfgIr in let file = get_gfile() in
              List.find (fun f -> f.fname = name_varinfo) file.funcs;
            in
            let param_map =
              BatList.fold_lefti (fun map i formal ->
                  let param = PointerAnalysis.get_param i in
                  let pval = Cra.V.symbol_of (VVal param) in
                  let pwidth = Cra.V.symbol_of (VWidth param) in
                  let ppos = Cra.V.symbol_of (VWidth param) in
                  let fval = Ctx.mk_const (Cra.V.symbol_of (VVal (Core.Var.mk formal))) in
                  let fwidth = Ctx.mk_const (Cra.V.symbol_of (VWidth (Core.Var.mk formal))) in
                  let fpos = Ctx.mk_const (Cra.V.symbol_of (VPos (Core.Var.mk formal))) in
                  map
                  |> Srk.Syntax.Symbol.Map.add pval fval
                  |> Srk.Syntax.Symbol.Map.add pwidth fwidth
                  |> Srk.Syntax.Symbol.Map.add ppos fpos)
                Srk.Syntax.Symbol.Map.empty
                func.CfgIr.formals
            in
            let pre_cost_zero =
              let cost_symbol = Cra.V.symbol_of cost in
              Syntax.substitute_const srk (fun sym ->
                  if sym = cost_symbol then
                    Ctx.mk_real QQ.zero
                  else
                    Ctx.mk_const sym)
            in
            match Wedge.symbolic_bounds_formula ~exists srk guard cost_symbol with
            | `Sat (lower, upper) ->
              begin match lower with
                | Some lower ->
                  let lower = Syntax.substitute_map srk param_map lower in
                  logf ~level:`always " %a <= cost" (Syntax.pp_expr_unnumbered srk) lower;
                  logf ~level:`always " %a is o(%a)"
                    Varinfo.pp procedure
                    BigO.pp (BigO.of_term srk (pre_cost_zero lower))
                | None -> ()
              end;
              begin match upper with
                | Some upper ->
                  let upper = Syntax.substitute_map srk param_map upper in
                  logf ~level:`always " cost <= %a" (Syntax.pp_expr_unnumbered srk) upper;
                  logf ~level:`always " %a is O(%a)"
                  Varinfo.pp procedure
                  BigO.pp (BigO.of_term srk (pre_cost_zero upper))
                | None -> ()
              end
            | `Unsat ->
              logf ~level:`always "%a is infeasible"
                Varinfo.pp procedure
          end else
          logf ~level:`always "Procedure %a has zero cost" Varinfo.pp procedure;
          (*Format.printf "---------------------------------\n"*) )
    end

let check_assertions rg query main assertions = 
    if Srk.SrkUtil.Int.Map.cardinal assertions > 0 then
    logf ~level:`always "======= Assertion Checking ======";
    let entry_main = (RG.block_entry rg main).did in
    assertions |> SrkUtil.Int.Map.iter (fun v (phi, loc, msg) ->
        let path = BURG.path_weight query entry_main v in
        let sigma sym =
          match Cra.V.of_symbol sym with
          | Some v when K.mem_transform v path ->
            K.get_transform v path
          | _ -> Ctx.mk_const sym
        in
        let phi = Syntax.substitute_const Ctx.context sigma phi in
        let path_condition =
          Ctx.mk_and [K.guard path; Ctx.mk_not phi]
          |> SrkSimplify.simplify_terms srk
        in
        logf ~level:`trace "Path condition:@\n%a"
          (Syntax.pp_smtlib2 Ctx.context) path_condition;
        Cra.dump_goal loc path_condition;
        match Wedge.is_sat Ctx.context path_condition with
        | `Sat -> 
          Report.log_error loc msg;
          Format.printf "Assertion on line %d FAILED: \"%s\"\n" loc.Cil.line msg
        | `Unsat -> 
          Report.log_safe ();
          Format.printf "Assertion on line %d PASSED: \"%s\"\n" loc.Cil.line msg
        | `Unknown ->
          logf ~level:`warn "Z3 inconclusive";
          Report.log_error loc msg;
          Format.printf "Assertion on line %d FAILED/INCONCLUSIVE: \"%s\"\n" loc.Cil.line msg
          );
    Format.printf "=================================\n"

let scc_mem (scc:BURG.scc) en ex = 
  List.fold_left (fun found (p_entry,p_exit,pathexpr) -> 
    found || (p_entry == en && p_exit = ex)) false scc.procs;;

type edge_content = RecursiveCall of int * int 
                    | NonRecursiveCall of K.t
                    | WeightedEdge of K.t

let find_recursive_calls (ts : K.t Cra.label Cra.WG.t) pathexpr (scc:BURG.scc) = 
  let pe_call_edge_set = function
    | `Edge (s, t) ->
      begin match WeightedGraph.edge_weight ts s t with
        | Call (en, ex) -> 
          if scc_mem scc en ex 
          then IntPairSet.singleton (s,t)
          else IntPairSet.empty
        | _ -> IntPairSet.empty
      end
    | `Mul (x, y) | `Add (x, y) -> IntPairSet.union x y
    | `Star x -> x
    | `Zero | `One -> IntPairSet.empty
  in
  let scc_call_edges = NPathexpr.eval pe_call_edge_set pathexpr in 
  logf ~level:`info "  calls = [ ";
  IntPairSet.iter (fun (s,t) -> logf ~level:`info "(%d,%d) " s t) scc_call_edges;
  logf ~level:`info "]\n";
  scc_call_edges

(** Given a path expression and a function which tests whether an edge (u,v)
 *    is a call back into the current SCC, return a pair (r,n) of path
 *    expressions describing the recursive paths (r) which always call 
 *    back into the current SCC) and non-recursive paths n which never do.
 * *)
let factor_pair pathexpr is_scc_call edge (alg:NPathexpr.t WeightedGraph.algebra) =
  let factor_alg = function
    | `Edge (s, t) -> if is_scc_call s t 
                      then (edge s t, alg.zero)
                      else (alg.zero, edge s t)
    | `Add ((r1,n1), (r2,n2)) -> 
       (alg.add r1 r2, alg.add n1 n2)
    | `Mul ((r1,n1), (r2,n2)) -> 
       (alg.add 
          (alg.add 
            (alg.mul r1 r2) (* ...    *)
            (alg.mul r1 n2))(*  rec   *)
          (alg.mul n1 r2),  (* ...    *)
        alg.mul n1 n2)      (* nonrec *)
    | `Star (r,n) -> (*  Rec looks like (r+n)*r(r+n)* and non-rec is n* *)
       let mixed = alg.star (alg.add r n) in
       let nstar = alg.star n in
       (alg.mul (alg.mul nstar r) mixed,
        nstar)
    | `Zero -> (alg.zero, alg.zero)
    | `One -> (alg.zero, alg.one)
  in
  NPathexpr.eval factor_alg pathexpr

exception HasNonlinearRecursion
let check_linearity pathexpr is_scc_call =
  try 
    let factor_alg = function
      | `Edge (s, t) -> (is_scc_call s t)
      | `Add (b1, b2) -> b1 || b2
      | `Mul (b1, b2) -> if (b1 && b2) 
                         then raise HasNonlinearRecursion
                         else (b1 || b2)
      | `Star b -> if b then raise HasNonlinearRecursion else b
      | `Zero -> false
      | `One -> false
    in
    (let _ = NPathexpr.eval factor_alg pathexpr in 
    true)
  with HasNonlinearRecursion -> false

let is_constant_ipathexpr ipathexpr = 
  let is_constant = 
    ((function
      | `IDetensor (u,t) -> u && t
      | `IProject x -> x
      | `IVar v -> false
      | `IConstantEdge (s, t) -> true
      | `IMul (x, y) -> x && y
      | `IAdd (x, y) -> x && y
      | `IStar x -> x
      | `IZero -> true
      | `IOne -> true), 
     (function 
      | `ITensor (x,y) -> x && y
      | `IProjectT x -> x
      | `IMulT (x, y) -> x && y
      | `IAddT (x, y) -> x && y
      | `IStarT x -> x
      | `IZeroT -> true
      | `IOneT -> true))
  in
  IcraPathExpr.eval is_constant ipathexpr

let detensor_product uchild tchild = 
  let one_tensor_uchild = NewtonDomain.tensor K.one uchild in
  let dotted = KK.mul one_tensor_uchild tchild in
  NewtonDomain.detensor_transpose dotted

let handle_linear_recursion (scc : BURG.scc) classify_edge = 
  let original_equation_system = 
      List.fold_left (fun eqs (p_entry, p_exit, pathexpr) ->
        IntPairMap.add (p_entry,p_exit) pathexpr eqs)
    IntPairMap.empty
    scc.procs 
    in
  let ctx = IcraPathExpr.mk_context () in
  let convert_pathexpr_alg = function
      | `Edge (s, t) -> (match classify_edge s t with
                         | RecursiveCall (en,ex) ->
                           IcraPathExpr.mk_project ctx
                               (IcraPathExpr.mk_var ctx en ex)
                         | NonRecursiveCall _
                         | WeightedEdge _ -> 
                           IcraPathExpr.mk_constant_edge ctx s t)
      | `Add (b1, b2) -> IcraPathExpr.mk_add ctx b1 b2
      | `Mul (b1, b2) -> IcraPathExpr.mk_mul ctx b1 b2
      | `Star b -> IcraPathExpr.mk_star ctx b
      | `Zero -> IcraPathExpr.mk_zero ctx
      | `One -> IcraPathExpr.mk_one ctx
    in
  let icrapathexpr_equation_system = 
      IntPairMap.mapi (fun (p_entry, p_exit) pathexpr -> 
        NPathexpr.eval convert_pathexpr_alg pathexpr) 
        original_equation_system in
  logf ~level:`info " Beginning Gauss-Jordan elimination."; 
  logf ~level:`info " Original equation system: @."; 
    IntPairMap.iter (fun (p_entry'',p_exit'') ipathexpr -> 
       logf ~level:`info " (%d,%d) := %a @." 
      p_entry'' p_exit'' IcraPathExpr.pp (ipathexpr))
    icrapathexpr_equation_system;
  let transformed_ipathexpr_equation_system = 
      IntPairMap.fold (fun (p_entry, p_exit) _ eqs -> 
        let old_rhs = IcraPathExpr.mk_project ctx (* project is needed *)
          (IntPairMap.find (p_entry, p_exit) eqs) in
        logf ~level:`info " Acting on (%d,%d): @." p_entry p_exit; 
        let var = (p_entry,p_exit) in
        (* First, call Factor_{var} and then produce rhs' = U |>< (T)* *)
        let rhs' = IcraPathExpr.isolate ctx var old_rhs in
        let substituted_eqs = 
          IntPairMap.mapi 
            (fun (p_entry', p_exit') ipathexpr' ->
              if (p_entry', p_exit') = (p_entry,p_exit) 
              then rhs' (* var = rhs' *)
              else IcraPathExpr.subst ctx rhs' var ipathexpr')
            eqs
          in
          logf ~level:`info " After one substitution pass: @."; 
            IntPairMap.iter (fun (p_entry'',p_exit'') ipathexpr -> 
                logf ~level:`info " (%d,%d) := %a @." 
                p_entry'' p_exit'' IcraPathExpr.pp (ipathexpr))
              substituted_eqs;
          substituted_eqs)
        icrapathexpr_equation_system 
        icrapathexpr_equation_system in
  logf ~level:`info " Transformed equation system: @."; 
    IntPairMap.iter (fun (p_entry'',p_exit'') ipathexpr -> 
      logf ~level:`info " (%d,%d) := %a @." 
      p_entry'' p_exit'' IcraPathExpr.pp (ipathexpr))
    transformed_ipathexpr_equation_system;
  let () = IntPairMap.iter (fun (p_entry, p_exit) ipathexpr -> 
             assert (is_constant_ipathexpr ipathexpr))
             transformed_ipathexpr_equation_system in
  let tr_alg = 
    ((function
      | `IDetensor (u,t) -> detensor_product u t
      | `IProject x -> K.project x
      | `IVar v -> failwith "Variables should have been eliminated already!"
      | `IConstantEdge (s, t) -> (match classify_edge s t with
         | RecursiveCall (en,ex) -> failwith "Un-eliminated recursive call"
         | WeightedEdge w 
         | NonRecursiveCall w -> w)
      | `IMul (x, y) -> K.mul x y
      | `IAdd (x, y) -> K.add x y
      | `IStar x -> K.star x
      | `IZero -> K.zero
      | `IOne -> K.one), 
     (function 
      | `ITensor (x,y) -> NewtonDomain.tensor (K.transpose x) y
      | `IProjectT x -> KK.project x
      | `IMulT (x, y) -> KK.mul x y
      | `IAddT (x, y) -> KK.add x y
      | `IStarT x -> KK.star x
      | `IZeroT -> KK.zero
      | `IOneT -> KK.one)) in
  let table = IcraPathExpr.mk_table () in
  let assignment = 
    IntPairMap.mapi (fun (p_entry, p_exit) ipathexpr -> 
      let full_summary = IcraPathExpr.eval ~table tr_alg ipathexpr in
      K.project full_summary)
      transformed_ipathexpr_equation_system in
  let summaries = 
    IntPairMap.fold (fun (p_entry, p_exit) summary s ->
      (p_entry, p_exit, summary)::s)
      assignment
      [] in
  logf ~level:`info " Summaries of linearly recursive procedures: @."; 
    IntPairMap.iter (fun (p_entry'',p_exit'') summary -> 
        logf ~level:`info " (%d,%d) := @." p_entry'' p_exit'';
        print_indented ~level:`info 3 summary)
    assignment;
  summaries


let postprocess_summaries summary_list =
  if !chora_use_wedgecover then 
    let postprocess_summary parts = 
      let (p_entry, p_exit, summary) = parts in
      let tr_symbols, body = to_transition_formula summary in
      let projection x = 
        (List.fold_left 
          (fun found (vpre,vpost) -> found || vpre == x || vpost == x) 
            false tr_symbols)
      in 
      let psi = Wedge.cover srk projection body in 
      let new_summary = of_transition_formula tr_symbols psi in
      (p_entry, p_exit, new_summary)
    in
    List.map postprocess_summary summary_list
  else 
    summary_list

let build_summarizer (ts : K.t Cra.label Cra.WG.t) =  
  let program_vars = 
    let open CfgIr in let file = get_gfile() in
    let never_addressed_functions = 
      List.filter (fun f -> not (Varinfo.addr_taken f.fname)) file.funcs in 
    let vars = List.filter (fun vi -> 
      (* (not (Varinfo.is_global vi)) || *)
      let vname = Varinfo.show vi in 
      not (List.fold_left (fun found f -> (found || ((Varinfo.show f.fname) = vname)))
        false 
        never_addressed_functions
      )) file.vars in 
    List.map (fun vi -> Cra.VVal (Core.Var.mk vi)) vars in
  let local_program_vars = 
    let open CfgIr in let file = get_gfile() in
    let never_addressed_functions = 
      List.filter (fun f -> not (Varinfo.addr_taken f.fname)) file.funcs in 
    let vars = List.filter (fun vi -> 
      (not (Varinfo.is_global vi)) 
      || 
      let vname = Varinfo.show vi in 
      not (List.fold_left (fun found f -> (found || ((Varinfo.show f.fname) = vname)))
        false 
        never_addressed_functions
      )) file.vars in 
    List.map (fun vi -> Cra.VVal (Core.Var.mk vi)) vars in
  let havoc_locals = K.havoc local_program_vars in
  let top = K.havoc program_vars in

  logf ~level:`trace "  top = [";
  print_indented 3 top;
  logf ~level:`trace "  ]\n";

  logf ~level:`trace "  havoc_locals = [";
  print_indented 3 havoc_locals;
  logf ~level:`trace "  ]\n";

  let weight_of_call_zero cs ct cen cex = K.zero in
  (*let summarizer (scc : BURG.scc) path_weight_internal context pathexp_algebra =*)
  let summarizer (scc : BURG.scc) path_graph context lower_summaries = 
    (* Entry-point of summarizer.  Here we have been given an SCC to work on. *)
    logf ~level:`info "Processing a call-graph SCC:";

    (*let is_within_scc (s,t) = List.mem (s,t) callgraph_scc in*)
    (*let is_scc_call s t = match WeightedGraph.edge_weight ts s t with
                          | Call (en, ex) -> scc_mem scc en ex 
                          | _ -> false in*)
    (* FIXME: eventually change all the code to use only classify_edge *)
    let classify_edge s t = 
      match WeightedGraph.edge_weight ts s t with
      | Call (en, ex) -> 
          if scc_mem scc en ex 
          then RecursiveCall (en,ex)
          else let summary = (M.find (en, ex) lower_summaries) in
               NonRecursiveCall (summary)
      | Weight w -> WeightedEdge w in
    let is_scc_call s t = 
      match classify_edge s t with 
      | RecursiveCall (_,_) -> true
      | _ -> false in 
    let call_edge_map = List.fold_left (fun pe_map (p_entry,p_exit,pathexpr) ->
        let scc_call_edges = find_recursive_calls ts pathexpr scc in
        IntPairMap.add (p_entry,p_exit) scc_call_edges pe_map)
      IntPairMap.empty 
      scc.procs in 
    let edge_weight_with_calls weight_of_call =
      BURG.weight_algebra (fun s t ->
          match M.find (s, t) ts.labels (*rg.labels*) with
          | Weight w -> w
          | Call (en, ex) -> 
              if is_scc_call s t (*is_within_scc (en,ex) *)
              then weight_of_call s t en ex
              else M.find (en, ex) lower_summaries) in
    (* path_weight_internal takes a (src,tgt) pair and 
          a call-mapping function (from the client, 
          returning type W.t), and it gives back a W.t for the 
          paths from src to tgt *)
    let path_weight_internal src tgt weight_of_call = 
      let weight = edge_weight_with_calls weight_of_call in
      WeightedGraph.path_weight path_graph src tgt
      |> NPathexpr.eval (* ~table:query.table *) weight in
    (* ---------------------- Non-recursive SCC ------------------------- *)
    if (List.length scc.procs == 1 
        && (let (p_entry,p_exit,pathexpr) = List.hd scc.procs in
        IntPairSet.cardinal 
          (IntPairMap.find (p_entry,p_exit) call_edge_map) == 0)) then
      (logf ~level:`info "  Non-recursive SCC.";
      let (p_entry,p_exit,pathexpr) = List.hd scc.procs in
      let single_proc_weight = 
        path_weight_internal p_entry p_exit weight_of_call_zero in
      postprocess_summaries
        [(p_entry,p_exit,project single_proc_weight)])
    else 
    begin
      (* -------------------- Recursive SCC ------------------------------ *)
        logf ~level:`info "  Recursive SCC."; 
      let is_linear = 
        List.fold_left (fun so_far (p_entry, p_exit, pathexpr) ->
          so_far && (check_linearity pathexpr is_scc_call))
        true
        scc.procs in
      (if is_linear then logf ~level:`info "  Linear recursion.");
      if is_linear && !chora_linspec then 
      begin
        postprocess_summaries
          (handle_linear_recursion scc classify_edge)
      end 
      else
      begin
        (* ------------------ Non-linear recursion ----------------------- *)
        logf ~level:`info "  Non-linear recursion.";
        let transition_footprint tr = 
          BatEnum.fold 
            (fun vs (var,term) -> VarSet.add var vs)
            VarSet.empty 
            (K.transform tr)
        in 
        let scc_footprint = 
          let var_set_alg = function
            | `Edge (s, t) ->
              begin match M.find (s, t) ts.labels with
                | Call (en, ex) -> 
                  if is_scc_call s t then VarSet.empty
                  else transition_footprint (M.find (en, ex) lower_summaries)
                | Weight w -> transition_footprint w
              end
            | `Mul (x, y) | `Add (x, y) -> VarSet.union x y
            | `Star x -> x
            | `Zero | `One -> VarSet.empty
          in
          List.fold_left (fun vars (p_entry,p_exit,pathexpr) ->
              VarSet.union vars (NPathexpr.eval var_set_alg pathexpr))
            VarSet.empty
            scc.procs
        in
        logf ~level:`info "  SCC footprint = [";
        VarSet.iter (fun v -> logf ~level:`info "%a;" (Cra.V.pp) v) scc_footprint;
        logf ~level:`info "]@.";
        let scc_global_footprint = 
          VarSet.filter (fun v -> Cra.V.is_global v) scc_footprint in 
        let scc_local_footprint = 
          VarSet.filter (fun v -> not (Cra.V.is_global v)) scc_footprint in 
        logf ~level:`info "  SCC locals footprint = [";
        VarSet.iter (fun v -> logf ~level:`info "%a;" (Cra.V.pp) v) scc_local_footprint;
        logf ~level:`info "]@.";

        List.iter (fun (u,v,p) -> 
            (logf ~level:`info "  Proc%s = %t" (proc_name_triple_string (u,v)) (fun f -> NPathexpr.pp f p))) scc.procs;
        let split_expr_map = List.fold_left (fun se_map (p_entry,p_exit,pathexpr) ->
            let edge s t = NPathexpr.mk_edge context s t in
            let pe_algebra = BURG.pathexp_algebra context in 
            let (rec_pe,nonrec_pe) = factor_pair pathexpr is_scc_call edge pe_algebra in
            (*let (rec_pe, nonrec_pe) = factor_pair pathexpr is_within_scc edge pe_algebra in*)
            logf ~level:`info "    Rec part: %t" (fun f -> NPathexpr.pp f rec_pe);
            logf ~level:`info "    Nonrec part: %t" (fun f -> NPathexpr.pp f nonrec_pe);
            ProcMap.add (p_entry,p_exit) (rec_pe,nonrec_pe) se_map)
          ProcMap.empty 
          scc.procs in 

        (*   ***   Compute the weights of the base case of each procedure  ***   *)
        let base_case_map = List.fold_left (fun bc_map (p_entry,p_exit,pathexpr) ->
            let (rec_pe,nonrec_pe) = ProcMap.find (p_entry,p_exit) split_expr_map in
            (*let base_case_weight = project (path_weight_internal p_entry p_exit weight_of_call_zero) in*)
            let base_case_weight = project (NPathexpr.eval (edge_weight_with_calls weight_of_call_zero) nonrec_pe) in
            logf ~level:`info "  base_case%s = [" (proc_name_triple_string (p_entry,p_exit)); 
              print_indented 15 base_case_weight; logf ~level:`info "  ]";
            ProcMap.add (p_entry,p_exit) base_case_weight bc_map)
          ProcMap.empty 
          scc.procs in 

        let simple_height = make_aux_variable (if !chora_dual then "RB" else "H") in 
        let (height_model, excepting) = 
          if !chora_dual then 
            let rm = make_aux_variable "RM" in 
            let mb = make_aux_variable "MB" in 
            (* When we perform dual-height analysis, we make two copies each (one "lower",
               one "upper") of most of the symbols in our vocabulary, but there
               are some exceptions, i.e., symbols that should not be copied.  The variable
               excepting holds the list of such symbols *)
            let excepting = List.fold_left (fun excepting v -> 
                let sym = Cra.V.symbol_of v in 
                let excepting = Srk.Syntax.Symbol.Set.add sym excepting in 
                Srk.Syntax.Symbol.Set.add (post_symbol sym) excepting)
              Srk.Syntax.Symbol.Set.empty
              (simple_height.value::rm.value::mb.value::program_vars) in 
            (RB_RM_MB (simple_height (* that is, rb *), rm, mb), excepting)
          else 
            (RB (simple_height), Srk.Syntax.Symbol.Set.empty) in 

        logf ~level:`info "  Beginning top-down analysis"; 
        (*   ***   Compute top-down summaries for each procedure   ***   *)
        let top_down_formula_map = 
          make_top_down_weight_multi scc.procs (*top*) ts is_scc_call lower_summaries 
            base_case_map simple_height 
            scc_local_footprint scc_global_footprint scc_footprint in
        logf ~level:`info "  Finished top-down analysis"; 

        (*   ***   Compute the abstraction that we will use for a call to each procedure  ***   *)
        let bounds_map = List.fold_left (fun b_map (p_entry,p_exit,pathexpr) ->
            let base_case_weight = ProcMap.find (p_entry,p_exit) base_case_map in 
            (*let bounds = make_call_abstraction base_case_weight scc_global_footprint in *)
            let (tr_symbols, base_case_fmla) = 
                to_transition_formula_with_unmodified base_case_weight scc_global_footprint in
            let bounds = make_call_abstraction base_case_fmla tr_symbols in 
            ProcMap.add (p_entry,p_exit) bounds b_map)
          ProcMap.empty 
          scc.procs in 
        (* Construct the recursive-case weight using the formula computed by make_call_abstraction *)
        let call_abstraction_weight_map = ProcMap.mapi
          (fun (p_entry,p_exit) info_structure ->
            let call_abstraction_weight = 
              of_transition_formula info_structure.tr_symbols info_structure.call_abstraction_fmla in
            logf ~level:`info "  call_abstration%s = [" (proc_name_triple_string (p_entry,p_exit)); 
            print_indented 15 call_abstraction_weight; logf ~level:`info "  ]";
            call_abstraction_weight)
          bounds_map in
        (* Define a function for handling calls to each procedure in the SCC *)
        let weight_of_call_rec cs ct cen cex = 
          (*let callee_bounds = ProcMap.find (cen,cex) bounds_map in
          callee_bounds.call_abstraction_weight in*)
          ProcMap.find (cen,cex) call_abstraction_weight_map in

        (*   ***   Compute the recursive-case weight/formula for each procedure  ***   *)
        let rec_fmla_map = List.fold_left (fun rf_map (p_entry,p_exit,pathexpr) ->
            (* WARNING: the following line isn't precise unless you take special action to
                 remove the base case later... *)
            (*let recursive_weight = path_weight_internal p_entry p_exit weight_of_call_rec in
            logf ~level:`info "  recursive_weight = [";
            print_indented 15 recursive_weight;
            logf ~level:`info "  ]";*)
            let (rec_pe,nonrec_pe) = ProcMap.find (p_entry,p_exit) split_expr_map in
            let recursive_weight_nobc = project (NPathexpr.eval (edge_weight_with_calls weight_of_call_rec) rec_pe) in
            logf ~level:`info "  recursive_weight-BC%s = [" (proc_name_triple_string (p_entry,p_exit));
            print_indented 15 recursive_weight_nobc;
            logf ~level:`info "  ]"; 
            (*ProcMap.add (p_entry,p_exit) recursive_weight_nobc rw_map;*)
            (* *)
            (* OLD: (* REMOVE BASE CASE semantically using the "recursion_flag" *)
            (*let initially_no_recursion = (assign_value_to_literal bounds.recursion_flag 0) in 
            let eventually_recursion = (assume_value_eq_literal bounds.recursion_flag 1) in 
            let recursive_weight_nobc = 
              K.mul (K.mul initially_no_recursion recursive_weight) eventually_recursion in*)*)
            let (tr_symbols, rec_fmla) = to_transition_formula recursive_weight_nobc in
            logf ~level:`trace "  rec_case_formula_body: @.%a@." (Srk.Syntax.Formula.pp srk) rec_fmla;
            ProcMap.add (p_entry,p_exit) rec_fmla rf_map)
          ProcMap.empty 
          scc.procs in 

        (*let summary_list = 
          make_height_based_summaries
            rec_fmla_map bounds_map program_vars top_down_formula_map scc height_model in*)

        let proc_key_list = List.map (fun (p_entry,p_exit,pathexpr) -> (p_entry,p_exit)) scc.procs in
         
        let summary_fmla_list = 
          make_height_based_summaries
            rec_fmla_map bounds_map top_down_formula_map proc_key_list height_model excepting in

        let summary_list = List.map (fun (proc_key,summary_fmla) ->
            let (p_entry,p_exit) = proc_key in
            (* Produce the final summary from this conjunction formula *)
            (*     FIXME: I should really be iterating over the SCC footprint variables,
                          not over the list of all program variables. *)
            let final_tr_symbols = 
              List.map (fun var -> 
                let pre_sym = Cra.V.symbol_of var in 
                let post_sym = post_symbol pre_sym in 
                (pre_sym,post_sym) ) program_vars in 
            let summary_weight = of_transition_formula final_tr_symbols summary_fmla in 
            log_tr_proc "@.    Final_summary%s = " p_entry p_exit summary_weight;
            (p_entry,p_exit,summary_weight))
          summary_fmla_list in 

        postprocess_summaries
          summary_list 
      end
    end in
  summarizer

let build_procedure_names_map rg = 
  RG.blocks rg |> BatEnum.iter (fun procedure ->
    let entry = (RG.block_entry rg procedure).did in
    let exit = (RG.block_exit rg procedure).did in
    let name = Varinfo.show procedure in 
    procedure_names_map := ProcMap.add (entry,exit) name !procedure_names_map)

let analyze_chora file =
  Cra.populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
    let rg = Interproc.make_recgraph file in
    build_procedure_names_map rg;
    let (ts, assertions) = Cra.make_transition_system rg in
    let summarizer = build_summarizer ts in
    (* *) 
    let query = BURG.mk_query ts summarizer in
    (* *)
    resource_bound_analysis rg query;
    check_assertions rg query main assertions
    end
  (* *)
  | _ -> assert false;;

let _ =
  CmdLine.register_pass
    ("-chora",
     analyze_chora,
     " Compositional recurrence analysis for non-linear recursion");
  CmdLine.register_config
    ("-chora-summaries",
     Arg.Set chora_print_summaries,
     " Print procedure summaries during the CHORA analysis pass");
  CmdLine.register_config
    ("-chora-debug-wedges",
     Arg.Set chora_print_wedges,
     " Print procedure summaries abstracted to wedges (for display only)");
  CmdLine.register_config
    ("-chora-wedgecover",
     Arg.Set chora_use_wedgecover,
     " Replace each summary with a disjunction of wedges (used at call sites)");
  (*CmdLine.register_config
    ("-chora-debug-depth-bounds",
     Arg.Set chora_print_depth_bound_wedges,
     " Print depth bound formulas abstracted to wedges");*)
  CmdLine.register_config
    ("-chora-debug-squeeze",
     Arg.Set chora_debug_squeeze,
     " Print 'squeezed' depth bound formula");
  CmdLine.register_config
    ("-chora-debug-recs",
     Arg.Set chora_debug_recs,
     " Print information about recurrences for non-linear recursion");
  (*CmdLine.register_config
    ("-chora-squeeze-sb",
     Arg.Set chora_squeeze_sb,
     " Convert depth-bound formula to simplified symbolic bounds");*)
  CmdLine.register_config
    ("-chora-no-squeeze-sb",
     Arg.Clear chora_squeeze_sb,
     " Do not convert depth-bound formula to simplified symbolic bounds");
  CmdLine.register_config
    ("-chora-squeeze",
     (*Arg.Set chora_squeeze_wedge,*)
     Arg.Unit (fun () -> chora_squeeze_wedge := true; chora_squeeze_sb := false),
     " Convert depth-bound formula to wedge");
  CmdLine.register_config
    ("-chora-squeeze-conjoin",
     Arg.Set chora_squeeze_conjoin,
     " Conjoin original depth-bound formula to its own squeezed version");
  CmdLine.register_config
    ("-chora-no-linspec",
     Arg.Clear chora_linspec,
     " Disable the special-case handling of linear recursion");
  CmdLine.register_config
    ("-chora-dual",
     Arg.Set chora_dual,
     " Compute non-trivial lower bounds in addition to upper bounds"); (* "dual-height" analysis *)
  CmdLine.register_config
    ("-chora-full",
     Arg.Unit (fun () -> chora_dual := true; chora_fallback := true),
     " Include a 'fallback' to height-based analysis in chora dual analysis");

