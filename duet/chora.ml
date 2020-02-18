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
module Pctx = Syntax.MakeContext ()  (* parsing context, for reachc code *)

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

  let make_aux_global_variable name = 
    let new_var = Core.Var.mk (Core.Varinfo.mk_global name (Core.Concrete (Core.Int 32))) in 
    let new_var_val = Cra.VVal new_var in 
    (* NOTE: in the following line, the function symbol_of puts a symbol into the hash table *)
    let new_var_sym = Cra.V.symbol_of new_var_val in 
    {value  = new_var_val;
     symbol = new_var_sym}
  
  let make_aux_local_variable name = 
    let new_var = Core.Var.mk (Core.Varinfo.mk_local name (Core.Concrete (Core.Int 32))) in 
    let new_var_val = Cra.VVal new_var in 
    (* NOTE: in the following line, the function symbol_of puts a symbol into the hash table *)
    let new_var_sym = Cra.V.symbol_of new_var_val in 
    {value  = new_var_val;
     symbol = new_var_sym}

  let make_aux_variable = make_aux_global_variable

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

let make_aux_procedure srk int_arity name = 
  Srk.Syntax.mk_symbol srk ~name 
    (`TyFun (List.init int_arity (fun n -> `TyInt), `TyBool))

let procedure_names_map = ref IntPairMap.empty

module ProcModuleC = struct
  module ProcMap = IntPairMap

  let proc_name_string (entry,exit) = 
    if IntPairMap.mem (entry,exit) !procedure_names_map then 
      let name = IntPairMap.find (entry,exit) !procedure_names_map in
      Format.sprintf "(%d,%d,\"%s\")" entry exit name
    else
      Format.sprintf "(%d,%d,?)" entry exit

  (*let proc_name_string (entry,exit) = 
    if ProcMap.mem (entry,exit) !procedure_names_map then 
      let name = ProcMap.find (entry,exit) !procedure_names_map in
      Format.sprintf "%s" name
    else
      Format.sprintf "<unknown procedure(%d,%d)>" entry exit*)
end

module ChoraC = ChoraCore.MakeChoraCore(ProcModuleC)(AuxVarModuleC)

open AuxVarModuleC
open ProcModuleC

(* The following flags are used inside ChoraCore, I think *)
(* let chora_dual = ChoraC.chora_dual*)
(* let chora_debug_recs = ChoraC.chora_debug_recs *)
(* let chora_fallback = ChoraC.chora_fallback *)

(* The following flags aren't used inside ChoraCore *)
let chora_use_wedgecover = ref false
(*let chora_print_depth_bound_wedges = ref false*)
let chora_print_summaries = ref false
let chora_print_wedges = ref false
let chora_debug_squeeze = ref false
let chora_squeeze_sb = ref true (* on by default, now *)
let chora_squeeze_wedge = ref false
let chora_squeeze_conjoin = ref false
let chora_linspec = ref true

let substitution_optimization = ref true  (* for reachc code *)
let reachc_retry_flag = ref true
let reachc_share_locals = ref true

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
  logf ~level formatter (proc_name_string (p_entry,p_exit));
  print_indented 17 tr;
  logf ~level "@."

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
    [ `ITensor of 'a * 'a       (* Note: really this is "tensor transpose" *)
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
    | ITensor of t * t           (* NOTE: really this is "tensor transpose" *)
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
    | IProject a -> x (* New rule in 2020 *)
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
    | IProjectT a -> x (* New rule in 2020 *)
    | _ -> HCT.hashcons ctx.tctx (IProjectT x)
  let rec mk_mulT ctx x y = match x.obj, y.obj with (* FIXME Make sure I don't make mul backwards somehow *)
    | IZeroT, _ -> mk_zeroT ctx
    | _, IZeroT -> mk_zeroT ctx
    | IOneT,  _ -> y
    | _, IOneT -> x
  (*  | ITensor(a,b), ITensor(c,d) when a.obj = IOne && c.obj = IOne -> 
            mk_tensor ctx (mk_one ctx) (mk_mul ctx b d) (* New rule in 2020 *)*)
  (*| ITensor(w,x), ITensor(y,z) -> mk_tensor ctx (mk_mul ctx y w) (mk_mul ctx x z)
    | IMulT(d,ITensor(w,x)), ITensor(y,z) -> mk_mulT ctx d (mk_tensor ctx (mk_mul ctx y w) (mk_mul ctx x z))
    | ITensor(w,x), IMulT(ITensor(y,z),c) -> mk_mulT ctx (mk_tensor ctx (mk_mul ctx y w) (mk_mul ctx x z)) c *)
    | _, _ -> HCT.hashcons ctx.tctx (IMulT (x, y))
  let mk_addT ctx x y = match x.obj, y.obj with
    | IZeroT, _ -> y
    | _, IZeroT -> x
  (*| ITensor(a,b), ITensor(c,d) when a.obj = IOne && c.obj = IOne -> 
            mk_tensor ctx (mk_one ctx) (mk_add ctx b d) (* New rule in 2020 *)*)
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
        (*let (xa,xb) = x in 
        let (va,vb) = v in 
        Printf.printf " Subst checking (%d,%d) against (%d,%d)\n" xa xb va vb;*)
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
module M = WeightedGraph.M

module U = Graph.Persistent.Digraph.ConcreteBidirectional(SrkUtil.Int)

type 'a weighted_graph = 'a WeightedGraph.weighted_graph



let project = K.exists Cra.V.is_global



(* .................................. *)
(*          proper contents           *)


module MakeBottomUpRecGraph (W : Weight) = struct
  open WeightedGraph

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

let depth_bound_formula_to_wedge depth_bound_formula sym = 
  let projection x =
    x = sym ||
    match Cra.V.of_symbol x with
    | Some v -> Core.Var.is_global (Cra.var_of_value v)
    | None -> false
  in
  let wedge = Wedge.abstract ~exists:projection srk depth_bound_formula in
  let level = if !chora_debug_squeeze then `always else `info in
  logf ~level " incorporating squeezed depth formula: %t" 
    (fun f -> Wedge.pp f wedge);
  Wedge.to_formula wedge
  (*let wedge_as_formula = Wedge.to_formula wedge in 
  Srk.Syntax.mk_and srk [depth_bound_formula; wedge_as_formula]*)

let depth_bound_formula_to_symbolic_bounds phi sym = 
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
 
let make_depth_bound_weight_multi procs (ts : K.t Cra.label Cra.WG.t) 
      is_scc_call lower_summaries base_case_map height 
      scc_local_footprint scc_global_footprint scc_footprint
      (* for debugging:  program_vars *) =
  (* Note: this height variable really represents depth *)
  let set_height_zero = assign_value_to_literal height.value 0 in 
  let increment_height = increment_variable height.value in 
  let assume_height_non_negative = assume_literal_leq_value 0 height.value in
  let depth_graph = ref BURG.empty in
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
                depth_graph := Srk.WeightedGraph.add_edge !depth_graph s (Weight low) t
              else begin
                (* A call from this SCC back into this SCC *)
                depth_graph := Srk.WeightedGraph.add_edge !depth_graph s (Weight havoc_loc_and_inc) en;
                depth_graph := Srk.WeightedGraph.add_edge !depth_graph s (Weight havoc_globals) t
              end
            | Weight w -> (* Regular (non-call) edge *)
              depth_graph := Srk.WeightedGraph.add_edge !depth_graph s (Weight w) t
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
      depth_graph := Srk.WeightedGraph.add_edge !depth_graph p_entry (Weight weight) !dummy_exit_node)
    procs;
  let td_formula_map = (List.fold_left (fun td_formula_map (p_entry,p_exit,pathexpr) ->
      match WeightedGraph.path_weight !depth_graph p_entry !dummy_exit_node with
      | Weight cycles ->
        let td_summary = K.mul set_height_zero cycles in
        let td_summary = K.mul td_summary assume_height_non_negative in
        let td_summary = project td_summary in (* FIXME Not sure this is needed *)
        logf ~level:`info "  multi_phi_td%s = [" (proc_name_string (p_entry,p_exit));
        print_indented 15 td_summary; logf ~level:`info "  ]\n";
        (*(if !chora_print_depth_bound_wedges then
        begin
          logf ~level:`always "  wedge[phi_td%t] is [" (proc_name_string (p_entry,p_exit));
          debug_print_depth_wedge td_summary;
          logf ~level:`always "  ]";
        end);*)
        let _, depth_bound_formula = to_transition_formula td_summary in
        logf ~level:`info "@.  dbf%s: %a" (proc_name_string (p_entry,p_exit))
            (Srk.Syntax.Formula.pp srk) depth_bound_formula;
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
        (*let to_be_squeezed = depth_bound_formula in (* naive version *) *)
        let to_be_squeezed = 
          (* sophisticated version: assume H' >= 0 inside squeezed version *) 
          Syntax.mk_and srk [post_height_gt_zero; depth_bound_formula] in
        let symbolic_bounds_depth_bound_formula = 
          if !chora_squeeze_sb || !chora_debug_squeeze
          then depth_bound_formula_to_symbolic_bounds to_be_squeezed post_height_sym
          else Syntax.mk_true srk in
        let wedge_depth_bound_formula = 
          if !chora_squeeze_wedge || !chora_debug_squeeze
          then depth_bound_formula_to_wedge to_be_squeezed post_height_sym
          else Syntax.mk_true srk in
        (*let incorporate_dbf fmla = 
          Syntax.mk_and srk [fmla; depth_bound_formula] in*)
        let incorporate_dbf fmla = 
            begin
              let case_split = 
                  Syntax.mk_or srk 
                    [(Syntax.mk_and srk [post_height_eq_zero; base_case_formula]);
                     (Syntax.mk_and srk [post_height_gt_zero; fmla])] in
              if !chora_squeeze_conjoin
              then Syntax.mk_and srk [depth_bound_formula; case_split]
              else case_split
            end
          in
        let final_depth_bound_formula = 
          if !chora_squeeze_sb
          then (if !chora_squeeze_wedge 
                then
                  failwith "ERROR: don't use -chora-squeeze and -chora-squeeze-sb simultaneously"
                else
                  incorporate_dbf symbolic_bounds_depth_bound_formula)
          else (if !chora_squeeze_wedge 
                then incorporate_dbf wedge_depth_bound_formula
                else depth_bound_formula) in 
        ProcMap.add (p_entry,p_exit) final_depth_bound_formula td_formula_map
      | _ -> failwith "A call was found in td_summary")
    ProcMap.empty procs) in
  td_formula_map;;

(*
let make_depth_bound_weight_oneproc p_entry path_weight_internal top scc_call_edges = 
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
  let depth_bound_summary = K.mul set_height_zero (K.star (K.mul increment_height sum_of_fragments)) in
  logf ~level:`info "  phi_td = [";
  print_indented 15 depth_bound_summary;
  logf ~level:`info "  ]\n";
  let depth_bound_symbols, depth_bound_formula = to_transition_formula depth_bound_summary in  
  logf ~level:`info "@.  dbf: %a"
      (Srk.Syntax.Formula.pp srk) depth_bound_formula;
  let is_post_height (pre_sym,post_sym) = (pre_sym == height_var_sym_pair.symbol) in 
  let post_height_sym = snd (List.find is_post_height depth_bound_symbols) in
  depth_bound_formula, post_height_sym;;
*)

let get_procedure_summary query rg procedure = 
  let entry = (RG.block_entry rg procedure).did in
  let exit = (RG.block_exit rg procedure).did in
  BURG.path_weight query entry exit

let print_procedure_summary_internal summary pp_fun pp_arg = 
  let level = if !chora_print_summaries then `always else `info in
  logf ~level:level "---------------------------------";
  logf ~level:level " -- Procedure summary for %a = " pp_fun pp_arg;
  print_indented ~level:level 0 summary;
  logf ~level:level "";
  if !chora_print_wedges then 
    (let level = if !chora_print_wedges then `always else `info in
     logf ~level:level " -- Procedure summary wedge for %a = @." pp_fun pp_arg;
     debug_print_wedge_of_transition summary)
  else ()

let print_procedure_summary procedure summary = 
  print_procedure_summary_internal summary Varinfo.pp procedure

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

let check_assertions query entry_main assertions = 
    if Srk.SrkUtil.Int.Map.cardinal assertions > 0 then
    logf ~level:`always "======= Assertion Checking ======";
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
  logf ~level:`info "  call edges = [ ";
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
       logf ~level:`info " %s := %a @." 
      (proc_name_string (p_entry'',p_exit'')) IcraPathExpr.pp (ipathexpr))
    icrapathexpr_equation_system;
  let transformed_ipathexpr_equation_system = 
      IntPairMap.fold (fun (p_entry, p_exit) _ eqs -> 
        let old_rhs = IcraPathExpr.mk_project ctx (* project is needed *)
          (IntPairMap.find (p_entry, p_exit) eqs) in
        logf ~level:`info " Acting on %s: @." (proc_name_string (p_entry,p_exit)); 
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
                logf ~level:`info " %s := %a @." 
                (proc_name_string (p_entry'',p_exit'')) IcraPathExpr.pp (ipathexpr))
              substituted_eqs;
          substituted_eqs)
        icrapathexpr_equation_system 
        icrapathexpr_equation_system in
  logf ~level:`info " Transformed equation system: @."; 
    IntPairMap.iter (fun (p_entry'',p_exit'') ipathexpr -> 
      logf ~level:`info " %s := %a @." 
      (proc_name_string (p_entry'',p_exit'')) IcraPathExpr.pp (ipathexpr))
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
      (*| `IStarT x -> (logf ~level:`info "    -Beginning tensored star"; logf ~level:`info "    -Its body is: %a" KK.pp x; let t = KK.star x in logf ~level:`info "    -The tensor-starred result is: %a" KK.pp t; logf ~level:`info "      -Ending tensored star"; t)*)
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
        logf ~level:`info " %s := @." (proc_name_string (p_entry'',p_exit''));
        print_indented ~level:`info 3 summary)
    assignment;
  summaries


(* This function post-processes all procedure summaries-- turning them
    into disjunctions of wedges-- if chora_use_wedgecover is true. *)
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
            (logf ~level:`info "  Proc%s = %t" (proc_name_string (u,v)) (fun f -> NPathexpr.pp f p))) scc.procs;
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
            logf ~level:`info "  base_case%s = [" (proc_name_string (p_entry,p_exit)); 
              print_indented 15 base_case_weight; logf ~level:`info "  ]";
            ProcMap.add (p_entry,p_exit) base_case_weight bc_map)
          ProcMap.empty 
          scc.procs in 

        let simple_height = make_aux_variable (if !ChoraC.chora_dual then "RB" else "H") in 
        let (height_model, excepting) = 
          if !ChoraC.chora_dual then 
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
            (ChoraC.RB_RM_MB (simple_height (* that is, rb *), rm, mb), excepting)
          else 
            (ChoraC.RB (simple_height), Srk.Syntax.Symbol.Set.empty) in 

        logf ~level:`info "  Beginning depth-bound analysis"; 
        (*   ***   Compute depth-bound summaries for each procedure   ***   *)
        let depth_bound_formula_map = 
          make_depth_bound_weight_multi scc.procs (*top*) ts is_scc_call lower_summaries 
            base_case_map simple_height 
            scc_local_footprint scc_global_footprint scc_footprint in
        logf ~level:`info "  Finished depth-bound analysis"; 

        (*   ***   Compute the abstraction that we will use for a call to each procedure  ***   *)
        let (bounds_map,tr_symbols_map) = List.fold_left (fun (b_map,tr_map) (p_entry,p_exit,pathexpr) ->
            let base_case_weight = ProcMap.find (p_entry,p_exit) base_case_map in 
            (*let bounds = ChoraC.make_hypothetical_summary base_case_weight scc_global_footprint in *)
            let (tr_symbols, base_case_fmla) = 
                to_transition_formula_with_unmodified base_case_weight scc_global_footprint in
            let param_prime = Str.regexp "param[0-9]+'" in
            let hs_projection x = 
              (let symbol_name = Srk.Syntax.show_symbol srk x in 
              let this_name_is_a_param_prime = Str.string_match param_prime symbol_name 0 in
              if this_name_is_a_param_prime then 
                ((*Format.printf "Rejected primed param symbol %s" symbol_name;*) false)
              else
                ((List.fold_left 
                    (fun found (vpre,vpost) -> found || vpre == x || vpost == x) 
                    false tr_symbols)
                  || 
                  is_var_global x
                ))
            in 
            let bounds = ChoraC.make_hypothetical_summary base_case_fmla hs_projection in 
            (ProcMap.add (p_entry,p_exit) bounds b_map,
             ProcMap.add (p_entry,p_exit) tr_symbols tr_map))
          (ProcMap.empty, ProcMap.empty)
          scc.procs in 
        (* Construct the recursive-case weight using the formula computed by make_hypothetical_summary *)
        let call_abstraction_weight_map = ProcMap.mapi
          (fun (p_entry,p_exit) info_structure ->
            let tr_symbols = ProcMap.find (p_entry,p_exit) tr_symbols_map in 
            let call_abstraction_weight = 
              of_transition_formula tr_symbols info_structure.ChoraC.call_abstraction_fmla in
            logf ~level:`info "  call_abstration%s = [" (proc_name_string (p_entry,p_exit)); 
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
            logf ~level:`info "  recursive_weight-BC%s = [" (proc_name_string (p_entry,p_exit));
            print_indented 15 recursive_weight_nobc;
            logf ~level:`info "  ]"; 
            (*ProcMap.add (p_entry,p_exit) recursive_weight_nobc rw_map;*)
            (* *)
            (* OLD: (* REMOVE BASE CASE semantically using the "recursion_flag" *)
            (*let initially_no_recursion = (assign_value_to_literal bounds.recursion_flag 0) in 
            let eventually_recursion = (assume_value_eq_literal bounds.recursion_flag 1) in 
            let recursive_weight_nobc = 
              K.mul (K.mul initially_no_recursion recursive_weight) eventually_recursion in*)*)
            let (_, rec_fmla) = to_transition_formula recursive_weight_nobc in
            logf ~level:`trace "  rec_case_formula_body: @.%a@." (Srk.Syntax.Formula.pp srk) rec_fmla;
            ProcMap.add (p_entry,p_exit) rec_fmla rf_map)
          ProcMap.empty 
          scc.procs in 

        (*let summary_list = 
          ChoraC.make_height_based_summaries
            rec_fmla_map bounds_map program_vars depth_bound_formula_map scc height_model in*)

        let proc_key_list = List.map (fun (p_entry,p_exit,pathexpr) -> (p_entry,p_exit)) scc.procs in
         
        let summary_fmla_list = 
          ChoraC.make_height_based_summaries
            rec_fmla_map bounds_map depth_bound_formula_map proc_key_list height_model excepting in

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

let analyze_chora_c file =
  Cra.populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
    let rg = Interproc.make_recgraph file in
    build_procedure_names_map rg;
    let (ts, assertions) = Cra.make_transition_system rg in
    let summarizer = build_summarizer ts in
    (* Compute summaries *) 
    let burg_query = BURG.mk_query ts summarizer in
    (* Using summaries, compute resource bounds *)
    resource_bound_analysis rg burg_query;
    (* Using summaries, check assertions *)
    check_assertions burg_query (RG.block_entry rg main).did assertions
    end
  (* *)
  | _ -> assert false;;


(* ************ REACHC STUFF ************** *)

module IntMap = BatMap.Int

let name_of_symbol ctx symbol = 
  match Syntax.symbol_name ctx symbol with
  | None -> Syntax.show_symbol ctx symbol
  | Some name -> name


let is_syntactic_false srk expr = 
  match Syntax.destruct srk expr with
  | `Fls -> true
  | _ -> false

let is_syntactic_true srk expr = 
  match Syntax.destruct srk expr with
  | `Tru -> true
  | _ -> false

let get_const srk term = 
  match Syntax.Term.destruct srk term with
  | `App (func, args) -> 
    if ((List.length args) = 0) then Some func else None
  | _ -> None

let is_predicate srk expr = 
  match Syntax.destruct srk expr with
  | `App (func, args) -> 
    (match Syntax.expr_typ srk expr with
    | `TyBool -> true
    | _ -> false)
  | _ -> false

let id_of_predicate srk pred = 
  match Syntax.destruct srk pred with
  | `App (func, args) -> 
    (match Syntax.expr_typ srk pred with
    | `TyBool -> Syntax.int_of_symbol func
    | _ -> failwith "id_of_predicate called on non-bool predicate")
  | _ -> failwith "id_of_predicate called on non-application"

let id_of_var srk var =
  match Syntax.destruct srk var with
  | `Var (vnum, typ) -> vnum
  | _ -> failwith "id_of_var called on non-variable"

let typ_of_var srk var =
  match Syntax.destruct srk var with
  | `Var (vnum, typ) -> typ
  | _ -> failwith "typ_of_var called on non-variable"

let find_predicates srk expr = 
  let alg = function
    | `And conjuncts -> List.concat conjuncts
    | `Or disjuncts -> List.concat disjuncts
    | `Quantify (_, name, typ, phi) -> phi
    | `Not (phi) -> phi
    | `Proposition (`Var i) -> failwith "Var-proposition in CHC"
    | `Proposition (`App (p, args)) -> 
      (*if is_predicate srk p then [id_of_predicate srk p] else []*)
      [Syntax.int_of_symbol p]
    | `Atom (_, x, y) -> []
    | `Ite (cond, bthen, belse) -> cond @ bthen @ belse
    | `Tru -> []
    | `Fls -> []
  in
  Syntax.Formula.eval srk alg expr


let logf_noendl ?(level=`info) =
  let sf = Format.std_formatter in 
  if (Log.level_leq (!Log.verbosity_level) level ||
      Log.level_leq (!my_verbosity_level) level)
  then Format.fprintf sf
  else Format.ifprintf sf

(*module VarSet = BatSet.Int*)

type atom_arg_t = Ctx.t Srk.Syntax.Term.t
type pred_num_t = int

type atom_t = {
    pred_num:pred_num_t;
    args:atom_arg_t list
}

type chc_t = {
   conc:atom_t;
   hyps:atom_t list;
   fmla:Ctx.t Srk.Syntax.Formula.t (* constraint formula *)
} 

type pred_info = {
   example_atom:atom_t; (* possibly-meaningful predicate names, arity, etc. *)
   (* arity ? *)
   (* types ? *)
   (* is this auxiliary? vs. is it taken from the original program? *)
}

module Chc = struct
  (* constrained horn clause *)

  module Atom = struct

    (* atom, i.e., predicate occurrence *)
    type t = atom_t

    let construct (pred_num:pred_num_t) (args:atom_arg_t list) : atom_t = 
      {pred_num=pred_num;args=args}

    let arg_of_symbol sym : atom_arg_t =
      Srk.Syntax.mk_const srk sym

    let print ?(level=`info) srk atom = 
      let n_args = List.length atom.args in 
      logf_noendl ~level "%s(" 
        (Syntax.show_symbol srk (Syntax.symbol_of_int atom.pred_num));
      List.iteri 
        (fun i arg ->
          (*Format.printf "%s" (Syntax.show_symbol srk sym);*)
          (*logf_noendl ~level "%a" (Syntax.pp_symbol srk) sym;*)
          logf_noendl ~level "%a" (Syntax.Term.pp srk) arg;
          if i != n_args - 1 then logf_noendl ~level ",")
        atom.args;
      logf_noendl ~level ")"

  end

  let construct 
        (conc:atom_t) (hyps:atom_t list) 
        (fmla:Ctx.t Srk.Syntax.Formula.t) : chc_t = 
    {conc=conc;hyps=hyps;fmla=fmla}

  let has_hyp chc target_hyp_num = 
    List.fold_left 
      (fun running hyp -> 
         (running || (hyp.pred_num = target_hyp_num)))
      false
      chc.hyps

  let symbol_of_term_opt term = 
    match Syntax.destruct srk term with
    | `App (func, args) when args = [] -> Some func
    | _ -> None

  let symbol_of_term ?(errormsg="fresh_symbols_for_args did not do its job") term = 
    match Syntax.destruct srk term with
    | `App (func, args) when args = [] -> func
    | _ -> failwith errormsg

  (** Replace all skolem constants appearing in the CHC
   *    with fresh skolem constants *)
  let fresh_skolem_all chc =
    let freshen_symbol_to_symbol =
      Memo.memo 
        (fun sym ->
          let name = name_of_symbol srk sym in
          let typ = Syntax.typ_symbol srk sym in
          Syntax.mk_symbol srk ~name typ) in
    let freshen_symbol_to_const sym =
      Syntax.mk_const srk (freshen_symbol_to_symbol sym) in
    let freshen_expr expr =
      Syntax.substitute_const srk freshen_symbol_to_const expr in
    let freshen_atom atom = 
      (* Term version *)
      let new_args = List.map freshen_expr atom.args in 
      Atom.construct atom.pred_num new_args in
    let new_conc_atom = freshen_atom chc.conc in
    let new_hyp_atoms = List.map freshen_atom chc.hyps in
    let new_phi = freshen_expr chc.fmla in
    construct new_conc_atom new_hyp_atoms new_phi

  (* 
  (* This old version generates equations only, never substitutions *)
  (* This function allows you to specify that some arguments within some
       atom should be replaced with a fresh variable even if other arguments
       within the same atom are not being replaced. *)
  let freshen_and_equate_args_finegrained chc plan_conc_atom plan_hyp_atom_list = 
    let chc = fresh_skolem_all chc in
    let old_atoms = chc.conc::chc.hyps in
    let plan_pseudo_atoms = plan_conc_atom::plan_hyp_atom_list in
    let equations = List.concat (List.map2 
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          assert (old_atom.pred_num = plan_pred_num);
          List.concat (List.map2 
             (fun old_arg plan_arg_option -> 
                 match plan_arg_option with
                 | None -> []
                 | Some new_arg -> [Syntax.mk_eq srk old_arg new_arg])
             old_atom.args
             plan_args))
      old_atoms
      plan_pseudo_atoms) in
    let new_atoms = List.map2
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          let new_args = List.map2
            (fun old_arg plan_arg_option ->
                match plan_arg_option with
                | None -> old_arg
                | Some new_arg -> new_arg)
            old_atom.args
            plan_args in
          Atom.construct old_atom.pred_num new_args)
      old_atoms
      plan_pseudo_atoms in
    let new_conc = List.hd new_atoms in
    let new_hyps = List.tl new_atoms in
    let new_phi = Syntax.mk_and srk (chc.fmla::equations) in
    construct new_conc new_hyps new_phi
  *) 

  (* This function allows you to specify that some arguments within some
       atom should be replaced with a fresh variable even if other arguments
       within the same atom are not being replaced. *)
  let freshen_and_equate_args_finegrained chc plan_conc_atom plan_hyp_atom_list = 
    let chc = fresh_skolem_all chc in
    let old_atoms = chc.conc::chc.hyps in
    let plan_pseudo_atoms = plan_conc_atom::plan_hyp_atom_list in
    let sub_targets = ref Syntax.Symbol.Set.empty in
    let seen_symbols = ref Syntax.Symbol.Set.empty in
    (if !substitution_optimization then 
    List.iter
      (fun plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          List.iter
            (fun plan_arg_opt ->
                match plan_arg_opt with
                | None -> ()
                | Some arg ->
                  match symbol_of_term_opt arg with
                  | None -> 
                    let new_symbols = Syntax.symbols arg in
                    seen_symbols := Syntax.Symbol.Set.union 
                      !seen_symbols new_symbols;
                    sub_targets := Syntax.Symbol.Set.diff
                      !sub_targets new_symbols
                  | Some sym -> 
                    if Syntax.Symbol.Set.mem sym !seen_symbols
                    then 
                      sub_targets := 
                        Syntax.Symbol.Set.remove sym !sub_targets
                    else 
                      (sub_targets := 
                         Syntax.Symbol.Set.add sym !sub_targets;
                       seen_symbols :=
                         Syntax.Symbol.Set.add sym !seen_symbols))
            plan_args)
      plan_pseudo_atoms);
    let sub_sources = ref Syntax.Symbol.Set.empty in
    let seen_symbols = ref Syntax.Symbol.Set.empty in
    (if !substitution_optimization then 
    List.iter
      (fun atom ->
          List.iter
            (fun arg ->
                match symbol_of_term_opt arg with
                | None -> 
                  let new_symbols = Syntax.symbols arg in
                  seen_symbols := Syntax.Symbol.Set.union 
                    !seen_symbols new_symbols;
                  sub_sources := Syntax.Symbol.Set.diff
                    !sub_sources new_symbols
                | Some sym -> 
                  if Syntax.Symbol.Set.mem sym !seen_symbols
                  then 
                    sub_sources := 
                      Syntax.Symbol.Set.remove sym !sub_sources
                  else 
                    (sub_sources := 
                      Syntax.Symbol.Set.add sym !sub_sources;
                    seen_symbols :=
                      Syntax.Symbol.Set.add sym !seen_symbols))
            atom.args)
      old_atoms);
    let check_substitution old_arg new_arg =
      match symbol_of_term_opt old_arg with
      | None -> None
      | Some src_sym ->
        if Syntax.Symbol.Set.mem src_sym !sub_sources
        then (match symbol_of_term_opt new_arg with
              | None -> None
              | Some tgt_sym -> 
                if Syntax.Symbol.Set.mem tgt_sym !sub_targets
                then Some (src_sym,new_arg)
                else None)
        else None in
    let substitutions = ref Syntax.Symbol.Map.empty in
    let equations = List.concat (List.map2 
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          assert (old_atom.pred_num = plan_pred_num);
          List.concat (List.map2 
             (fun old_arg plan_arg_option -> 
                 match plan_arg_option with
                 | None -> [] (* no new equation *)
                 | Some new_arg -> 
                   if !substitution_optimization
                   then match check_substitution old_arg new_arg with
                        | None -> (* create equation *)
                          [Syntax.mk_eq srk old_arg new_arg]
                        | Some (src_sym,tgt_term) ->
                          substitutions := 
                            Syntax.Symbol.Map.add
                              src_sym
                              tgt_term
                              !substitutions;
                          [] (* substitution instead of equation *)
                   else (* create equation *)
                     [Syntax.mk_eq srk old_arg new_arg])
             old_atom.args
             plan_args))
      old_atoms
      plan_pseudo_atoms) in
    let subbed_fmla = 
      if !substitution_optimization
      then Syntax.substitute_map srk !substitutions chc.fmla
      else chc.fmla in
    let new_atoms = List.map2
      (fun old_atom plan_pseudo_atom ->
          let (plan_pred_num,plan_args) = plan_pseudo_atom in
          let new_args = List.map2
            (fun old_arg plan_arg_option ->
                match plan_arg_option with
                | None -> old_arg
                | Some new_arg -> new_arg)
            old_atom.args
            plan_args in
          Atom.construct old_atom.pred_num new_args)
      old_atoms
      plan_pseudo_atoms in
    let new_conc = List.hd new_atoms in
    let new_hyps = List.tl new_atoms in
    let new_phi = Syntax.mk_and srk (subbed_fmla::equations) in
    construct new_conc new_hyps new_phi


  (* Coarse-grained version *)
  let freshen_and_equate_args chc plan_conc_atom plan_hyp_atom_list =
    let somes x = List.map (fun y -> Some y) x in
    let nones x = List.map (fun y -> None) x in
    let fg_conc_atom =
      match plan_conc_atom with
      | None -> (chc.conc.pred_num, nones chc.conc.args)
      | Some atom -> (chc.conc.pred_num, somes atom.args) in
    let fg_hyp_atom_list = 
      List.map2
        (fun plan_hyp_atom hyp ->
            match plan_hyp_atom with
            | None -> (hyp.pred_num, nones hyp.args)
            | Some atom -> (hyp.pred_num, somes atom.args))
        plan_hyp_atom_list
        chc.hyps in
    freshen_and_equate_args_finegrained chc fg_conc_atom fg_hyp_atom_list

  let freshen_and_equate_args_directly chc plan_conc_atom plan_hyp_atom_list =
    (* Old version that doesn't boil it down to a call to the fine-grained *)
    let chc = fresh_skolem_all chc in
    let old_atoms = chc.conc::chc.hyps in
    let new_atoms = plan_conc_atom::plan_hyp_atom_list in
    let equations = List.concat (List.map2 
      (fun old_atom new_atom_option ->
          match new_atom_option with
          | None -> []
          | Some new_atom ->
             begin
             assert (old_atom.pred_num = new_atom.pred_num);
             List.map2 
                (fun old_arg new_arg -> Syntax.mk_eq srk old_arg new_arg)
                old_atom.args
                new_atom.args
             end)
      old_atoms
      new_atoms) in
    let new_conc = match plan_conc_atom with
                   | None -> chc.conc
                   | Some new_conc_atom -> new_conc_atom in
    let new_hyps = 
        List.map2 (fun old_atom plan_hyp_atom ->
            match plan_hyp_atom with
            | None -> old_atom
            | Some new_hyp_atom -> new_hyp_atom)
        chc.hyps
        plan_hyp_atom_list in 
    let new_phi = Syntax.mk_and srk (chc.fmla::equations) in
    construct new_conc new_hyps new_phi
   
  (* Replace *every* atom-arg with a fresh symbol *)
  let fresh_symbols_for_args chc =
    let new_sym atom arg_num = 
        let name = 
          (name_of_symbol srk (Syntax.symbol_of_int atom.pred_num)) 
          ^ "_arg" ^ (string_of_int arg_num) in
        Syntax.mk_symbol srk ~name `TyInt in
    let atom_with_new_syms atom = 
        let new_args = List.mapi
          (fun arg_num arg ->
              let sym = new_sym atom arg_num in
              Syntax.mk_const srk sym)
          atom.args in
        Atom.construct atom.pred_num new_args in
    let plan_conc = Some (atom_with_new_syms chc.conc) in
    let plan_hyps = List.map
      (fun hyp -> Some (atom_with_new_syms hyp))
      chc.hyps in
    freshen_and_equate_args chc plan_conc plan_hyps

  let fresh_symbols_for_term_args chc =
    let new_sym atom arg_num = 
        let arg = List.nth atom.args arg_num in 
        match Syntax.destruct srk arg with
        | `App (func, f_args) when f_args = [] -> func
        | _ -> (* predicate argument term that isn't a var *)
          let name = 
            (name_of_symbol srk (Syntax.symbol_of_int atom.pred_num)) 
            ^ "_arg" ^ (string_of_int arg_num) in
          Syntax.mk_symbol srk ~name `TyInt in
    let atom_with_new_syms atom = 
        let new_args = List.mapi
          (fun arg_num arg ->
              let sym = new_sym atom arg_num in
              Syntax.mk_const srk sym)
          atom.args in
        Atom.construct atom.pred_num new_args in
    let plan_conc = Some (atom_with_new_syms chc.conc) in
    let plan_hyps = List.map
      (fun hyp -> Some (atom_with_new_syms hyp))
      chc.hyps in
    freshen_and_equate_args chc plan_conc plan_hyps

  (* This function makes all implicit constraints explicit. 
    
     An example of a CHC having implicit constraints is this one:
    
       P(x,y,z+1) :- Q(x,w,0,z*2) /\ phi
       
     which implicitly constrains the first arguments of P and Q to be
     equal, and implicitly constrains the last argument of P, minus one,
     to be half the last argument to Q, and implicitly constrains the
     second-to-last argument to Q to be zero, all without involving any
     explicit constrains in phi. *)
  let fresh_symbols_to_make_constraints_explicit chc =
    let atoms = chc.conc::chc.hyps in
    let seen_symbols = ref Syntax.Symbol.Set.empty in
    let plan_atoms = List.map
      (fun atom ->
          (atom.pred_num,
           List.map
             (fun arg ->
                 let new_symbols = Syntax.symbols arg in
                 let plan_arg = 
                   (* If we set this to None, we'll replace arg with a 
                        fresh constant; if we set it to Some t, we'll
                        replace arg with t.  *)
                   if Syntax.Symbol.Set.disjoint new_symbols !seen_symbols
                   then match symbol_of_term_opt arg with (*arg is unseen *)
                        | None -> None (*arg is a non-const term*)
                        | Some sym -> Some arg (*arg is an unseen const*)
                   else (* arg has been seen already *)
                      None in
                 seen_symbols := 
                     Syntax.Symbol.Set.union !seen_symbols new_symbols;
                 plan_arg)
             atom.args))
      atoms in
    let plan_conc_atom = List.hd plan_atoms in
    let plan_hyp_atoms = List.tl plan_atoms in
    freshen_and_equate_args_finegrained chc plan_conc_atom plan_hyp_atoms

  let subst_all outer_chc inner_chc = 
    let outer_chc = fresh_skolem_all outer_chc in
    let (outer_hyps_matching, outer_hyps_non_matching) = 
      List.partition
        (fun atom -> (atom.pred_num = inner_chc.conc.pred_num))
        outer_chc.hyps
      in
    (if List.length outer_hyps_matching = 0 
    then failwith "Mismatched subst_all call"
    else ());
    let (new_hyps, new_phis) = 
      List.fold_left
        (fun (hyps, phis) outer_hyp -> 
          assert (outer_hyp.pred_num = inner_chc.conc.pred_num);
          let plan_conc_atom = Some outer_hyp in
          let plan_hyp_atom_list = List.map (fun hyp -> None) inner_chc.hyps in
          let new_inner_chc = 
              freshen_and_equate_args 
                inner_chc plan_conc_atom plan_hyp_atom_list in
          (new_inner_chc.hyps @ hyps, new_inner_chc.fmla::phis))
        ([],[])
        outer_hyps_matching
      in
    let phi = Syntax.mk_and srk (outer_chc.fmla::new_phis) in
    let hyps = outer_hyps_non_matching @ new_hyps in
    construct outer_chc.conc hyps phi

  let disjoin chcs =
    match chcs with
    | [] -> failwith "Empty chc list in Chc.disjoin"
    | [chc1] -> chc1
    | chc1::old_chcs ->
      let chc1 = fresh_skolem_all chc1 in
      let chc1 = fresh_symbols_for_args chc1 in
      let new_phis = 
        List.map
          (fun old_chc ->
             let plan_conc_atom = Some chc1.conc in
             let plan_hyp_atom_list = List.map (fun hyp -> Some hyp) chc1.hyps in
             let new_chc = 
               freshen_and_equate_args
                 old_chc plan_conc_atom plan_hyp_atom_list in
             new_chc.fmla) 
          old_chcs in
      let new_phi = Syntax.mk_or srk (chc1.fmla::new_phis) in
      construct chc1.conc chc1.hyps new_phi

  let subst_equating_globally chc subst_map = 
    let sub_policy atom =
        if IntMap.mem atom.pred_num subst_map 
        then Some (IntMap.find atom.pred_num subst_map)
        else None in
    freshen_and_equate_args
      chc
      (sub_policy chc.conc)
      (List.map sub_policy chc.hyps)

  let print ?(level=`info) srk chc = 
    logf_noendl ~level "{ @[";
    List.iter 
      (fun pred -> Atom.print srk pred; logf_noendl ~level ";@ ")
      chc.hyps;    
    logf_noendl ~level "%a@ -> " (Syntax.Formula.pp srk) chc.fmla;
    Atom.print ~level srk chc.conc;
    logf_noendl ~level "@] }@."
 
  let print_as_wedge ?(level=`info) srk chc = 
    let chc = fresh_symbols_for_term_args chc in 
    logf_noendl ~level "{ @[";
    List.iter 
      (fun atom -> Atom.print srk atom; logf_noendl ~level ";@ ")
      chc.hyps;
    let all_preds = chc.conc::chc.hyps in 
    let all_pred_args =
      List.concat
        (List.map 
          (fun atom -> List.map symbol_of_term atom.args) all_preds) in
    let exists = (fun sym -> List.mem sym all_pred_args) in 
    let wedge = Wedge.abstract ~exists srk chc.fmla in
    logf_noendl ~level "%a@ -> " Wedge.pp wedge;
    Atom.print ~level srk chc.conc;
    logf_noendl ~level "@] }@."

  let to_transition chc = 
    let chc = fresh_symbols_for_args chc in
    assert (List.length chc.hyps = 1);
    let hyp_atom = List.hd chc.hyps in
    assert (hyp_atom.pred_num = chc.conc.pred_num);
    (*Var.reset_tables;*)
    (*List.iter (fun arg -> Var.register_var (symbol_of_term arg)) hyp_atom.args;*)
    (* conc_args and hyp_args are lists of symbols *)
    let transform = 
      List.map2 
        (fun pre post -> 
            (let pre_sym = symbol_of_term pre in 
             (* pre-state as variable *)
             (match Var.of_symbol pre_sym with
             | Some v -> v
             | _ -> failwith "Unregistered variable in to_transition"),
            (* post-state is term *)
            post
            (* if post-state were symbol: *) (*Syntax.mk_const srk post)*)))
        hyp_atom.args
        chc.conc.args
      in
    (chc, K.construct chc.fmla transform)

  (* Make a chc that corresponds to the identity transition, 
     on the model of the given model_chc.
     The returned chc will have the same atoms as model_chc.  *)
  let identity_chc model_chc =
    assert (List.length model_chc.hyps = 1);
    let hyp_pred = List.hd model_chc.hyps in
    assert (hyp_pred.pred_num = model_chc.conc.pred_num);
    let eqs = List.fold_left2
      (fun eqs hyp_arg conc_arg ->
          let eq = Syntax.mk_eq srk hyp_arg conc_arg in eq::eqs)
      [] 
      hyp_pred.args
      model_chc.conc.args
    in
    let phi = Syntax.mk_and srk eqs in
    construct model_chc.conc model_chc.hyps phi
  
  (* Make a fact chc having a false constraint, 
     on the model of the given conclusion atom. *)
  let false_fact conc_atom =
    let chc = construct conc_atom [] (Syntax.mk_false srk) in
    fresh_symbols_for_args chc 
  
  let of_transition tr model_chc : chc_t =
    if K.is_one tr then identity_chc model_chc else
    let post_shim = Memo.memo 
        (fun sym -> Syntax.mk_symbol srk 
         ~name:("Post_"^(Syntax.show_symbol srk sym)) `TyInt) in
    let (tr_symbols, post_def) =
      BatEnum.fold (fun (symbols, post_def) (var, term) ->
          let pre_sym = Var.symbol_of var in
          match get_const srk term with
          | Some existing_post_sym ->
            ((pre_sym,existing_post_sym)::symbols,post_def)
          | None -> 
            let new_post_sym = post_shim pre_sym in
            let post_term = Syntax.mk_const srk new_post_sym in
            ((pre_sym,new_post_sym)::symbols,(Syntax.mk_eq srk post_term term)::post_def)
          )
        ([], [])
        (K.transform tr)
    in
    let body =
      SrkSimplify.simplify_terms srk (Syntax.mk_and srk ((K.guard tr)::post_def))
    in
    (* Now, body is a formula over the pre-state and post-state variable pairs
       found in tr_symbols.  I assume that the pre-state variables haven't changed,
       but the post-state variables may have changed.  Because the post-state 
       variables may have changed, I will look up each of the variables in the
       predicate-occurrence in the hypothesis of the model rule and find the
       (new?) post-state variable that it corresponds to, and then I'll put that 
       variable into the predicate-occurrence in the conclusion of the rule that
       I return.  *)
    assert (List.length model_chc.hyps = 1);
    let hyp_pred = List.hd model_chc.hyps in
    assert (hyp_pred.pred_num = model_chc.conc.pred_num);
    let new_args = 
      List.map 
        (fun hyp_arg -> 
           let hyp_var = symbol_of_term hyp_arg in
           let rec go pairs = 
             match pairs with
             | (pre_sym, post_sym)::rest -> 
                     if hyp_var = pre_sym 
                     then Syntax.mk_const srk post_sym 
                     else go rest
             | [] -> logf ~level:`fatal "  ERROR: missing symbol %a" (Syntax.pp_symbol srk) hyp_var;
                     failwith "Could not find symbol in of_transition"
           in go tr_symbols)
        hyp_pred.args in
    let new_conc_pred = Atom.construct model_chc.conc.pred_num new_args in 
    (construct new_conc_pred model_chc.hyps body)

end

let build_chc_program srk1 srk2 phi query_pred =
  let rec get_rule vars rules phi = 
    match Syntax.destruct srk1 phi with
    | `Quantify (`Forall, nam, typ, expr) ->
       get_rule ((nam,typ)::vars) rules expr
    | `Or [nothyp; conc] ->
       (match Syntax.destruct srk1 nothyp with 
       | `Not (hyp) -> (hyp,conc,vars)::rules (* reverse? *)
       | _ -> logf ~level:`always "  Bad Rule: %a" (Syntax.Formula.pp srk1) phi;
              failwith "Unrecognized rule format (No negated hypothesis)")
    | _ -> logf ~level:`always "  Bad Rule: %a" (Syntax.Formula.pp srk1) phi;
           failwith "Unrecognized rule format (No top-level quantifier or disjunction)"
    in
  let rules = 
    match Syntax.destruct srk1 phi with
    | `And (parts) -> 
      List.fold_left 
        (fun rules psi -> get_rule [] rules psi)
        []
        parts
    | `Tru -> logf ~level:`always "RESULT: SAT (warning: empty CHC program; EMPTY_PROGRAM)";
      []
    | _ -> 
      (*uncomment to allow*) get_rule [] [] phi
      (*forbid*) (*failwith "Currently forbidden: single-clause CHC program"*)
    in 
  (* Filter out 'dummy rules' having conclusion 'true' *)
  let rules = List.filter 
    (fun (hyp,conc,vars) -> not (is_syntactic_true srk1 conc)) rules in 
  let rename_pred_internal sym = 
    let name = Syntax.show_symbol srk1 sym in
    Syntax.mk_symbol srk2 ~name:name `TyBool
    in
  let rename_pred = Memo.memo rename_pred_internal in
  let chc_record_of_rule (hyp,conc,vars) = 
    let var_to_skolem_internal var = 
      (let (name, typ) = List.nth vars var in
      match typ with 
      | `TyInt | `TyBool -> Syntax.mk_symbol srk2 ~name:name `TyInt 
      | `TyReal -> failwith "Unrecognized rule format (Real-valued variable)")
      in
    let var_to_skolem = Memo.memo var_to_skolem_internal in
    let convert_formula expr = 
      let mut_equations = ref [] in
      let mut_predicates = ref [] in
      let mut_booleans = ref Syntax.Symbol.Set.empty in
      let rec go_formula expr = 
        begin
          match Syntax.Formula.destruct srk1 expr with
          (* Negation node *)
          | `Not p ->
            begin
              match Syntax.Formula.destruct srk1 p with
              | `Proposition (`Var var) ->
                (* Special case: *)
                (* The boolean quantified variable var appears negatively here. *)
                (* We replace v with an integer variable w and assert w == 0. *)
                let sym = var_to_skolem var in 
                mut_booleans := Syntax.Symbol.Set.add sym !mut_booleans;
                Syntax.mk_eq srk2 (Syntax.mk_const srk2 sym) (Syntax.mk_real srk2 QQ.zero) 
              | _ -> 
              (* General case of negation: *)
              let subexpr = go_formula p in
              Syntax.mk_not srk2 subexpr
            end
          (* Non-recursive nodes *)
          | `Tru -> Syntax.mk_true srk2
          | `Fls -> Syntax.mk_false srk2
          | `Proposition (`Var var) ->
            (* The boolean quantified variable var appears positively here. *)
            (* We replace v with an integer variable w and assert w == 1. *)
            let sym = var_to_skolem var in 
            mut_booleans := Syntax.Symbol.Set.add sym !mut_booleans;
            Syntax.mk_eq srk2 (Syntax.mk_const srk2 sym) (Syntax.mk_real srk2 QQ.one) 
          | `Proposition (`App (f, args)) ->
            (* A horn-clause-predicate occurrence *)
            let fsym = rename_pred f in 
            let fnumber = Syntax.int_of_symbol fsym in
            let rec accum_arg_info (arglist: (('a, 'b) Syntax.expr) list) symbollist = 
              match arglist with
              | [] -> symbollist
              | orig_arg::more_args ->
                (* orig_arg is an argument to a horn-clause predicate *)
                begin
                  match Syntax.Expr.refine srk1 orig_arg with
                  | `Term arg ->
                  begin
                    (* Integer argument to horn-clause predicate *)
                    match Syntax.destruct srk1 arg with
                    | `Var (v, `TyInt) -> 
                      accum_arg_info more_args ((var_to_skolem v)::symbollist)
                    | `Var (v, `TyReal) ->
                      failwith "Unrecognized rule format (Got real predicate argument)"
                    | _ -> 
                      let term = go_term arg in
                      let termsymbol = Syntax.mk_symbol srk2 ~name:"TermSymbol" `TyInt in
                      let termeq = Syntax.mk_eq srk2 (Syntax.mk_const srk2 termsymbol) term in
                      mut_equations := termeq :: !mut_equations;
                      accum_arg_info more_args (termsymbol::symbollist)
                  end
                  | `Formula arg ->
                  begin
                    (* Boolean argument to horn-clause predicate *)
                    match Syntax.Formula.destruct srk1 arg with
                    | `Proposition (`Var var) ->
                      (* Common case: boolean variable *)
                      let sym = var_to_skolem var in 
                      (*mut_booleans := Syntax.Symbol.Set.add sym !mut_booleans;*)
                      accum_arg_info more_args (sym::symbollist)
                    | _ -> 
                      let subformula = go_formula arg in
                      let formulasymbol = Syntax.mk_symbol srk2 ~name:"FormulaSymbol" `TyInt in
                      let formulatrue = 
                        (Syntax.mk_eq srk2 
                          (Syntax.mk_const srk2 formulasymbol) 
                          (Syntax.mk_real srk2 (QQ.one))) in
                      let formulafalse = 
                        (Syntax.mk_eq srk2 
                          (Syntax.mk_const srk2 formulasymbol) 
                          (Syntax.mk_real srk2 (QQ.zero))) in
                      let notf f = Syntax.mk_not srk2 f in
                      let formulaiff = 
                          Syntax.mk_or srk2 
                            [Syntax.mk_and srk2 [ formulatrue;      subformula]; 
                             Syntax.mk_and srk2 [formulafalse; notf subformula]]
                      in
                      mut_equations := formulaiff :: !mut_equations;
                      accum_arg_info more_args (formulasymbol::symbollist)
                  end
                end
              in
            let argsymbols = accum_arg_info args [] in
            let argterms = List.map (fun sym -> Syntax.mk_const srk2 sym) argsymbols in
            let atom = Chc.Atom.construct fnumber (List.rev argterms) in
            mut_predicates := atom :: !mut_predicates;
            Syntax.mk_true srk2
          (* Recursive nodes: bool from something *)
          | `Ite (cond, bthen, belse) ->
            let cond_f = go_formula cond in
            let bthen_f = go_formula bthen in 
            let belse_f = go_formula belse in 
            Syntax.mk_ite srk2 cond_f bthen_f belse_f
          (* Recursive nodes: bool from bool *)
          | `And exprs -> 
            let subexprs = combine_formulas exprs in  
            Syntax.mk_and srk2 subexprs
          | `Or exprs ->
            let subexprs = combine_formulas exprs in  
            Syntax.mk_or srk2 subexprs
          (* Recursive nodes: bool from int *)
          | `Atom (op, s, t) -> 
            let (s_sub,t_sub) = combine_two_terms s t in
            (match op with
            | `Eq ->  Syntax.mk_eq srk2 s_sub t_sub
            | `Leq -> Syntax.mk_leq srk2 s_sub t_sub 
            | `Lt ->  Syntax.mk_lt srk2 s_sub t_sub)
          (* Format-violating nodes: *)
          | `Quantify (_,_,_,_) -> 
            logf ~level:`fatal "  Bad Rule: %a" (Syntax.Formula.pp srk1) expr;
            failwith "Unrecognized rule format (Got quantifier in rule)"
        end
      and go_term term = 
        begin
          match Syntax.Term.destruct srk1 term with
          (* Non-recursive nodes *)
          | `Real qq -> Syntax.mk_real srk2 qq
          | `Var (var, `TyInt) -> 
            let sym = var_to_skolem var in 
            Syntax.mk_const srk2 sym
          (* Recursive nodes: int from int *)
          | `Add terms ->
            let subexprs = combine_terms terms in  
            Syntax.mk_add srk2 subexprs
          | `Mul terms ->
            let subexprs = combine_terms terms in  
            Syntax.mk_mul srk2 subexprs
          | `Binop (`Div, s, t) ->
            let (s_sub,t_sub) = combine_two_terms s t in
            Syntax.mk_div srk2 s_sub t_sub
          | `Binop (`Mod, s, t) ->
            let (s_sub,t_sub) = combine_two_terms s t in
            Syntax.mk_mod srk2 s_sub t_sub
          | `Unop (`Floor, t) ->
            let subexpr = go_term t in
            Syntax.mk_floor srk2 subexpr
          | `Unop (`Neg, t) ->
            let subexpr = go_term t in
            Syntax.mk_neg srk2 subexpr
          | `Ite (cond, bthen, belse) ->
            let cond_f = go_formula cond in
            let bthen_f = go_term bthen in 
            let belse_f = go_term belse in 
            Syntax.mk_ite srk2 cond_f bthen_f belse_f
          (* Format-violating nodes: *)
          | `Var (v, `TyReal) ->
            logf ~level:`fatal "  Bad Rule: %a" (Syntax.Term.pp srk1) term;
            failwith "Unrecognized rule format (Got real-valued variable)"
          | `App (func, args) -> 
            logf ~level:`fatal "  Bad Rule: %a" (Syntax.Term.pp srk1) term;
            failwith "Unrecognized rule format (Got function application)"
        end
      and combine_formulas exprs = 
        begin
          List.fold_left
            (fun subexprs ex -> 
                let ex_s = go_formula ex in 
                (ex_s::subexprs))
            []
            exprs
        end
      and combine_terms exprs = 
        begin 
          List.fold_left
            (fun subexprs ex -> 
                let ex_s = go_term ex in 
                (ex_s::subexprs))
            []
            exprs
        end
      and combine_two_terms s t = 
        begin
          let s_sub = go_term s in
          let t_sub = go_term t in 
          (s_sub,t_sub)
        end
      in
      let phi = go_formula expr in
      (phi, !mut_predicates, !mut_equations, !mut_booleans)
      (* end of convert_formula *)
    in
    let (hyp_sub,hyp_preds,hyp_eqs,hyp_bools) = convert_formula hyp in
    let (conc_sub,conc_preds,conc_eqs,conc_bools) = convert_formula conc in
    let conc_atom = match conc_preds with
      | [conc_atom] -> conc_atom
      | [] -> 
        if (not (is_syntactic_false srk2 conc_sub))
        then failwith "Unrecognized rule format (Non-false non-predicate conclusion)"
        else Chc.Atom.construct query_pred []
      | _ -> failwith "Unrecognized rule format (Multiple conclusion predicate)"
    in 
    let eqs = hyp_eqs @ conc_eqs in
    let bools = Syntax.Symbol.Set.to_list 
      (Syntax.Symbol.Set.union hyp_bools conc_bools) in
    let bool_constraints = 
      List.map 
        (fun boolsym ->
           Syntax.mk_or srk2
             [(Syntax.mk_eq srk2 
               (Syntax.mk_const srk2 boolsym) 
              (Syntax.mk_real srk2 (QQ.zero))); 
             (Syntax.mk_eq srk2 
               (Syntax.mk_const srk2 boolsym) 
             (Syntax.mk_real srk2 (QQ.one)))])
       bools in
    let phi = Syntax.mk_and srk2 (hyp_sub::(eqs @ bool_constraints)) in
    (Chc.construct conc_atom hyp_preds phi)
    (* *)
  in
  List.map chc_record_of_rule rules

let print_summaries summaries = 
  logf ~level:`always "\n** Summaries as formulas **\n";
  BatMap.Int.iter
    (fun pred_num summary_rule ->
        Chc.print ~level:`always srk summary_rule;
        logf ~level:`always "  ")
    !summaries;
  logf ~level:`always "\n** Summaries as wedges **\n";
  BatMap.Int.iter
    (fun pred_num summary_rule ->
        Chc.print_as_wedge ~level:`always srk summary_rule;
        logf ~level:`always "  ")
    !summaries

let augment_pred_info_map pred_info_map chc_map = 
  let pred_info_map = ref pred_info_map in
  BatMap.Int.iter (fun pred_num chcs ->
      List.iter (fun chc -> 
          List.iter (fun atom ->
              if not (IntMap.mem atom.pred_num !pred_info_map)
              then let info = {example_atom=atom} in
                  pred_info_map := 
                    IntMap.add atom.pred_num info !pred_info_map)
          (chc.conc::chc.hyps))
      chcs)
  chc_map;
  !pred_info_map

let build_pred_info_map chc_map = 
  augment_pred_info_map (BatMap.Int.empty) chc_map

type procedure_info = {
    name : string;
    entry : int;
    exit : int;
    proc_symbol : Srk.Syntax.symbol;
    pred_symbol : Srk.Syntax.symbol;
}

(* Assume that the term is a symbol and return that symbol *)
let symbol_of_term term = 
  match Syntax.destruct srk term with
  | `App (func, args) when args = [] -> func
  | _ -> failwith "symbol_of_term saw a non-symbol term"

let arg_symbols_of_chc chc =
  let atoms = chc.conc::chc.hyps in
  List.concat
    (List.map
       (fun atom ->
           List.map
             (fun arg -> symbol_of_term arg)
             atom.args)
       atoms)

let arg_symbols_of_chc_hyps chc =
  let atoms = chc.hyps in
  List.concat
    (List.map
       (fun atom ->
           List.map
             (fun arg -> symbol_of_term arg)
             atom.args)
       atoms)

(*
(* For reference, here is CHORA's C-assertion-checking code *)
let check_assertions query entry_main assertions = 
    if Srk.SrkUtil.Int.Map.cardinal assertions > 0 then
    logf ~level:`always "======= Assertion Checking ======";
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
*)

(* This is the CHC equivalent of checking assertions *)
let analyze_query_procedure query_summary = 
  logf ~level:`info " query summary is: %a" K.pp query_summary;
  let phi = K.guard query_summary in
  match Wedge.is_sat srk phi with
  | `Sat -> logf ~level:`always "RESULT: UNKNOWN (final constraint is sat)"
  | `Unsat -> logf ~level:`always "RESULT: SAT (final constraint is unsat)"
  | `Unknown -> 
    if not !reachc_retry_flag then 
      logf ~level:`always "RESULT: UNKNOWN (final constraint unknown)"
    else
    begin
      logf ~level:`info "Preliminary: unknown (final constraint unknown)";
      logf ~level:`info "Retrying...";
      let wedge = Wedge.abstract srk phi in
      if Wedge.is_bottom wedge
      then logf ~level:`always "RESULT: SAT (final constraint is unsat)"
      else logf ~level:`always "RESULT: UNKNOWN (final constraint unknown)"
    end

let build_path_in_BURG 
      chc burg predsym_to_proc_map globals_map new_vertex shared_locals =
  let open WeightedGraph in
  let local_counter = ref 0 in
  let locals_map =
    List.fold_left
      (fun locals_map arg_sym -> 
          let var_record = 
            (if !reachc_share_locals
            then (let num_shared = List.length !shared_locals in
                 if !local_counter < num_shared
                 then List.nth !shared_locals (num_shared - !local_counter - 1)
                 else (let new_name = "local_" ^ (string_of_int !local_counter) in
                       let new_record = make_aux_local_variable new_name in
                       shared_locals := new_record :: !shared_locals;
                       new_record))
            else make_aux_local_variable (name_of_symbol srk arg_sym)) in
          local_counter := !local_counter + 1;
          Syntax.Symbol.Map.add arg_sym var_record locals_map)
      Syntax.Symbol.Map.empty
      (arg_symbols_of_chc_hyps chc) in
  (*let locals_list = 
    List.map
      (fun var_record -> var_record.value)
      (BatList.of_enum (Syntax.Symbol.Map.values locals_map)) in
  let havoc_locals = K.havoc locals_list in*)
  let proc = IntMap.find chc.conc.pred_num predsym_to_proc_map in
  let source_vertex = ref proc.entry in
  let append_edge ?target weight =
    let tgt = match target with 
              | None -> new_vertex () 
              | Some t -> t in
    burg := WeightedGraph.add_edge !burg !source_vertex weight tgt;
    source_vertex := tgt in
  (* Unnecessary edge: havoc the local vars of this chc *)
  (*append_edge (Weight havoc_locals);*)
  (* Next set of edges: two edges for each call *)
  List.iter
    (fun hyp -> 
        let callee = IntMap.find hyp.pred_num predsym_to_proc_map in
        (* Call edge *)
        append_edge (Call (callee.entry,callee.exit));
        (* The above call leaves results in globalvar_0,...,globalvar_n *)
        let assignments = 
          List.mapi
            (fun i arg ->
                let arg_sym = symbol_of_term arg in
                let local = Syntax.Symbol.Map.find arg_sym locals_map in
                let global_sym = (BatMap.Int.find i globals_map).symbol in
                let global_term = Syntax.mk_const srk global_sym in
                (* Now, we assign localvar_i := globalvar_i *)
                (local.value, global_term))
            hyp.args in
        (* Assignment edge *)
        (* DEBUGGING: REMOVE ME LATER *)
        (*let t =  in Format.printf "ASSIGNMENT EDGE of %s: %a@." 
          (name_of_symbol srk (Syntax.symbol_of_int chc.conc.pred_num)) K.pp t ;*)
        append_edge (Weight (K.parallel_assign assignments)))
    chc.hyps;
  (* Finally, we create an edge that assigns to the globals using the
       constraint of the given CHC *)
  (* Constants in the constraint formula that correspond to one of our
       local variables should be replaced by the corresponding
       local variable symbol *)
  let subst sym =
    let new_sym = if Syntax.Symbol.Map.mem sym locals_map 
    then (Syntax.Symbol.Map.find sym locals_map).symbol
                  else sym in
    Syntax.mk_const srk new_sym in
  let guard = Syntax.substitute_const srk subst chc.fmla in
  let assignments = 
    List.mapi
      (fun i arg ->
          let arg_sym = symbol_of_term arg in
          let arg_term = Syntax.mk_const srk arg_sym in
          let global_var = (BatMap.Int.find i globals_map).value in
          (* Now, we assign globalvar_i := conclusion_atom_arg_i *)
          (global_var, arg_term))
      chc.conc.args in

  (* DEBUGGING: REMOVE ME LATER *)
  (*let t = (K.construct guard assignments)  in
  Format.printf "TERMINAL EDGE of %s: %a@." 
    (name_of_symbol srk (Syntax.symbol_of_int chc.conc.pred_num)) K.pp t
  ;*)

  append_edge ~target:proc.exit (Weight (K.construct guard assignments))

let build_BURG_from_chc_map chc_map pred_info_map query_int =
  let num_globals =
    BatMap.Int.fold
      (fun _ pred_info_record running ->
          max running
            (List.length pred_info_record.example_atom.args))
      pred_info_map
      0 in
  let burg = ref BURG.empty in
  let last_vertex = ref 10000 in
  let new_vertex () = 
      last_vertex := !last_vertex + 1;
      burg := WeightedGraph.add_vertex !burg !last_vertex;
      !last_vertex in
  let predsym_to_proc_map =
    IntMap.fold
      (fun pred_symbol_int pred_info_record running ->
          let pred_symbol = Syntax.symbol_of_int pred_symbol_int in
          let name = name_of_symbol srk pred_symbol in
          let num_args = List.length pred_info_record.example_atom.args in
          let proc_symbol = make_aux_procedure srk num_args name in
          let entry = new_vertex () in
          let exit = new_vertex () in
          procedure_names_map := 
            ProcMap.add (entry,exit) name !procedure_names_map;
          let proc_info = 
              {name=name;entry=entry;exit=exit;
               proc_symbol=proc_symbol;pred_symbol=pred_symbol} in
          IntMap.add pred_symbol_int proc_info running)
      pred_info_map
      IntMap.empty in
  let globals_map =
    let nums = BatEnum.range 0 ~until:num_globals in
    BatEnum.fold
      (fun running num ->
          let num_str = string_of_int num in
          let val_sym = AuxVarModuleC.make_aux_global_variable ("g" ^ num_str) in
          IntMap.add num val_sym running)
      IntMap.empty
      nums in
  let shared_locals = ref [] in
  IntMap.iter
    (fun pred_symbol_int chcs ->
        List.iter
          (fun chc -> 
              build_path_in_BURG
                chc burg predsym_to_proc_map globals_map new_vertex shared_locals)
          chcs)
    chc_map;
  (!burg, predsym_to_proc_map)

(* Ensure that there always exists at least the query "false" *)
let append_trivial_query chc_map query_int =
  let query_atom = Chc.Atom.construct query_int [] in
  let trivial_query = Chc.false_fact query_atom in
  let query_chcs = BatMap.Int.find_default [] query_int chc_map in
  BatMap.Int.add query_int (trivial_query::query_chcs) chc_map

let analyze_chc_program chcs query_int = 
  let chc_map = List.fold_left
    (fun chc_map chc ->
      (* Required for sound (and non-crashing) analysis : 
          We force all predicate arguments to be (1) distinct (2) symbols.
          Both (1) and (2) are assumed by later code.  *)
      let chc = Chc.fresh_symbols_for_args chc in
      BatMap.Int.add
        chc.conc.pred_num
        (chc::(BatMap.Int.find_default [] chc.conc.pred_num chc_map))
        chc_map)
    BatMap.Int.empty
    chcs in
  let chc_map = append_trivial_query chc_map query_int in
  let pred_info_map = build_pred_info_map chc_map in
  logf ~level:`info "ChoraCHC: started build_BURG_from_chc_map@.";
  let (burg, predsym_to_proc_map) = 
      build_BURG_from_chc_map chc_map pred_info_map query_int in
  logf ~level:`info "ChoraCHC: finished build_BURG_from_chc_map@.";
  let query_proc = IntMap.find query_int predsym_to_proc_map in
  (* At this point, burg contains the bottom-up RecGraph that we want *)
  let summarizer = build_summarizer burg in
  (* Compute procedure summaries: *)
  logf ~level:`info "ChoraCHC: started BURG.mk_query@.";
  let burg_query = BURG.mk_query burg summarizer in
  logf ~level:`info "ChoraCHC: finished BURG.mk_query@.";
  (if !chora_print_summaries
  then 
      let procedures = BatList.of_enum (M.keys burg_query.summaries) in
      let procedures = procedures @ [(query_proc.entry,query_proc.exit)] in
      List.iter
        (fun (en,ex) ->
             let summary = BURG.path_weight burg_query en ex in
             let pp_fun = (fun fmt str -> Format.fprintf fmt "%s" str) in
             let pp_arg = ProcMap.find (en,ex) !procedure_names_map in
             print_procedure_summary_internal summary pp_fun pp_arg)
        procedures);
  (* Prepare to check assertions *)
  (*let query_entry_exit = (query_proc.entry,query_proc.exit) in*)
  (*let query_summary = M.find query_entry_exit burg_query.summaries in*)
  logf ~level:`info "ChoraCHC: started BURG.path_weight for query@.";
  let query_summary = 
    BURG.path_weight burg_query query_proc.entry query_proc.exit in
  logf ~level:`info "ChoraCHC: finished BURG.path_weight for query@.";
  (* Check assertions *)
  logf ~level:`info "ChoraCHC: started analyze_query_procedure@.";
  analyze_query_procedure query_summary;
  logf ~level:`info "ChoraCHC: finished analyze_query_procedure@."

let really_parse_smt2 file = 
  let filename = file.filename in
  (* FIXME let Z3 read the whole file... *)
  let chan = open_in filename in
  logf ~level:`info "ChoraCHC: started reading file@.";
  let str = really_input_string chan (in_channel_length chan) in
  logf ~level:`info "ChoraCHC: finished reading file@.";
  close_in chan;
  let z3ctx = Z3.mk_context [] in
  logf ~level:`info "ChoraCHC: started SrkZ3 parse@.";
  let phi = SrkZ3.load_smtlib2 ~context:z3ctx Pctx.context str in
  logf ~level:`info "ChoraCHC: finished SrkZ3 parse@.";
  let query_sym = Syntax.mk_symbol srk ~name:"QUERY" `TyBool in
  let query_int = Syntax.int_of_symbol query_sym in
  logf ~level:`info "ChoraCHC: started build_chc_program@.";
  let chcs = build_chc_program Pctx.context srk phi query_int in
  logf ~level:`info "ChoraCHC: finished build_chc_program@.";
  List.iter
    (fun chc ->
        logf_noendl ~level:`info "Incoming CHC: @.  ";
        Chc.print srk chc)
    chcs;
  analyze_chc_program chcs query_int

let dummy_parse_smt2 filename =
  let (dummy_file : CfgIr.file) = 
    {filename = filename (*"dummy_file"*);
     funcs = [];
     threads = [];
     entry_points = [];
     vars = [];
     types = [];
     globinit = None} in
  CfgIr.gfile := Some dummy_file;
  dummy_file

let _ = 
  CmdLine.register_parser ("smt2", dummy_parse_smt2);
  CmdLine.register_pass
    ("-chorachc",
     really_parse_smt2,
     " CHC analysis for non-linear recursion");
  CmdLine.register_config
    ("-chorachc-no-retry",
     Arg.Clear reachc_retry_flag,
     " Do not apply a second step of wedge abstraction to query summary");
  CmdLine.register_config
    ("-chorachc-no-share-locals",
     Arg.Clear reachc_share_locals,
     " Don't use a shared pool of local variables")

let _ =
  CmdLine.register_pass
    ("-chora",
     analyze_chora_c,
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
     " Print 'squeezed' depth-bound formula");
  CmdLine.register_config
    ("-chora-debug-recs",
     Arg.Set ChoraC.chora_debug_recs,
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
     Arg.Set ChoraC.chora_dual,
     " Compute non-trivial lower bounds in addition to upper bounds"); (* "dual-height" analysis *)
  CmdLine.register_config
    ("-chora-full",
     Arg.Unit (fun () -> ChoraC.chora_dual := true; ChoraC.chora_fallback := true),
     " Include a 'fallback' to height-based analysis in chora dual analysis");

