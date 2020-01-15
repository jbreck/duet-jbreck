open Core
open Apak
open CfgIr
open Srk

module RG = Interproc.RG
module G = RG.G

(*module K = NewtonDomain.ICRA*)  (* Unbound value K.exists *)
(*module K = Cra.K*)
module K = NewtonDomain.K
module KK = NewtonDomain.KK

module Ctx = NewtonDomain.Ctx

module Var = Cra.V
module VarSet = BatSet.Make(Cra.V)

include Log.Make(struct let name = "chora" end)
module A = Interproc.MakePathExpr(K)

(*let srk = Cra.srk *)


module type AuxVarHandler = sig
  type t (* type of an auxiliary variable *)
         (*   e.g., a Cra.value *)
  type val_sym = { 
      value: t; 
      symbol: Srk.Syntax.symbol
  }
  val make_variable : string -> val_sym
  val srk : 'a Syntax.context
end;;

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

open BatPervasives

module IntPair = struct
  type t = int * int [@@deriving ord]
  let equal (x,y) (x',y') = (x=x' && y=y')
  let hash = Hashtbl.hash
end
module IntPairMap = BatMap.Make(IntPair)
module IntPairSet = BatSet.Make(IntPair)

let procedure_names_map = ref IntPairMap.empty

let proc_name_triple entry exit channel = 
  if IntPairMap.mem (entry,exit) !procedure_names_map then 
    let name = IntPairMap.find (entry,exit) !procedure_names_map in
    Format.fprintf channel "(%d,%d,\"%s\")" entry exit name
  else
    Format.fprintf channel "(%d,%d,?)" entry exit

let proc_name entry exit channel = 
  if IntPairMap.mem (entry,exit) !procedure_names_map then 
    let name = IntPairMap.find (entry,exit) !procedure_names_map in
    Format.fprintf channel "%s" name
  else
    Format.fprintf channel "<unknown procedure(%d,%d)>" entry exit

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

let chora_print_summaries = ref false
let chora_print_wedges = ref false
let chora_use_wedgecover = ref false
(*let chora_print_depth_bound_wedges = ref false*)
let chora_debug_squeeze = ref false
let chora_debug_recs = ref false
(*let chora_squeeze_sb = ref false*)
let chora_squeeze_sb = ref true (* on by default, now *)
let chora_squeeze_wedge = ref false
let chora_squeeze_conjoin = ref false
let chora_linspec = ref true
let chora_dual = ref false (* compute non-trivial lower bounds in addition to upper bounds *)
let chora_fallback = ref false
let chora_just_allow_decrease = ref false (* WARNING: it's unsound to set this to true *)

type val_sym = { 
    value: Cra.value; 
    symbol:Srk.Syntax.symbol
}
type height_model_type = 
    (* Root to baseline of tree *)
    | RB of val_sym 
    (* Root to baseline, root to midline, midline to baseline *)
    (*   where the midline is defined as the depth of the shallowest leaf *)
    | RB_RM_MB of val_sym * val_sym * val_sym 

let make_variable name = 
  let new_var = Core.Var.mk (Core.Varinfo.mk_global name (Core.Concrete (Core.Int 32))) in 
  let new_var_val = Cra.VVal new_var in 
  (* NOTE: in the following line, the function symbol_of puts a symbol into the hash table *)
  let new_var_sym = Cra.V.symbol_of new_var_val in 
  {value  = new_var_val;
   symbol = new_var_sym}

(* ugly: copied from newtonDomain just for debugging *)
let print_indented ?(level=`info) indent k =
      logf ~level:level "%a"
      (fun f () -> Format.printf "%s"
          (SrkUtil.mk_show (fun formatter tr ->
              Format.pp_open_vbox formatter indent;
              Format.pp_print_break formatter 0 0;
              Format.fprintf formatter "%a" K.pp tr;
              Format.pp_close_box formatter ()) k)) ()

let post_symbol =
  Memo.memo (fun sym ->
    match Var.of_symbol sym with
    | Some var ->
      Srk.Syntax.mk_symbol Cra.srk ~name:(Var.show var ^ "'") (Var.typ var :> Srk.Syntax.typ)
    | None -> assert false)

let upper_symbol =
  Memo.memo (fun sym ->
   Srk.Syntax.mk_symbol Cra.srk 
     ~name:("Rm_"^(Srk.Syntax.show_symbol Cra.srk sym)) 
     (Srk.Syntax.typ_symbol Cra.srk sym))

let lower_symbol =
  Memo.memo (fun sym ->
   Srk.Syntax.mk_symbol Cra.srk 
     ~name:("Mb_"^(Srk.Syntax.show_symbol Cra.srk sym)) 
     (Srk.Syntax.typ_symbol Cra.srk sym))

let rb_symbol =
  Memo.memo (fun sym ->
   Srk.Syntax.mk_symbol Cra.srk 
     ~name:("Rb_"^(Srk.Syntax.show_symbol Cra.srk sym)) 
     (Srk.Syntax.typ_symbol Cra.srk sym))

let to_transition_formula tr =
  let (tr_symbols, post_def) =
    BatEnum.fold (fun (symbols, post_def) (var, term) ->
        let pre_sym = Var.symbol_of var in
        let post_sym = post_symbol pre_sym in
        let post_term = Srk.Syntax.mk_const Cra.srk post_sym in
        ((pre_sym,post_sym)::symbols,
          (Srk.Syntax.mk_eq Cra.srk post_term term)::post_def))
      ([], [])
      (K.transform tr)
  in
  let body =
    SrkSimplify.simplify_terms Cra.srk (Srk.Syntax.mk_and Cra.srk ((K.guard tr)::post_def))
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
  let unmodified_inclusive_body = Srk.Syntax.mk_and Cra.srk
    (body::(List.map 
      (fun sym -> Srk.Syntax.mk_eq Cra.srk
        (Srk.Syntax.mk_const Cra.srk sym)
        (Srk.Syntax.mk_const Cra.srk (post_symbol sym)))
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
          | Some v -> (v, Srk.Syntax.mk_const Cra.srk post)::tr
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
    (fun f -> Wedge.pp f (Wedge.abstract ~exists:projection Cra.srk body))

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
    (fun f -> Wedge.pp f (Wedge.abstract ~exists:projection Cra.srk body))

type 'a bound_info = {
  bound_pairs : (Srk.Syntax.symbol * 'a Srk.Syntax.term) list;
  (*recursion_flag : Cra.value;*)
  (*call_abstraction_weight : K.t;*)
  tr_symbols : (Srk.Syntax.symbol * Srk.Syntax.symbol) list;
  call_abstraction_fmla : 'a Srk.Syntax.formula
}

let assign_value_to_literal value literal = 
  K.assign value (Srk.Syntax.mk_real Cra.srk (Srk.QQ.of_int literal))

(*let assume_value_eq_literal value literal = 
  let var = Cra.V.symbol_of value in 
  K.assume (Srk.Syntax.mk_eq Cra.srk 
    (Srk.Syntax.mk_const Cra.srk var)
    (Srk.Syntax.mk_real Cra.srk (Srk.QQ.of_int literal)))*)

let assume_literal_leq_value literal value = 
  let var = Cra.V.symbol_of value in 
  K.assume (Srk.Syntax.mk_leq Cra.srk 
    (Srk.Syntax.mk_real Cra.srk (Srk.QQ.of_int literal))
    (Srk.Syntax.mk_const Cra.srk var))

let increment_variable value = 
  K.assign
    value 
    (Srk.Syntax.mk_add 
      Cra.srk
      [(Srk.Syntax.mk_const Cra.srk (Cra.V.symbol_of value));
       (Srk.Syntax.mk_real Cra.srk (Srk.QQ.of_int 1))])

(*let make_call_abstraction base_case_weight scc_global_footprint = 
  let (tr_symbols, body) = 
      to_transition_formula_with_unmodified base_case_weight scc_global_footprint in*)
let make_call_abstraction base_case_fmla tr_symbols = 
  let param_prime = Str.regexp "param[0-9]+'" in
  let projection x = 
    (
    let symbol_name = Srk.Syntax.show_symbol Cra.srk x in 
    let this_name_is_a_param_prime = Str.string_match param_prime symbol_name 0 in
    if this_name_is_a_param_prime then 
        ((*Format.printf "Rejected primed param symbol %s" symbol_name;*) false)
    else
    ( 
      (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
      || 
      match Cra.V.of_symbol x with 
      | Some v -> Cra.V.is_global v
      | None -> false (* false *)
    ))
  in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk base_case_fmla in 
  logf ~level:`info "\n  base_case_wedge = %t \n\n" (fun f -> Wedge.pp f wedge);
  let cs = Wedge.coordinate_system wedge in 
  let bounding_atoms = ref [] in
  let bound_list = ref [] in
  let add_bounding_var vec negate =
    let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
    if CoordinateSystem.type_of_vec cs vec = `TyInt then
    begin
      let term = CoordinateSystem.term_of_vec cs vec in 
      (*logf ~level:`info "  base-case-bounded term: %a \n" (Srk.Syntax.Term.pp Cra.srk) term;*)
      (* *)
      (* Hacky Optional Behavior: Ignore CRA's auto-generated array-position and array-width variables *)
      let name = Srk.Syntax.Term.show Cra.srk term in
      match String.index_opt name '@' with | Some i -> () | None ->
      begin
        let bounding_var_sym_pair = make_variable "B_in" in
        (*let bounding_var = Core.Var.mk (Core.Varinfo.mk_global "B_in" (Core.Concrete (Core.Int 32))) in 
          let bounding_var_sym = Cra.V.symbol_of (Cra.VVal bounding_var) in  *)
        let bounding_term = Srk.Syntax.mk_const Cra.srk bounding_var_sym_pair.symbol in 
        let bounding_atom = Srk.Syntax.mk_leq Cra.srk term bounding_term in 
        bounding_atoms := bounding_atom            :: (!bounding_atoms);
        bound_list     := (bounding_var_sym_pair.symbol, term) :: (!bound_list) 
      end
    end
  in
  let handle_constraint = function 
    | (`Eq, vec) ->
      (*logf ~level:`info "  rec equation: %a \n" Linear.QQVector.pp vec;*)
      add_bounding_var vec true; 
      add_bounding_var vec false
    | (`Geq, vec) ->
      add_bounding_var vec true in 
  List.iter handle_constraint (Wedge.polyhedron wedge);
  (*let rec_flag_var_sym_pair = make_variable "Recursion_Flag" in
  let rec_flag_var = Core.Var.mk (Core.Varinfo.mk_global "Recursion_Flag" ( Core.Concrete (Core.Int 32))) in 
    let rec_flag_val = Cra.VVal rec_flag_var in 
    let _ = Cra.V.symbol_of rec_flag_val in (* Add to symbol table... (HACK!) *)
  let set_rec_flag = assign_value_to_literal rec_flag_var_sym_pair.value 1 in *)
  let call_abstraction_fmla = Srk.Syntax.mk_and Cra.srk (!bounding_atoms) in 
  (*let call_abstraction_weight = of_transition_formula tr_symbols call_abstraction_fmla in*)
    {bound_pairs = !bound_list;
     (*recursion_flag = rec_flag_var_sym_pair.value;*)
     (*call_abstraction_weight = K.mul set_rec_flag call_abstraction_weight *)(*}*)
     tr_symbols = tr_symbols;
     call_abstraction_fmla = (*K.mul set_rec_flag*) call_abstraction_fmla}

type 'a recurrence_collection = {
  done_symbols: int Srk.Syntax.Symbol.Map.t; (* accepted *)
  ineq_tr: (Srk.Syntax.Symbol.Map.key * Srk.Syntax.Symbol.Map.key) list;
  blk_transforms: Srk.QQ.t array array list;
  blk_adds: Srk.Polynomial.QQXs.t array list;
  (*rev_term_of_id: ((Cra.Ctx.t, 'a) Srk.Syntax.expr) list;*)
  term_of_id: ((Cra.Ctx.t, 'a) Srk.Syntax.expr) BatDynArray.t;
  n_recs_accepted: int;
  n_recs_specified: int
}

type recurrence_candidate = {
  outer_sym: Srk.Syntax.symbol;
  inner_sym: Srk.Syntax.symbol;
  (*coeff: Srk.QQ.t;*)
  sub_cs: Cra.Ctx.t Srk.CoordinateSystem.t;
  inequation: (Srk.QQ.t * int) list;
  dependencies: Srk.Syntax.symbol list (* what other same-stratum symbols does this depend on? *)
}

let accept_candidate candidate recurrences = 
  BatDynArray.add recurrences.term_of_id (Srk.Syntax.mk_const Cra.srk candidate.inner_sym);
  let new_num = recurrences.n_recs_accepted in 
  logf ~level:`trace "   Accepted candidate recurrence: inner_sym=%d rec_num=%d" (Srk.Syntax.int_of_symbol candidate.inner_sym) new_num;
  {done_symbols = 
      if Srk.Syntax.Symbol.Map.mem candidate.inner_sym recurrences.done_symbols 
      then recurrences.done_symbols
      else Srk.Syntax.Symbol.Map.add candidate.inner_sym new_num recurrences.done_symbols;
   ineq_tr = (candidate.inner_sym, candidate.outer_sym)::recurrences.ineq_tr;
   blk_transforms = recurrences.blk_transforms;
   blk_adds = recurrences.blk_adds;
   (*rev_term_of_id = (Srk.Syntax.mk_const Cra.srk candidate.inner_sym)::recurrences.rev_term_of_id;*)
   term_of_id = recurrences.term_of_id;
   n_recs_accepted = recurrences.n_recs_accepted + 1;
   n_recs_specified = recurrences.n_recs_specified}

let register_recurrence transform_block add_block recurrences = 
  (* FIXME I should somehow sanity-check that register_recurrence is being called 
     in the same order as accept_candidate was called *)
  {done_symbols = recurrences.done_symbols;
   ineq_tr = recurrences.ineq_tr;
   blk_transforms = transform_block::recurrences.blk_transforms;
   blk_adds = add_block::recurrences.blk_adds;
   term_of_id = recurrences.term_of_id;
   n_recs_accepted = recurrences.n_recs_accepted;
   n_recs_specified = recurrences.n_recs_specified + (Array.length transform_block)};;

let empty_recurrence_collection () = 
  {done_symbols = Srk.Syntax.Symbol.Map.empty;
   ineq_tr = [];
   blk_transforms = [];
   blk_adds = [];
   term_of_id = BatDynArray.create ();
   (*rev_term_of_id = [];*)
   n_recs_accepted = 0;
   n_recs_specified = 0}

let count_recurrences recurrences = 
  Srk.Syntax.Symbol.Map.cardinal recurrences.done_symbols

type term_examination_result = 
  | DropTerm
  | DropInequation 
  | UseInnerTerm of Srk.QQ.t * int 
  | UseInnerTermWithDependency of Srk.QQ.t * int * (Srk.Syntax.symbol list)
  | UseSelfOuterTerm of Srk.QQ.t * int 
  | UseConstantTerm of Srk.QQ.t * int

let build_sub_dim_to_rec_num_map recurrences sub_cs = 
  (* Option 1: build from done_symbols *)
  (*Srk.Syntax.Symbol.Map.fold
    (fun sym recurrence_number old_map -> 
      let sub_dim = (CoordinateSystem.cs_term_id sub_cs (`App (sym, []))) in 
      BatMap.Int.add sub_dim (recurrence_number) old_map)
    recurrences.done_symbols
    BatMap.Int.empty*)
  (* *)
  (* Option 2: build from coordinate system *)
  BatEnum.fold (fun oldmap sub_dim ->
      match CoordinateSystem.destruct_coordinate sub_cs sub_dim with
      | `App (sym,_) -> 
        if Srk.Syntax.Symbol.Map.mem sym recurrences.done_symbols then
          let recurrence_number = 
            Srk.Syntax.Symbol.Map.find sym recurrences.done_symbols in
          BatMap.Int.add sub_dim recurrence_number oldmap
        else oldmap
      | _ -> oldmap)
    BatMap.Int.empty
    (0 -- (CoordinateSystem.dim sub_cs - 1))

let rec build_polynomial recurrences sub_cs coeff dim = 
  match CoordinateSystem.destruct_coordinate sub_cs dim with 
  | `App (sym,_) -> 
    ((*Format.printf "****BPOLY build_polynomial saw a symbol@.";*)
     let rec_num = 
       Srk.Syntax.Symbol.Map.find sym recurrences.done_symbols in
     let poly = Polynomial.QQXs.of_dim rec_num in 
     Polynomial.QQXs.scalar_mul coeff poly)
  | `Mul (x,y) -> 
    ((*Format.printf "****BPOLY build_polynomial saw a `Mul@.";*)
     let x_poly = build_vector_dims recurrences sub_cs x in 
     let y_poly = build_vector_dims recurrences sub_cs y in
     let poly = Polynomial.QQXs.mul x_poly y_poly in 
     Polynomial.QQXs.scalar_mul coeff poly)
  | _ -> failwith "Unrecognized polynomial part in build_polynomial"
and build_vector_dims recurrences sub_cs inner_vector = 
  BatEnum.fold 
    (fun running_poly (coeff,dim) -> 
       let poly = build_polynomial recurrences sub_cs coeff dim in
       let poly = Polynomial.QQXs.scalar_mul coeff poly in
       Polynomial.QQXs.add running_poly poly)
    Polynomial.QQXs.zero
    (Srk.Linear.QQVector.enum inner_vector)

let build_recurrence sub_cs recurrences target_inner_sym target_outer_sym 
                     new_coeffs_and_dims blk_transform sub_dim_to_rec_num = 
  let max_rec_number = 
    Srk.Syntax.Symbol.Map.fold
      (fun sym recurrence_number old_max -> max old_max recurrence_number)
      recurrences.done_symbols 0 in
  let blk_last = (Array.length blk_transform) - 1 in
  let blk_start = recurrences.n_recs_specified in 
  let new_vec = Linear.QQVector.of_list new_coeffs_and_dims in
  let target_inner_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_inner_sym, [])) in 
  let target_outer_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_outer_sym, [])) in 
  let inner_rec_num = BatMap.Int.find target_inner_dim sub_dim_to_rec_num in 
  logf ~level:`trace "   blk_start %d@.   max_rec_number %d@.   inner_rec_num %d@.   nb_recs_in_block %d@.   blk_last %d@.   target_inner_sym %d" 
    blk_start max_rec_number inner_rec_num (Array.length blk_transform) blk_last (Srk.Syntax.int_of_symbol target_inner_sym);
  assert (inner_rec_num >= blk_start);
  (* Now process a constant offset *)
  let const_coeff = Linear.QQVector.coeff CoordinateSystem.const_id new_vec in 
  let const_add_poly = Polynomial.QQXs.scalar const_coeff in 
  (* Eventually I need to process possible terms over this B_in *)
  let blk_add_entry = List.fold_left 
    (fun poly (coeff,dim) -> 
      if dim = CoordinateSystem.const_id then poly 
      else if dim = target_outer_dim then poly 
      else if BatMap.Int.mem dim sub_dim_to_rec_num then
        begin
          let rec_num = BatMap.Int.find dim sub_dim_to_rec_num in 
          if rec_num < blk_start then (* lower stratum *)
            (* Build up a blk_add_entry to be returned *)
            let monomial = Polynomial.Monomial.singleton rec_num 1 in(*lin!*)
            Polynomial.QQXs.add_term coeff monomial poly
          else (* same stratum *) 
            (* In-place modification of blk_transform parameter *)
            (* REV: Should I write blk_last-x here, so that I flip 
               the recurrences backwards to match term_of_id? *)
            let col = (*blk_last-*)inner_rec_num-blk_start in
            let row = (*blk_last-*)rec_num-blk_start in
            ((*Format.printf "Writing a %a to col=%d, row=%d@." QQ.pp coeff col row;*)
            blk_transform.(col).(row) <- coeff;
            poly)
        end
      (*else build_polynomial recurrences sub_cs coeff dim*)
      else Polynomial.QQXs.add poly
          (build_polynomial recurrences sub_cs coeff dim) )
        (* (failwith "Unrecognized component of recurrence inequation")) *)
    const_add_poly
    new_coeffs_and_dims in 
  blk_add_entry;;

let is_an_inner_symbol sym b_in_b_out_map = 
  Srk.Syntax.Symbol.Map.mem sym b_in_b_out_map

let log_fmla_proc ?(level=`info) formatter p_entry p_exit formula = 
  logf ~level formatter (proc_name_triple p_entry p_exit)
      (Srk.Syntax.Formula.pp Cra.srk) formula

let log_tr_proc formatter p_entry p_exit tr = 
  logf ~level:`info formatter (proc_name_triple p_entry p_exit);
  print_indented 17 tr;
  logf ~level:`info "@."

let rename_b_in_to_zero b_in_b_out_map solution = 
  let subst_b_in_with_zeros sym = 
    if is_an_inner_symbol sym b_in_b_out_map
    then Srk.Syntax.mk_real Cra.srk QQ.zero 
    else Srk.Syntax.mk_const Cra.srk sym in 
  Srk.Syntax.substitute_const Cra.srk subst_b_in_with_zeros solution 

(* Build a procedure summary for one procedure.
 *
 * Q. What's happening in case of mutual recursion? 
 * A. Well, in case of mutual recursion, we have built and solved a 
 *      recurrence for the current SCC; this recurrence may describe
 *      several b_out bounding symbols, of which only a subset apply to
 *      the procedure we're currently summarizing.  When we get to this 
 *      point in the code, the solution formula describes all of those
 *      bounding symbols.  However, the bounding_conjunction that we build
 *      here references only the b_out bounding symbols that apply to the 
 *      procedure that we're currently working on.  In that way, we're about
 *      to build a summary that is specific to this procedure, even though
 *      we started from a recurrence solution that is the same for all
 *      procedures in the current SCC. *)
let build_height_based_summary 
    solution b_in_b_out_map bounds top_down_formula program_vars 
    p_entry p_exit = 
  (* b_in = 0: In the height-based analysis, initial b_in values equal zero *)
  let solution_starting_at_zero = rename_b_in_to_zero b_in_b_out_map solution in 
  let level = if !chora_debug_recs then `always else `info in
  log_fmla_proc ~level "@.    simplified%t: @.    %a" p_entry p_exit solution_starting_at_zero;
  (* each term <= each b_out:  *)
  let bounding_conjunction = 
    let make_bounding_conjuncts (in_sym,term) =
      let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in 
      Srk.Syntax.mk_leq Cra.srk term (Srk.Syntax.mk_const Cra.srk out_sym)
    in
    let bounding_conjuncts = 
      List.map make_bounding_conjuncts bounds.bound_pairs in 
    Srk.Syntax.mk_and Cra.srk bounding_conjuncts in 
  log_fmla_proc "@.    bddg conj%t: %a" p_entry p_exit bounding_conjunction; 
  (* top_down formula /\ (solution with b_in = 0) /\ each term <= each b_out *)
  let big_conjunction = 
    Srk.Syntax.mk_and Cra.srk [top_down_formula; 
                               solution_starting_at_zero;
                               bounding_conjunction] in
  log_fmla_proc "@.    big conj%t: %a" p_entry p_exit big_conjunction; 
  (* Produce the final summary from this conjunction formula *)
  (*     FIXME: I should really be iterating over the SCC footprint variables,
                not over the list of all program variables. *)
  let final_tr_symbols = 
    List.map (fun var -> 
      let pre_sym = Cra.V.symbol_of var in 
      let post_sym = post_symbol pre_sym in 
      (pre_sym,post_sym)) program_vars in 
  let height_based_summary = of_transition_formula final_tr_symbols big_conjunction in 
  log_tr_proc "@.    HBA_summary%t = " p_entry p_exit height_based_summary;
  height_based_summary

let substitute_one_sym formula old_sym new_sym =  
  let subst_rule sym = 
    if sym == old_sym 
    then Srk.Syntax.mk_const Cra.srk new_sym  
    else Srk.Syntax.mk_const Cra.srk sym in
  Srk.Syntax.substitute_const Cra.srk subst_rule formula

let lower_some_symbols formula excepting = 
  let subst_rule sym = 
    if Srk.Syntax.Symbol.Set.mem sym excepting 
    then Srk.Syntax.mk_const Cra.srk sym
    else Srk.Syntax.mk_const Cra.srk (lower_symbol sym) in 
  Srk.Syntax.substitute_const Cra.srk subst_rule formula

let upper_some_symbols formula excepting = 
  let subst_rule sym = 
    if Srk.Syntax.Symbol.Set.mem sym excepting 
    then Srk.Syntax.mk_const Cra.srk sym
    else Srk.Syntax.mk_const Cra.srk (upper_symbol sym) in 
  Srk.Syntax.substitute_const Cra.srk subst_rule formula

let rb_some_symbols formula excepting = 
  let subst_rule sym = 
    if Srk.Syntax.Symbol.Set.mem sym excepting 
    then Srk.Syntax.mk_const Cra.srk sym
    else Srk.Syntax.mk_const Cra.srk (rb_symbol sym) in 
  Srk.Syntax.substitute_const Cra.srk subst_rule formula

(* In this function, we build up a bunch of formulas F1...F8 and then
     we conjoin them.  To ensure that the different conjuncts are "wired
     together" correctly, we do a lot of renaming the symbols in the
     different formulas so that the ones that are supposed to talk to
     each other do so, and the ones that aren't don't. *)
let build_dual_height_summary 
      rb rm mb rm_solution mb_solution b_in_b_out_map bounds top_down_formula 
      excepting program_vars p_entry p_exit height_model = 
  (* F1: rb top-down formula (Root-->Baseline), serving to constrain rb *)
  let rb_topdown = lower_some_symbols top_down_formula excepting in
  log_fmla_proc "@.    rb_tdf%t: %a" p_entry p_exit rb_topdown;
  (* F2: rm top-down formula (Root-->Midline), serving to constrain rm *)
  let rm_topdown = substitute_one_sym 
    top_down_formula (post_symbol rb.symbol) (post_symbol rm.symbol) in
  let rm_topdown = upper_some_symbols rm_topdown excepting in
  log_fmla_proc "@.    rm_tdf%t: %a" p_entry p_exit rm_topdown;
  (* F3: height equation: rb = rm + mb*)
  let rb_const = Srk.Syntax.mk_const Cra.srk (post_symbol rb.symbol) in 
  let rm_const = Srk.Syntax.mk_const Cra.srk (post_symbol rm.symbol) in 
  let mb_const = Srk.Syntax.mk_const Cra.srk (post_symbol mb.symbol) in 
  let height_eq = Srk.Syntax.mk_eq Cra.srk rb_const
    (Srk.Syntax.mk_add Cra.srk [rm_const; mb_const]) in
  log_fmla_proc "@.    ht_eq%t: %a" p_entry p_exit height_eq;
  (* F3: height inequation: rm <= rb *)
  let height_ineq = Srk.Syntax.mk_leq Cra.srk rm_const rb_const in
  log_fmla_proc "@.    ht_ineq%t: %a" p_entry p_exit height_ineq;
  (* F5: mb solution relating mb, b_in_low, b_out_low, with b_in_low = 0 *)
  let original_mb_solution = mb_solution in 
  let mb_solution = rename_b_in_to_zero b_in_b_out_map mb_solution in 
  let mb_solution = lower_some_symbols mb_solution excepting in
  log_fmla_proc "@.    mb_simplified%t: %a" p_entry p_exit mb_solution;
  (* F6: rm solution relating rm, b_in_up, b_out_up *)
  let rm_solution = upper_some_symbols rm_solution excepting in
  log_fmla_proc "@.    rm_unsimplified%t: %a" p_entry p_exit rm_solution;
  (* F7: bound_upper: each prog. var. term <= each b_out_up:  *)
  let bound_upper = 
    let make_bounding_conjuncts (in_sym,term) =
      let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in 
      Srk.Syntax.mk_leq Cra.srk term (Srk.Syntax.mk_const Cra.srk out_sym) in
    let bounding_conjuncts = 
      List.map make_bounding_conjuncts bounds.bound_pairs in 
    Srk.Syntax.mk_and Cra.srk bounding_conjuncts in 
  let bound_upper = upper_some_symbols bound_upper excepting in 
  log_fmla_proc "@.    bd_up conj%t: %a" p_entry p_exit bound_upper;
  (* F8: bound_bridge: 0 <= b_in_up /\ b_in_up <= b_out_low *)
  let bound_bridge = 
    let make_bridging_conjuncts in_sym =
      let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in
      let up_in_const = Srk.Syntax.mk_const Cra.srk (upper_symbol in_sym) in 
      let low_out_const = Srk.Syntax.mk_const Cra.srk (lower_symbol out_sym) in
      let zero = Srk.Syntax.mk_real Cra.srk QQ.zero in
      Srk.Syntax.mk_and Cra.srk
        [Srk.Syntax.mk_leq Cra.srk zero up_in_const;
         Srk.Syntax.mk_leq Cra.srk up_in_const low_out_const] in
    let scc_b_in_symbols = 
      Srk.Syntax.Symbol.Map.fold
        (fun in_sym _ rest -> in_sym::rest)
        b_in_b_out_map
        [] in 
    let bridging_conjuncts = 
      List.map make_bridging_conjuncts scc_b_in_symbols in 
    Srk.Syntax.mk_and Cra.srk bridging_conjuncts in 
  log_fmla_proc "@.    bd_bridge conj%t: %a" p_entry p_exit bound_bridge;
  let first_part = [rb_topdown;rm_topdown;height_eq;height_ineq] in
  let last_part = [mb_solution;bound_bridge;rm_solution;bound_upper] in
  (* ===== Optional "Fallback" to height-based analysis ===== *)
  (* F9(optional) bound_rb: each prog. var. term <= each b_out_rb *)
  let fallback = if !chora_fallback then begin
    let bound_rb = 
      let make_bounding_conjuncts (in_sym,term) =
        let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in 
        Srk.Syntax.mk_leq Cra.srk term (Srk.Syntax.mk_const Cra.srk out_sym) in
      let bounding_conjuncts = 
        List.map make_bounding_conjuncts bounds.bound_pairs in 
      Srk.Syntax.mk_and Cra.srk bounding_conjuncts in 
    let bound_rb = rb_some_symbols bound_rb excepting in 
    log_fmla_proc "@.    bd_rb conj%t: %a" p_entry p_exit bound_rb;
    (* F10(optional) rb solution relating rb, b_in_rb, b_out_rb with b_in_rb=0 *)
    let rb_solution = substitute_one_sym 
      original_mb_solution (post_symbol mb.symbol) (post_symbol rb.symbol) in
    let rb_solution = rename_b_in_to_zero b_in_b_out_map rb_solution in 
    let rb_solution = rb_some_symbols rb_solution excepting in
    log_fmla_proc "@.    rb_simplified%t: %a" p_entry p_exit rb_solution;
    [bound_rb;rb_solution]
  end else [] in 
  (* ==============  End of Fallback section   ============== *)
  (* big_conjunction *)
  let big_conjunction = Srk.Syntax.mk_and Cra.srk 
    (first_part @ fallback @ last_part) in
  log_fmla_proc "@.    DHA conj%t: %a" p_entry p_exit big_conjunction; 
  (* Produce the final summary from this conjunction formula *)
  (*     FIXME: I should really be iterating over the SCC footprint variables,
                not over the list of all program variables. *)
  let final_tr_symbols = 
    List.map (fun var -> 
      let pre_sym = Cra.V.symbol_of var in 
      let post_sym = post_symbol pre_sym in 
      (pre_sym,post_sym) ) program_vars in 
  let dual_height_summary = of_transition_formula final_tr_symbols big_conjunction in 
  log_tr_proc "@.    DHA_summary%t = " p_entry p_exit dual_height_summary;
  dual_height_summary

let sanity_check_recurrences recurrences term_of_id = 
  (if not ((List.length recurrences.blk_transforms) ==
           (List.length recurrences.blk_adds)) then
     failwith "Matrix recurrence transform/add blocks mismatched.");
  let print_expr i term = 
      logf ~level:`trace "  term_of_id[%d]=%a" i (Srk.Syntax.Expr.pp Cra.srk) term in
  (*let pp_dim f i = 
      Format.asprintf "%a" (Srk.Syntax.Expr.pp Cra.srk) (term_of_id.(i)) in*)
  let pp_dim f i = 
      Format.fprintf f "%a" (Srk.Syntax.Expr.pp Cra.srk) (term_of_id.(i)) in
  Array.iteri print_expr term_of_id;
  let print_blocks b trb = 
      let ab = List.nth recurrences.blk_adds ((List.length recurrences.blk_adds) - b - 1) in
      logf ~level:`trace "  Chora Block %d" b;
      let col_widths = Array.make ((Array.length trb) + 1) 0 in
      let strings = Array.make_matrix (Array.length trb) ((Array.length trb)+1) "" in
      for i = 0 to (Array.length trb) - 1 do
          let row = trb.(i) in
          for j = 0 to (Array.length row) - 1 do
              strings.(i).(j) <- QQ.show trb.(i).(j);
              col_widths.(j) <- max (col_widths.(j)) (String.length strings.(i).(j))
          done;
          let _ = Format.flush_str_formatter () in 
          Format.fprintf Format.str_formatter " %a " (Srk.Polynomial.QQXs.pp pp_dim) (ab.(i));
          let addstr = Format.flush_str_formatter () in
          let j = Array.length row in
          strings.(i).(j) <- addstr;
          col_widths.(j) <- max (col_widths.(j)) (String.length strings.(i).(j))
      done;
      for i = 0 to ((Array.length strings) - 1) do
          let row = strings.(i) in
          let rowstr = ref "|" in 
          for j = 0 to (Array.length row) - 2 do
              let strlen = String.length strings.(i).(j) in 
              rowstr := !rowstr ^ strings.(i).(j) ^ (String.make (col_widths.(j) - strlen) ' ') ^ "|"
          done;
          let j = (Array.length row) - 1 in
          rowstr := !rowstr ^ "  ++  |" ^ strings.(i).(j) ^ "|";
          rowstr := Str.global_replace (Str.regexp "\n") " " !rowstr;
          logf ~level:`trace "    [ %s ] " !rowstr
      done
    in 
  List.iteri print_blocks (List.rev recurrences.blk_transforms);
  let adds_size = List.fold_left (fun t arr -> t + Array.length arr) 0 recurrences.blk_adds in
  (if not (adds_size == (Array.length term_of_id)) then
     (Format.printf "Size of term_of_id is %d@." (Array.length term_of_id);
     Format.printf "Size of blk_transforms is %d@." (Array.length term_of_id);
     failwith "Matrix recurrence and term_of_id are of mismatched size."));
  let check_block_sizes trb ab = 
    let goodsize = (Array.length trb) in
    if not (goodsize == (Array.length ab)) then
        failwith "Matrix recurrence transform/add blocks are unequal size."
    else ()
    in
  List.iter2 check_block_sizes recurrences.blk_transforms recurrences.blk_adds

(* Filter out recurrences having unmet dependencies         *)
(*        AND in the future maybe prioritize recurrences    *)
(*   Don't extract more than one recurrence for each symbol *)
let rec filter_candidates recurrence_candidates recurrences =
  logf ~level:`trace "  Filtering recurrence candidates";
  let nb_recurs = List.length !recurrence_candidates in 
  let earlier_candidates = ref Srk.Syntax.Symbol.Set.empty in 
  let drop_redundant_recs recur = 
    (* Rule: at most one recurrence per bounding symbol *) 
    let result = 
      (not (Srk.Syntax.Symbol.Map.mem recur.inner_sym recurrences.done_symbols)) 
      &&
      (not (Srk.Syntax.Symbol.Set.mem recur.inner_sym !earlier_candidates)) in
    earlier_candidates := 
      Srk.Syntax.Symbol.Set.add recur.inner_sym !earlier_candidates; 
    result in 
  recurrence_candidates := 
      List.filter drop_redundant_recs !recurrence_candidates;
  let symbols_of_candidates = 
    let add_symbol_candidate syms recur = 
      Srk.Syntax.Symbol.Set.add recur.inner_sym syms in
    List.fold_left add_symbol_candidate
      Srk.Syntax.Symbol.Set.empty
      !recurrence_candidates in 
  let drop_rec_with_unmet_deps recur = 
    List.fold_left (fun ok dep -> ok &&
        (* Rule: no unmet dependencies *)
        ((Srk.Syntax.Symbol.Set.mem dep symbols_of_candidates)
         ||
         (Srk.Syntax.Symbol.Map.mem dep recurrences.done_symbols)))
      true
      recur.dependencies in 
  recurrence_candidates := 
      List.filter drop_rec_with_unmet_deps !recurrence_candidates;
  if (List.length !recurrence_candidates) < nb_recurs
  then filter_candidates recurrence_candidates recurrences 

(* Accept remaining recurrence candidates *) 
let accept_and_build_recurrences 
    recurrence_candidates recurrences allow_interdependence =
  let foreach_candidate_accept recurrences candidate = 
    accept_candidate candidate recurrences in 
  let recurrences = 
    List.fold_left 
      foreach_candidate_accept recurrences !recurrence_candidates in 
  (* PHASE: build recurrence matrices *) 
  let foreach_block_build recurrences candidate_block = 
    if List.length candidate_block = 0 then recurrences else
    let nRecurs = List.length candidate_block in 
    logf ~level:`trace "  Beginning to build a block of size: %d" (nRecurs);
    let blk_transform = Array.make_matrix nRecurs nRecurs QQ.zero in 
    let foreach_candidate_build add_entries candidate = 
      let sub_dim_to_rec_num = 
        build_sub_dim_to_rec_num_map recurrences candidate.sub_cs in 
      (build_recurrence candidate.sub_cs recurrences 
        candidate.inner_sym candidate.outer_sym 
        candidate.inequation blk_transform sub_dim_to_rec_num)::add_entries in
    let add_entries = 
      List.fold_left 
        foreach_candidate_build [] candidate_block in 
    let blk_add = Array.of_list (List.rev add_entries) in (* REV entries to match term_of_id *) 
    logf ~level:`trace "  Registering add block of size: %d" (Array.length blk_add);
    register_recurrence blk_transform blk_add recurrences in 
  let recurrences = 
    if not allow_interdependence then 
      (* Each candidate is a separate block *)
      List.fold_left 
        (fun r c -> foreach_block_build r [c]) 
        recurrences !recurrence_candidates
    else 
      (* The list of all candidates forms a recurrence block *)
      foreach_block_build recurrences !recurrence_candidates in
  recurrences

let is_negative q = ((QQ.compare q QQ.zero) < 0) 
let is_non_negative q = ((QQ.compare q QQ.zero) >= 0)
(*let is_at_least_one q = ((QQ.compare q QQ.one) >= 0)*)
let have_recurrence sym recurrences = 
  Srk.Syntax.Symbol.Map.mem sym recurrences.done_symbols

(* This function is really the heart of recurrence extraction *)
(* This function is applied to each B_in symbol *) 
let extract_recurrence_for_symbol 
    target_inner_sym b_in_b_out_map wedge_map recurrences 
    recurrence_candidates allow_interdependence allow_decrease = 
  (*logf ~level:`info "  Attempting extraction for %t DELETEME.@." 
    (fun f -> Srk.Syntax.pp_symbol Cra.srk f target_inner_sym);*)
  (* First, check whether we've already extracted a recurrence for this symbol *)
  if have_recurrence target_inner_sym recurrences then () else 
  if not (Srk.Syntax.Symbol.Map.mem target_inner_sym b_in_b_out_map) then () else 
  if not (Srk.Syntax.Symbol.Map.mem target_inner_sym wedge_map) then () else 
  let target_outer_sym = Srk.Syntax.Symbol.Map.find target_inner_sym b_in_b_out_map in
  let sub_wedge = Srk.Syntax.Symbol.Map.find target_inner_sym wedge_map in 
  (* TODO: I should start from the coordinate system, and map its dimensions to the symbols
   *         that I'm interested, rather than going in this direction, starting from the 
   *         symbols that I know about.  *)
  let sub_cs = Wedge.coordinate_system sub_wedge in
  if not (CoordinateSystem.admits sub_cs (Srk.Syntax.mk_const Cra.srk target_inner_sym)) then () else
  if not (CoordinateSystem.admits sub_cs (Srk.Syntax.mk_const Cra.srk target_outer_sym)) then () else
  begin
  (*let target_inner_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_inner_sym, [])) in*)
  let target_outer_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_outer_sym, [])) in 
  (* *) 
  let rec check_polynomial coeff dim = 
    (*Format.printf "****CHKP check_polynomial saw a coefficient %a @."
      (fun f -> Srk.QQ.pp f) coeff;*)
    if is_negative coeff then (false,[]) else
    match CoordinateSystem.destruct_coordinate sub_cs dim with 
    | `App (sym,_) -> 
            ((*Format.printf "****CHKP check_polynomial saw a symbol@.";*)
             (*(is_an_inner_symbol sym b_in_b_out_map, [sym])*)
             (have_recurrence sym recurrences, [sym]))
    | `Mul (x,y) -> 
            ((*Format.printf "****CHKP check_polynomial saw a `Mul@.";*)
             let x_result, x_deps = check_vector_dims x in 
             let y_result, y_deps = check_vector_dims y in
             (x_result && y_result, x_deps @ y_deps))
    | _ -> (false,[])
  and check_vector_dims inner_vector = 
    BatEnum.fold 
      (fun (running,deps) (coeff,dim) -> 
          let new_result, new_deps = check_polynomial coeff dim in
          (running && new_result, deps @ new_deps))
      (true,[])
      (Srk.Linear.QQVector.enum inner_vector)
    in
  (* *) 
  (* This function is applied to each inequation in sub_wedge *)
  let process_inequation vec negate = 
    (* *) 
    (* This function is applied to each (coeff,dim) pair in an inequation *)
    let process_coeff_dim_pair coeff dim =
      begin
      if dim == CoordinateSystem.const_id then (* ----------- CONSTANT *)
        (if is_non_negative coeff || allow_decrease
          then UseConstantTerm (coeff,dim)
          else DropTerm)          
      else match CoordinateSystem.destruct_coordinate sub_cs dim with 
      | `App (sym,_) -> 
        if sym == target_outer_sym then (* -------------- TARGET B_OUT *)
          (if is_negative coeff   (* Need upper bound on target symbol *)
            then UseSelfOuterTerm (coeff,dim)
            else DropInequation)
        else if sym == target_inner_sym then (* ---------- TARGET B_IN *)
          (if is_negative coeff
            then (if allow_decrease then 
                  (logf ~level:`info "  Drop negative-term inequation";
                  DropInequation)
                  else
                  (logf ~level:`info "  Drop negative term";
                  DropTerm))
            else UseInnerTerm (coeff,dim))
        else if have_recurrence sym recurrences then  (* LOWER STRATUM *)
          (if is_negative coeff
            then (if allow_decrease then 
                  (logf ~level:`info "  Drop negative-term inequation";
                  DropInequation)
                  else
                  (logf ~level:`info "  Drop negative term";
                  DropTerm))
            else UseInnerTerm (coeff,dim))
        else if is_an_inner_symbol sym b_in_b_out_map then
          (* Possible interdependency between variables: we've found
             an inequation relating target_outer_sym, for which we don't
             have a recurrence yet, to sym, for which we also don't have
             a recurrence yet.  We'll need to verify later that these
             two variables are part of a strongly connected comoponent of
             mutual dependency. *)
          (if is_negative coeff
            then DropInequation
            else UseInnerTermWithDependency (coeff,dim,[sym]))
        else 
          DropInequation
        (* The remaining cases involve non-trivial terms over the target B_in *)
        (* We currently do not extract such recurrences *)
        (* In the future, we will change this to allow
            monomials and interdependencies *)
        (* The dual-height analysis will also have to do this differently *)
      | _ -> ((*Format.printf "****CHKP Entering check_polynomial@.";*)
             let new_result, new_deps = check_polynomial coeff dim in
             (*Format.printf "****CHKP Result was %b@." new_result;*)
             if new_result then UseInnerTermWithDependency (coeff,dim,new_deps)
             else DropInequation
             (*DropInequation*))
      end 
    in 
    let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
    let coeffs_and_dims = Srk.Linear.QQVector.enum vec in 
    let rec examine_coeffs_and_dims accum dep_accum has_outer has_inner = 
      match BatEnum.get coeffs_and_dims with (* Note: "get" consumes an element *)
      | None -> 
        if has_outer && has_inner then Some (accum, dep_accum) else None
      | Some (coeff,dim) -> 
        match process_coeff_dim_pair coeff dim with 
        | DropInequation -> None
        | DropTerm -> examine_coeffs_and_dims 
            accum dep_accum has_outer has_inner
        | UseConstantTerm(new_coeff,new_dim) -> examine_coeffs_and_dims 
            ((new_coeff,new_dim)::accum) dep_accum has_outer has_inner
        | UseSelfOuterTerm(new_coeff,new_dim) -> examine_coeffs_and_dims 
            ((new_coeff,new_dim)::accum) dep_accum true      has_inner
        | UseInnerTerm(new_coeff,new_dim) -> examine_coeffs_and_dims 
            ((new_coeff,new_dim)::accum) dep_accum has_outer true
        | UseInnerTermWithDependency(new_coeff,new_dim,dep_dims) -> 
          (if allow_interdependence
          then examine_coeffs_and_dims 
            ((new_coeff,new_dim)::accum) (dep_dims @ dep_accum) has_outer true
          else None)
          (* Set this to None to turn off interdependency extraction *)
        in 
    match examine_coeffs_and_dims [] [] false false with 
    | None -> ()
    | Some (new_coeffs_and_dims, dep_accum) -> 
      (
      logf ~level:`trace "  Found a possible inequation";
      (*
      let target_outer_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_outer_sym, [])) in 
      let target_inner_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_inner_sym, [])) in 
      *)

      (*let sub_dim_to_rec_num = build_sub_dim_to_rec_num_map recurrences sub_cs in*)
      let term = CoordinateSystem.term_of_vec sub_cs vec in 
      (* *)
      let new_vec = Linear.QQVector.of_list new_coeffs_and_dims in
      (*let second_copy_vec = Linear.QQVector.of_list new_coeffs_and_dims in*)
      (*let outer_coeff = Linear.QQVector.coeff target_outer_dim new_vec in 
      let negated_outer_coeff = QQ.negate outer_coeff in *)
      let positive_outer_coeff = 
          QQ.negate (Linear.QQVector.coeff target_outer_dim new_vec) in 
      (* Drop any inequations that don't even mention the target B_out *)
      if (QQ.equal positive_outer_coeff QQ.zero)
         || 
         ((QQ.compare positive_outer_coeff QQ.zero) < 0) then () else 
      begin 
      (* We've identified a recurrence; now we'll put together the data 
        structures we'll need to solve it.  *)
      (let lev = if !chora_debug_recs then `always else `info in
      logf ~level:lev "  [PRE-REC] %a" (Srk.Syntax.Term.pp Cra.srk) term);
      logf ~level:`trace "    before filter: %a" Linear.QQVector.pp vec;
      let one_over_outer_coeff = QQ.inverse positive_outer_coeff in
      let new_vec = Linear.QQVector.scalar_mul one_over_outer_coeff new_vec in 
      logf ~level:`trace "    *after filter: %a" Linear.QQVector.pp new_vec;
      (*let inner_coeff = Linear.QQVector.coeff target_inner_dim new_vec in*)
      (*logf ~level:`trace "      inner_coeff: %a" QQ.pp inner_coeff;*)
      let normalized_coeffs_and_dims =
          BatList.of_enum (Srk.Linear.QQVector.enum new_vec) in
      (*let debug_vec = Linear.QQVector.of_list normalized_coeffs_and_dims in*)
      (*logf ~level:`trace "    **after cycle: %a" Linear.QQVector.pp debug_vec;
      logf ~level:`trace "      **scv cycle: %a" Linear.QQVector.pp second_copy_vec;*)
      recurrence_candidates := {outer_sym=target_outer_sym;
                                inner_sym=target_inner_sym;
                                (*coeff=inner_coeff;*)
                                sub_cs=sub_cs;
                                inequation=normalized_coeffs_and_dims;
                                (*inequation=new_coeffs_and_dims;*)
                                dependencies=dep_accum} :: 
                                (!recurrence_candidates)
      end
      )
    in
  let process_constraint = function 
    | (`Eq, vec) ->  process_inequation vec true; process_inequation vec false
    | (`Geq, vec) -> process_inequation vec false in 
  List.iter process_constraint (Wedge.polyhedron sub_wedge) 
  end 

(* Called once per outer bounding symbol *)
let make_outer_bounding_symbol
    (local_b_out_definitions, b_in_b_out_map, b_out_symbols) 
    (inner_sym, term) =
  let outer_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"B_out" `TyInt in
  let lhs = Srk.Syntax.mk_const Cra.srk outer_sym in 
  let rhs = term in 
  let b_out_constraint = 
    (* Drop any b_outs associated with terms that we don't know to be ints *)
    if Srk.Syntax.term_typ Cra.srk term = `TyInt then
      ((let lev = if !chora_debug_recs then `always else `info in
        logf ~level:lev "  [TERM]: %a  @@{h}:  %t  @@{h+1}:  %t " 
        (Srk.Syntax.Term.pp Cra.srk) term
        (fun f -> Srk.Syntax.pp_symbol Cra.srk f inner_sym)
        (fun f -> Srk.Syntax.pp_symbol Cra.srk f outer_sym));
        (* B_out <= term *)
        Srk.Syntax.mk_leq Cra.srk lhs rhs)
    else (let lev = if !chora_debug_recs then `always else `info in 
        logf ~level:lev "  Note: dropped a real term ";
        (* B_out = ? *)
        Srk.Syntax.mk_true Cra.srk) in
  (*local_b_out_definitions := b_out_constraint :: (!local_b_out_definitions);
  b_in_b_out_map := Srk.Syntax.Symbol.Map.add inner_sym outer_sym !b_in_b_out_map;
  b_out_symbols := Srk.Syntax.Symbol.Set.add outer_sym (!b_out_symbols) in*)
  (b_out_constraint :: local_b_out_definitions,
   Srk.Syntax.Symbol.Map.add inner_sym outer_sym b_in_b_out_map,
   Srk.Syntax.Symbol.Set.add outer_sym b_out_symbols)

(* Called once per proc *)
let make_outer_bounding_symbols_for_proc 
    recursive_weight_nobc bounds b_in_b_out_map b_out_symbols =
  (* REMOVE BASE CASE semantically using the "recursion_flag" *)
  (*let initially_no_recursion = (assign_value_to_literal bounds.recursion_flag 0) in 
  let eventually_recursion = (assume_value_eq_literal bounds.recursion_flag 1) in 
  let recursive_weight_nobc = 
    K.mul (K.mul initially_no_recursion recursive_weight) eventually_recursion in*)
  let (tr_symbols, body) = to_transition_formula recursive_weight_nobc in
  logf ~level:`trace "  rec_case_formula_body: @.%a@." (Srk.Syntax.Formula.pp Cra.srk) body;
  (* *)
  logf ~level:`info "[Chora] Listing bounded terms:";
  let (local_b_out_definitions, b_in_b_out_map, b_out_symbols) =
    List.fold_left 
      make_outer_bounding_symbol
      ([], b_in_b_out_map, b_out_symbols)
      bounds.bound_pairs in
  logf ~level:`trace "        Finished with bounded terms.";
  let lev = if !chora_debug_recs then `always else `info in
  logf ~level:lev "  ";
  (local_b_out_definitions, b_in_b_out_map, b_out_symbols, body)

(* Called once per SCC *)
let make_outer_bounding_symbols (scc:BURG.scc) rec_weight_map bounds_map =
  let b_in_b_out_map = Srk.Syntax.Symbol.Map.empty in 
  let b_out_symbols = Srk.Syntax.Symbol.Set.empty in
  let b_out_definitions_map = IntPairMap.empty in 
  let body_map = IntPairMap.empty in 
  List.fold_left 
    (fun 
      (b_out_definitions_map, b_in_b_out_map, b_out_symbols, body_map)
      (p_entry,p_exit,pathexpr) ->
      let rec_weight_nobc = IntPairMap.find (p_entry,p_exit) rec_weight_map in 
      let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
      let local_b_out_definitions, b_in_b_out_map, b_out_symbols, body = 
        make_outer_bounding_symbols_for_proc 
          rec_weight_nobc bounds b_in_b_out_map b_out_symbols in
      let b_out_definitions_map = 
          IntPairMap.add (p_entry, p_exit) local_b_out_definitions 
            b_out_definitions_map in
      let body_map = 
        IntPairMap.add (p_entry, p_exit) body body_map in 
      (b_out_definitions_map, b_in_b_out_map, b_out_symbols, body_map))
    (b_out_definitions_map, b_in_b_out_map, b_out_symbols, body_map)
    scc.procs

(* Called once per procedure per value of allow_decrease *)
let make_extraction_formula 
    (*recursive_weight_nobc*) bounds local_b_out_definitions b_in_b_out_map 
    b_out_symbols body ~allow_decrease =
  (* *)
  (* ----- These lines assume every b_in is non-negative. ----- *)
  (* They are only used, and only sound, when allow_decrease is false. *)
  let b_in_conjunction = 
    if allow_decrease
    then []
    else begin
         let non_negative_b_in (inner_sym, _) = 
         let lhs = Srk.Syntax.mk_real Cra.srk QQ.zero in 
         let rhs = Srk.Syntax.mk_const Cra.srk inner_sym in 
         Srk.Syntax.mk_leq Cra.srk lhs rhs in
         (* *)
         let all_b_in_non_negative = 
           List.map non_negative_b_in bounds.bound_pairs in 
         [Srk.Syntax.mk_and Cra.srk all_b_in_non_negative] 
    end in 
  (* ---------------------------------------------------------- *)
  (* *)
  let b_out_conjunction = Srk.Syntax.mk_and Cra.srk local_b_out_definitions in 
  (*logf ~level:`info "  b_out_conjunction: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) b_out_conjunction;*)
  let conjuncts = b_in_conjunction @ [body; b_out_conjunction] in
  let extraction_formula = Srk.Syntax.mk_and Cra.srk conjuncts in 
  logf ~level:`trace "  extraction_formula: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) extraction_formula;
  extraction_formula (* formerly had a tuple of return values *)

(* Option 1 *)
(* Old version: put everything through a single wedge first *)
(* Called once per procedure (per value of allow_decrease) *)
(*
let make_extraction_wedges_from_one_wedge
    extraction_formula bounds b_in_b_out_map b_out_symbols wedge_map = 
  (* NOTE: bounding symbols need to have been analyzed for all procedures in the SCC by this point *)
  let projection sym = 
    is_an_inner_symbol sym b_in_b_out_map || 
    Srk.Syntax.Symbol.Set.mem sym b_out_symbols in 
  let wedge = Wedge.abstract ~exists:projection ~subterm:projection Cra.srk extraction_formula in 
  (* Wedge.strengthen wedge; (* NOTE: Added just for debugging... *) *)
  logf ~level:`info "  extraction_wedge = @.%t@." (fun f -> Wedge.pp f wedge); 
  (* For each outer bounding symbol (B_out), project the wedge down to that outer
       symbol and all inner bounding symbols *)
  logf ~level:`trace "  Building a wedge map..."; 
  let add_wedge_to_map map (target_inner_sym, _) = 
    let target_outer_sym = Srk.Syntax.Symbol.Map.find target_inner_sym b_in_b_out_map in
    let targeted_projection sym = 
      sym == target_outer_sym || 
      is_an_inner_symbol sym b_in_b_out_map in 
    (* Project this wedge down to a sub_wedge that uses only this B_out and some B_ins *)
    let sub_wedge = Wedge.exists ~subterm:targeted_projection targeted_projection wedge in 
    (logf ~level:`trace "  sub_wedge_for[%t] = @.%t@." 
      (fun f -> Srk.Syntax.pp_symbol Cra.srk f target_outer_sym)
      (fun f -> Wedge.pp f sub_wedge);
    Srk.Syntax.Symbol.Map.add target_inner_sym sub_wedge map) in 
  let updated_wedge_map = 
    List.fold_left 
      add_wedge_to_map 
      wedge_map
      bounds.bound_pairs in 
  logf ~level:`trace "  Finished wedge map.";
  updated_wedge_map
*)

(* Option 2 *)
(* New version: make each new wedge from the original formula *)
(* Called once per procedure (per value of allow_decrease) *)
let make_extraction_wedges_from_formula
    extraction_formula bounds b_in_b_out_map b_out_symbols wedge_map = 
  (* NOTE: bounding symbols need to have been analyzed for all procedures in the SCC by this point *)
  logf ~level:`info "   Not using extraction_wedge; using formula instead"; 
  (* For each outer bounding symbol (B_out), project the wedge down to that outer
       symbol and all inner bounding symbols *)
  logf ~level:`trace "  Building a wedge map..."; 
  let add_wedge_to_map map (target_inner_sym, _) = 
    let target_outer_sym = Srk.Syntax.Symbol.Map.find target_inner_sym b_in_b_out_map in
    let targeted_projection sym = 
      sym == target_outer_sym || 
      is_an_inner_symbol sym b_in_b_out_map in 
    (* Project this wedge down to a sub_wedge that uses only this B_out and some B_ins *)
    let sub_wedge = Wedge.abstract ~exists:targeted_projection ~subterm:targeted_projection 
                      Cra.srk extraction_formula in 
    (*Wedge.strengthen sub_wedge; (* NOTE: Added just for debugging... *) *)
    (logf ~level:`trace "  sub_wedge_for[%t] = @.%t@." 
      (fun f -> Srk.Syntax.pp_symbol Cra.srk f target_outer_sym)
      (fun f -> Wedge.pp f sub_wedge);
    Srk.Syntax.Symbol.Map.add target_inner_sym sub_wedge map) in 
  let updated_wedge_map = 
    List.fold_left 
      add_wedge_to_map 
      wedge_map
      bounds.bound_pairs in 
  logf ~level:`trace "  Finished wedge map.";
  updated_wedge_map

let extract_and_solve_recurrences 
    b_in_b_out_map wedge_map post_height_sym ~allow_decrease = 
  (* *********************************************************************** *)
  (* ********               Recurrence Extraction                   ******** *)
  let recurrence_candidates = ref [] in
  (* This function is applied twice for each stratification level:
      first looking for non-interdependent variables and
      a second time allowing for interdependent variables *)
  let rec extract_recurrences recurrences allow_interdependence = 
    begin
    let nb_previous_recurrences = count_recurrences recurrences in 
    logf ~level:`trace "[Chora] Recurrence extraction:";
    (*List.iter (fun (inner_sym, _) -> *) (* ... *) (*bounds.bound_pairs;*)
    Srk.Syntax.Symbol.Map.iter
      (fun inner_sym _ -> 
          extract_recurrence_for_symbol (* This is the heart of recurrence extraction *)
            inner_sym b_in_b_out_map wedge_map recurrences 
            recurrence_candidates allow_interdependence allow_decrease)
      b_in_b_out_map;
    logf ~level:`trace "        Finished recurrence extraction";
         
    (*logf ~level:`info "  N candidates before filter: %d@." (List.length !recurrence_candidates);*)
    filter_candidates recurrence_candidates recurrences; 
    (*logf ~level:`info "  N candidates after filter:  %d@." (List.length !recurrence_candidates);*)
    
    let recurrences = accept_and_build_recurrences 
      recurrence_candidates recurrences allow_interdependence in
    logf ~level:`trace "  [ -- end of stratum -- ]";
    (* Did we get new recurrences? If so, then look for a higher stratum. *)
    if count_recurrences recurrences > nb_previous_recurrences then 
      extract_recurrences recurrences false
    else if not allow_interdependence then
      extract_recurrences recurrences true
    else recurrences 
    end 
    in 
  let recurrences = empty_recurrence_collection () in 
  let recurrences = extract_recurrences recurrences false in 
  (* *)
  (* *********************************************************************** *)
  (* ********               Recurrence Solving                      ******** *)
  (* *)
  let term_of_id = BatDynArray.to_array recurrences.term_of_id in 
  sanity_check_recurrences recurrences term_of_id;
  (* TODO: Change my interface to use pairs of transform_add blocks *)
  (* Send the matrix recurrence to OCRS and obtain a solution *)
  logf ~level:`trace "@.    Sending to OCRS ";
  let loop_counter = Srk.Syntax.mk_const Cra.srk post_height_sym in
  let nb_constants = 0 in
  let solution = SolvablePolynomial.exp_ocrs_external 
                  Cra.srk recurrences.ineq_tr loop_counter term_of_id 
                  nb_constants recurrences.blk_transforms 
                  recurrences.blk_adds in 
  logf ~level:`info "@.    solution: %a" 
      (Srk.Syntax.Formula.pp Cra.srk) solution;
  (* *)
  solution

(* Called once per SCC per value of allow_decrease *)
let build_wedge_map 
      b_out_definitions_map b_in_b_out_map b_out_symbols (*rec_weight_map*) bounds_map 
      program_vars top_down_formula_map (scc:BURG.scc) body_map ~allow_decrease =
  (* For each procedure, create a transition formula for use in extraction *)
  let extraction_formula_map = 
    List.fold_left 
      (fun extraction_formula_map
        (p_entry,p_exit,pathexpr) ->
      (*let rec_weight_nobc = IntPairMap.find (p_entry,p_exit) rec_weight_map in*)
      let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
      let body = IntPairMap.find (p_entry,p_exit) body_map in 
      let local_b_out_definitions = 
        IntPairMap.find (p_entry,p_exit) b_out_definitions_map in 
      let extraction_formula = 
        make_extraction_formula 
          (*rec_weight_nobc*) bounds local_b_out_definitions
          b_in_b_out_map b_out_symbols body ~allow_decrease in
      IntPairMap.add (p_entry,p_exit) extraction_formula extraction_formula_map)
    IntPairMap.empty
    scc.procs in 
  (* For each procedure, create a wedge for use in extraction *)
  let wedge_map = 
    List.fold_left (fun wedge_map (p_entry,p_exit,pathexpr) ->
      let extraction_formula = 
          IntPairMap.find (p_entry,p_exit) extraction_formula_map in 
      let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
      make_extraction_wedges_from_formula
        extraction_formula bounds b_in_b_out_map b_out_symbols wedge_map)
    Srk.Syntax.Symbol.Map.empty
    scc.procs in 
  wedge_map

(* Called once per SCC per value of allow_decrease *)
let build_wedges_and_extract_recurrences 
      b_out_definitions_map b_in_b_out_map b_out_symbols 
      (*rec_weight_map*) bounds_map program_vars top_down_formula_map 
      scc post_height_sym body_map ~allow_decrease =
  let wedge_map = build_wedge_map
    b_out_definitions_map b_in_b_out_map b_out_symbols 
    (*rec_weight_map*) bounds_map program_vars top_down_formula_map 
    scc body_map ~allow_decrease in
  extract_and_solve_recurrences 
    b_in_b_out_map wedge_map post_height_sym ~allow_decrease
  (* returns solution *)

let make_height_based_summaries
      rec_weight_map bounds_map program_vars top_down_formula_map 
      (scc:BURG.scc) height_model =
  (* *)
  let (b_out_definitions_map, b_in_b_out_map, b_out_symbols, body_map) = 
    make_outer_bounding_symbols scc rec_weight_map bounds_map in 
  match height_model with 
  (* *********************************************************************** *)
  (* ********                Height-based Analysis                  ******** *)
  | RB rb -> 
    (* ---------- Extract and solve recurrences --------- *)
    let solution = build_wedges_and_extract_recurrences 
      b_out_definitions_map b_in_b_out_map b_out_symbols 
      (*rec_weight_map*) bounds_map program_vars top_down_formula_map 
      scc (post_symbol rb.symbol) body_map ~allow_decrease:!chora_just_allow_decrease in
    (* ---------- Build summaries using recurrence solution --------- *)
    let summary_list = 
      List.fold_left (fun sums (p_entry,p_exit,pathexpr) ->
        let top_down_formula = 
            IntPairMap.find (p_entry,p_exit) top_down_formula_map in 
        let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
        let summary = build_height_based_summary 
          solution b_in_b_out_map bounds top_down_formula program_vars p_entry p_exit in
        (p_entry,p_exit,summary)::sums)
      []
      scc.procs in 
    summary_list
  (* *********************************************************************** *)
  (* ********                 Dual-height Analysis                  ******** *)
  | RB_RM_MB (rb, rm, mb) -> 
    begin 
    (* ---------- Extract and solve recurrences --------- *)
    let rm_solution = build_wedges_and_extract_recurrences 
      b_out_definitions_map b_in_b_out_map b_out_symbols 
      (*rec_weight_map*) bounds_map program_vars top_down_formula_map 
      scc (post_symbol rm.symbol) body_map ~allow_decrease:true in
    (* *)
    let mb_solution = build_wedges_and_extract_recurrences 
      b_out_definitions_map b_in_b_out_map b_out_symbols 
      (*rec_weight_map*) bounds_map program_vars top_down_formula_map 
      scc (post_symbol mb.symbol) body_map ~allow_decrease:false in
    (* ---------- Build summaries using recurrence solution --------- *)
    let excepting = List.fold_left (fun excepting v -> 
        let sym = Cra.V.symbol_of v in 
        let excepting = Srk.Syntax.Symbol.Set.add sym excepting in 
        Srk.Syntax.Symbol.Set.add (post_symbol sym) excepting)
      Srk.Syntax.Symbol.Set.empty
      (rb.value::rm.value::mb.value::program_vars) in 
    let summary_list = 
      List.fold_left (fun sums (p_entry,p_exit,pathexpr) ->
        let top_down_formula = 
            IntPairMap.find (p_entry,p_exit) top_down_formula_map in 
        let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
        let summary = build_dual_height_summary
          rb rm mb rm_solution mb_solution b_in_b_out_map bounds 
          top_down_formula excepting program_vars p_entry p_exit 
          height_model in
        (p_entry,p_exit,summary)::sums)
      []
      scc.procs in 
    summary_list
    end
;;

let top_down_formula_to_wedge top_down_formula sym = 
  let projection x =
    x = sym ||
    match Cra.V.of_symbol x with
    | Some v -> Core.Var.is_global (Cra.var_of_value v)
    | None -> false
  in
  let wedge = Wedge.abstract ~exists:projection Cra.srk top_down_formula in
  let level = if !chora_debug_squeeze then `always else `info in
  logf ~level " incorporating squeezed depth formula: %t" 
    (fun f -> Wedge.pp f wedge);
  Wedge.to_formula wedge
  (*let wedge_as_formula = Wedge.to_formula wedge in 
  Srk.Syntax.mk_and Cra.srk [top_down_formula; wedge_as_formula]*)

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
  let symbol_term = Syntax.mk_const Cra.srk sym in
  let debug_list part = 
     logf ~level "      -- inner bound list [";
     List.iter (fun elt -> logf ~level "       %a" (Syntax.Term.pp Cra.srk) elt) part;
     logf ~level "      -- inner bound list ]"
  in
  let debug_list_list parts = 
     logf ~level "   -- outer bound list [";
     List.iter (fun part -> debug_list part) parts;
     logf ~level "   -- outer bound list ]"
  in
  let safer_disjoin parts = 
    match parts with 
    | [] -> Syntax.mk_true Cra.srk
    | _ -> Syntax.mk_or Cra.srk parts
  in
  let to_formula parts = 
    let (lower,upper) = parts in
    (*| None -> Syntax.mk_false Cra.srk
      | Some (lower, upper) ->*)
    logf ~level " lower bounds: ";
    debug_list_list lower;
    logf ~level " upper bounds: ";
    debug_list_list upper;
    let lower_bounds =
      lower
      |> List.map (fun case ->
          case |> List.map (fun lower_bound -> Syntax.mk_leq Cra.srk lower_bound symbol_term)
          |> Syntax.mk_and Cra.srk)
      |> safer_disjoin
    in
    let upper_bounds =
      upper
      |> List.map (fun case ->
          case |> List.map (fun upper_bound -> Syntax.mk_leq Cra.srk symbol_term upper_bound)
          |> Syntax.mk_and Cra.srk)
      |> safer_disjoin
    in
    Syntax.mk_and Cra.srk [lower_bounds; upper_bounds]
  in
  logf ~level " sbf-squeeze input: %a " (Syntax.Formula.pp Cra.srk) phi;
  let formula_parts_wrapped = 
      Wedge.symbolic_bounds_formula_list ~exists Cra.srk phi sym in
  match formula_parts_wrapped with
  | `Sat (formula_parts) -> 
      let formula = to_formula formula_parts in 
      logf ~level " sbf-squeeze output: %a " (Syntax.Formula.pp Cra.srk) formula;
      formula
  | `Unsat ->
      logf ~level:`always " WARNING: sbf-squeeze got unsatisfiable depth formula!";
      Syntax.mk_true Cra.srk

  (* OLD CODE *)
  (*
  match Wedge.symbolic_bounds_formula ~exists Cra.srk phi sym with
  | `Sat (lower, upper) ->
    let lower_bound_formula = 
      begin match lower with
        | Some lower ->
          logf ~level " squeeze: %a <= height" (Syntax.pp_expr_unnumbered Cra.srk) lower;
          Syntax.mk_leq Cra.srk lower (Syntax.mk_const Cra.srk sym)
        | None -> 
          logf ~level " squeeze: no lower bound on height";
          Syntax.mk_true Cra.srk
      end
    in
    let upper_bound_formula =
      begin match upper with
        | Some upper ->
          logf ~level " squeeze: height <= %a" (Syntax.pp_expr_unnumbered Cra.srk) upper;
          Syntax.mk_leq Cra.srk (Syntax.mk_const Cra.srk sym) upper
        | None ->
          logf ~level " squeeze: no upper bound on height";
          Syntax.mk_true Cra.srk
      end
    in
    Syntax.mk_and Cra.srk [lower_bound_formula; upper_bound_formula]
  | `Unsat ->
    logf ~level:`always " squeeze: phi_td is infeasible";
    Syntax.mk_true Cra.srk
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
      let base_case_weight = IntPairMap.find (p_entry,p_exit) base_case_map in 
      let weight = K.mul base_case_weight top in
      top_graph := Srk.WeightedGraph.add_edge !top_graph p_entry (Weight weight) !dummy_exit_node)
    procs;
  let td_formula_map = (List.fold_left (fun td_formula_map (p_entry,p_exit,pathexpr) ->
      match WeightedGraph.path_weight !top_graph p_entry !dummy_exit_node with
      | Weight cycles ->
        let td_summary = K.mul set_height_zero cycles in
        let td_summary = K.mul td_summary assume_height_non_negative in
        let td_summary = project td_summary in (* FIXME Not sure this is needed *)
        logf ~level:`info "  multi_phi_td%t = [" (proc_name_triple p_entry p_exit);
        print_indented 15 td_summary; logf ~level:`info "  ]\n";
        (*(if !chora_print_depth_bound_wedges then
        begin
          logf ~level:`always "  wedge[phi_td%t] is [" (proc_name_triple p_entry p_exit);
          debug_print_depth_wedge td_summary;
          logf ~level:`always "  ]";
        end);*)
        let _, top_down_formula = to_transition_formula td_summary in
        logf ~level:`info "@.  tdf%t: %a" (proc_name_triple p_entry p_exit)
            (Srk.Syntax.Formula.pp Cra.srk) top_down_formula;
        let post_height_sym = post_symbol height.symbol in
        let post_height_gt_zero = Syntax.mk_lt Cra.srk 
          (Syntax.mk_zero Cra.srk)
          (Syntax.mk_const Cra.srk post_height_sym) in
        let post_height_eq_zero = Syntax.mk_eq Cra.srk 
          (Syntax.mk_zero Cra.srk)
          (Syntax.mk_const Cra.srk post_height_sym) in
        let base_case_weight = IntPairMap.find (p_entry,p_exit) base_case_map in 
        (*let _, base_case_formula = to_transition_formula base_case_weight in*)
        let _, base_case_formula = 
          to_transition_formula_with_unmodified base_case_weight scc_global_footprint in 
        (*let to_be_squeezed = top_down_formula in (* naive version *) *)
        let to_be_squeezed = 
          (* sophisticated version: assume H' >= 0 inside squeezed version *) 
          Syntax.mk_and Cra.srk [post_height_gt_zero; top_down_formula] in
        let symbolic_bounds_top_down_formula = 
          if !chora_squeeze_sb || !chora_debug_squeeze
          then top_down_formula_to_symbolic_bounds to_be_squeezed post_height_sym
          else Syntax.mk_true Cra.srk in
        let wedge_top_down_formula = 
          if !chora_squeeze_wedge || !chora_debug_squeeze
          then top_down_formula_to_wedge to_be_squeezed post_height_sym
          else Syntax.mk_true Cra.srk in
        (*let incorporate_tdf fmla = 
          Syntax.mk_and Cra.srk [fmla; top_down_formula] in*)
        let incorporate_tdf fmla = 
            begin
              let case_split = 
                  Syntax.mk_or Cra.srk 
                    [(Syntax.mk_and Cra.srk [post_height_eq_zero; base_case_formula]);
                     (Syntax.mk_and Cra.srk [post_height_gt_zero; fmla])] in
              if !chora_squeeze_conjoin
              then Syntax.mk_and Cra.srk [top_down_formula; case_split]
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
        IntPairMap.add (p_entry,p_exit) final_top_down_formula td_formula_map
      | _ -> failwith "A call was found in td_summary")
    IntPairMap.empty procs) in
  td_formula_map;;

(*
let make_top_down_weight_oneproc p_entry path_weight_internal top scc_call_edges = 
  let height_var_sym_pair = make_variable "H" in
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
      (Srk.Syntax.Formula.pp Cra.srk) top_down_formula;
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
                Syntax.substitute_const Cra.srk subst (K.get_transform cost summary)
              in
              Ctx.mk_and [Syntax.substitute_const Cra.srk subst (K.guard summary);
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
              Syntax.substitute_const Cra.srk (fun sym ->
                  if sym = cost_symbol then
                    Ctx.mk_real QQ.zero
                  else
                    Ctx.mk_const sym)
            in
            match Wedge.symbolic_bounds_formula ~exists Cra.srk guard cost_symbol with
            | `Sat (lower, upper) ->
              begin match lower with
                | Some lower ->
                  let lower = Syntax.substitute_map Cra.srk param_map lower in
                  logf ~level:`always " %a <= cost" (Syntax.pp_expr_unnumbered Cra.srk) lower;
                  logf ~level:`always " %a is o(%a)"
                    Varinfo.pp procedure
                    BigO.pp (BigO.of_term Cra.srk (pre_cost_zero lower))
                | None -> ()
              end;
              begin match upper with
                | Some upper ->
                  let upper = Syntax.substitute_map Cra.srk param_map upper in
                  logf ~level:`always " cost <= %a" (Syntax.pp_expr_unnumbered Cra.srk) upper;
                  logf ~level:`always " %a is O(%a)"
                  Varinfo.pp procedure
                  BigO.pp (BigO.of_term Cra.srk (pre_cost_zero upper))
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
          |> SrkSimplify.simplify_terms Cra.srk
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
      let psi = Wedge.cover Cra.srk projection body in 
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
            (logf ~level:`info "  Proc%t = %t" (proc_name_triple u v) (fun f -> NPathexpr.pp f p))) scc.procs;
        let split_expr_map = List.fold_left (fun se_map (p_entry,p_exit,pathexpr) ->
            let edge s t = NPathexpr.mk_edge context s t in
            let pe_algebra = BURG.pathexp_algebra context in 
            let (rec_pe,nonrec_pe) = factor_pair pathexpr is_scc_call edge pe_algebra in
            (*let (rec_pe, nonrec_pe) = factor_pair pathexpr is_within_scc edge pe_algebra in*)
            logf ~level:`info "    Rec part: %t" (fun f -> NPathexpr.pp f rec_pe);
            logf ~level:`info "    Nonrec part: %t" (fun f -> NPathexpr.pp f nonrec_pe);
            IntPairMap.add (p_entry,p_exit) (rec_pe,nonrec_pe) se_map)
          IntPairMap.empty 
          scc.procs in 

        (*   ***   Compute the weights of the base case of each procedure  ***   *)
        let base_case_map = List.fold_left (fun bc_map (p_entry,p_exit,pathexpr) ->
            let (rec_pe,nonrec_pe) = IntPairMap.find (p_entry,p_exit) split_expr_map in
            (*let base_case_weight = project (path_weight_internal p_entry p_exit weight_of_call_zero) in*)
            let base_case_weight = project (NPathexpr.eval (edge_weight_with_calls weight_of_call_zero) nonrec_pe) in
            logf ~level:`info "  base_case%t = [" (proc_name_triple p_entry p_exit); 
              print_indented 15 base_case_weight; logf ~level:`info "  ]";
            IntPairMap.add (p_entry,p_exit) base_case_weight bc_map)
          IntPairMap.empty 
          scc.procs in 

        let simple_height = make_variable (if !chora_dual then "RB" else "H") in 
        let height_model = 
          if !chora_dual then 
            let rm = make_variable "RM" in 
            let mb = make_variable "MB" in 
            RB_RM_MB (simple_height (* that is, rb *), rm, mb)
          else 
            RB (simple_height) in 

        logf ~level:`info "  Beginning top-down analysis"; 
        (*   ***   Compute top-down summaries for each procedure   ***   *)
        let top_down_formula_map = 
          make_top_down_weight_multi scc.procs (*top*) ts is_scc_call lower_summaries 
            base_case_map simple_height 
            scc_local_footprint scc_global_footprint scc_footprint in
        logf ~level:`info "  Finished top-down analysis"; 

        (*   ***   Compute the abstraction that we will use for a call to each procedure  ***   *)
        let bounds_map = List.fold_left (fun b_map (p_entry,p_exit,pathexpr) ->
            let base_case_weight = IntPairMap.find (p_entry,p_exit) base_case_map in 
            (*let bounds = make_call_abstraction base_case_weight scc_global_footprint in *)
            let (tr_symbols, base_case_fmla) = 
                to_transition_formula_with_unmodified base_case_weight scc_global_footprint in
            let bounds = make_call_abstraction base_case_fmla tr_symbols in 
            IntPairMap.add (p_entry,p_exit) bounds b_map)
          IntPairMap.empty 
          scc.procs in 
        (* Construct the recursive-case weight using the formula computed by make_call_abstraction *)
        let call_abstraction_weight_map = IntPairMap.mapi
          (fun (p_entry,p_exit) info_structure ->
            let call_abstraction_weight = 
              of_transition_formula info_structure.tr_symbols info_structure.call_abstraction_fmla in
            logf ~level:`info "  call_abstration%t = [" (proc_name_triple p_entry p_exit); 
            print_indented 15 call_abstraction_weight; logf ~level:`info "  ]";
            call_abstraction_weight)
          bounds_map in
        (* Define a function for handling calls to each procedure in the SCC *)
        let weight_of_call_rec cs ct cen cex = 
          (*let callee_bounds = IntPairMap.find (cen,cex) bounds_map in
          callee_bounds.call_abstraction_weight in*)
          IntPairMap.find (cen,cex) call_abstraction_weight_map in

        (*   ***   Compute the recursive-case weight/formula for each procedure  ***   *)
        let rec_weight_map = List.fold_left (fun rw_map (p_entry,p_exit,pathexpr) ->
            (* WARNING: the following line isn't precise unless you take special action to
                 remove the base case later... *)
            (*let recursive_weight = path_weight_internal p_entry p_exit weight_of_call_rec in
            logf ~level:`info "  recursive_weight = [";
            print_indented 15 recursive_weight;
            logf ~level:`info "  ]";*)
            let (rec_pe,nonrec_pe) = IntPairMap.find (p_entry,p_exit) split_expr_map in
            let recursive_weight_nobc = project (NPathexpr.eval (edge_weight_with_calls weight_of_call_rec) rec_pe) in
            logf ~level:`info "  recursive_weight-BC%t = [" (proc_name_triple p_entry p_exit);
            print_indented 15 recursive_weight_nobc;
            logf ~level:`info "  ]"; 
            IntPairMap.add (p_entry,p_exit) recursive_weight_nobc rw_map)
          IntPairMap.empty 
          scc.procs in 

        let summary_list = 
          make_height_based_summaries
            rec_weight_map bounds_map program_vars top_down_formula_map scc height_model in 

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
    procedure_names_map := IntPairMap.add (entry,exit) name !procedure_names_map)

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

