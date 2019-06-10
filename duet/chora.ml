open Core
open Apak
open CfgIr
open Srk

module RG = Interproc.RG
module G = RG.G
(*module K = NewtonDomain.ICRASum*)
module K = Cra.K
module Ctx = NewtonDomain.Ctx

module Var = Cra.V

include Log.Make(struct let name = "chora" end)
module A = Interproc.MakePathExpr(Cra.K)

(*open Pathexpr*)

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

(* ugly: copied from newtonDomain just for debugging *)
let print_indented ?(level=`info) indent k =
      logf ~level:level "%s"
      (SrkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" K.pp tr;
          Format.pp_close_box formatter ()) k)

let post_symbol =
  Memo.memo (fun sym ->
    match Var.of_symbol sym with
    | Some var ->
      (*let newsym = Srk.Syntax.mk_symbol Cra.srk ~name:("postrec_" ^ Var.show var) (Var.typ var :> Srk.Syntax.typ) in*)
      let newsym = Srk.Syntax.mk_symbol Cra.srk ~name:(Var.show var ^ "'") (Var.typ var :> Srk.Syntax.typ) in
      (*logf ~level:`info "New Symbol Created!  old=%s  new=%s\n" 
        (Srk.Syntax.show_symbol Cra.srk sym)
        (Srk.Syntax.show_symbol Cra.srk newsym); *)
      newsym
    | None -> assert false)

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

type 'a bound_info = {
  bound_pairs : (Srk.Syntax.symbol * 'a Srk.Syntax.term) list;
  recursion_flag : Cra.value;
  call_abstraction : K.t
}

let assign_value_to_literal value literal = 
  K.assign value (Srk.Syntax.mk_real Cra.srk (Srk.QQ.of_int literal))

let assume_value_eq_literal value literal = 
  let var = Cra.V.symbol_of value in 
  K.assume (Srk.Syntax.mk_eq Cra.srk 
    (Srk.Syntax.mk_const Cra.srk var)
    (Srk.Syntax.mk_real Cra.srk (Srk.QQ.of_int literal)))

let increment_variable value = 
  K.assign
    value 
    (Srk.Syntax.mk_add 
      Cra.srk
      [(Srk.Syntax.mk_const Cra.srk (Cra.V.symbol_of value));
       (Srk.Syntax.mk_real Cra.srk (Srk.QQ.of_int 1))])

(* PASS REC FLAG IN FROM OUTSIDE *)
(* Make bound analysis? *)
let mk_call_abstraction base_case_weight = 
  let (tr_symbols, body) = to_transition_formula base_case_weight in
  (*logf ~level:`info "  transition_formula_body: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) body;*)
  let projection x = 
    (* FIXME: THIS IS QUICK AND DIRTY *)
    (* FIXME: remove this clause*)
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
    || 
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false (* false *)
  in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk body in 
  logf ~level:`info "\n  base_case_wedge = %t \n\n" (fun f -> Wedge.pp f wedge);
  let cs = Wedge.coordinate_system wedge in 
  let bounding_atoms = ref [] in
  let bound_list = ref [] in
  let add_bounding_var vec negate =
      let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
      let term = CoordinateSystem.term_of_vec cs vec in 
      (*logf ~level:`info "  base-case-bounded term: %a \n" (Srk.Syntax.Term.pp Cra.srk) term;*)
    let bounding_var = Core.Var.mk (Core.Varinfo.mk_global "B_in" ( Core.Concrete (Core.Int 32))) in 
    let bounding_var_sym = Cra.V.symbol_of (Cra.VVal bounding_var) in 
    (*let bounding_var_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"B_in" `TyInt in *)
    let bounding_term = Srk.Syntax.mk_const Cra.srk bounding_var_sym in 
    let bounding_atom = Srk.Syntax.mk_leq Cra.srk term bounding_term in 
    bounding_atoms := bounding_atom            :: (!bounding_atoms);
    bound_list     := (bounding_var_sym, term) :: (!bound_list) in
  let handle_constraint = function 
    | (`Eq, vec) ->
      (*logf ~level:`info "  rec equation: %a \n" Linear.QQVector.pp vec;*)
      add_bounding_var vec true; 
      add_bounding_var vec false
    | (`Geq, vec) ->
      add_bounding_var vec true in 
  List.iter handle_constraint (Wedge.polyhedron wedge);
  let rec_flag_var = Core.Var.mk (Core.Varinfo.mk_global "Recursion_Flag" ( Core.Concrete (Core.Int 32))) in 
  let rec_flag_val = Cra.VVal rec_flag_var in 
  let _ = Cra.V.symbol_of rec_flag_val in (* Add to symbol table... (HACK!) *)
  let set_rec_flag = assign_value_to_literal rec_flag_val 1 in 
  let call_abstraction_fmla = Srk.Syntax.mk_and Cra.srk (!bounding_atoms) in 
  let call_abstraction_weight = of_transition_formula tr_symbols call_abstraction_fmla in 
    {bound_pairs = !bound_list;
     recursion_flag = rec_flag_val;
     call_abstraction = K.mul set_rec_flag call_abstraction_weight}

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
  coeff: Srk.QQ.t;
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
  | DropTerm | DropInequation | UseTerm of Srk.QQ.t * int 
  | UseTermWithDependency of Srk.QQ.t * int * Srk.Syntax.symbol

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
      else (failwith "Unrecognized component of recurrence inequation"))
    const_add_poly
    new_coeffs_and_dims in 
  blk_add_entry;;

let is_an_inner_symbol sym b_in_b_out_map = 
  Srk.Syntax.Symbol.Map.mem sym b_in_b_out_map

let build_summary_from_solution 
    solution b_in_b_out_map bounds top_down_formula program_vars 
    p_entry p_exit = 
  let subst_b_in_with_zeros sym = 
    if is_an_inner_symbol sym b_in_b_out_map
    then Srk.Syntax.mk_real Cra.srk QQ.zero 
    else Srk.Syntax.mk_const Cra.srk sym in 
  let solution_starting_at_zero = 
    Srk.Syntax.substitute_const Cra.srk subst_b_in_with_zeros solution in 
  (* let simpler = SrkSimplify.simplify_terms Cra.srk with_zeros in *)
  logf ~level:`info "@.    simplified%t: %a" (proc_name_triple p_entry p_exit)
      (Srk.Syntax.Formula.pp Cra.srk) solution_starting_at_zero;
  let bounding_conjunction = 
    let make_bounding_conjuncts (in_sym,term) =
      let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in 
      (* let subst_post sym = Srk.Syntax.mk_const Cra.srk (post_symbol sym) in 
      let post_term = Srk.Syntax.substitute_const Cra.srk subst_post term in *)
      Srk.Syntax.mk_leq Cra.srk term (Srk.Syntax.mk_const Cra.srk out_sym)
    in
    let bounding_conjuncts = 
      List.map make_bounding_conjuncts bounds.bound_pairs in 
    Srk.Syntax.mk_and Cra.srk bounding_conjuncts in 
  logf ~level:`info "@.    bddg conj%t: %a" (proc_name_triple p_entry p_exit)
      (Srk.Syntax.Formula.pp Cra.srk) bounding_conjunction; 
  let big_conjunction = 
    Srk.Syntax.mk_and Cra.srk [top_down_formula; 
                               solution_starting_at_zero;
                               bounding_conjunction] in
  logf ~level:`info "@.    big conj%t: %a" (proc_name_triple p_entry p_exit)
      (Srk.Syntax.Formula.pp Cra.srk) big_conjunction; 
  (* FIXME: I should really be iterating over the SCC footprint variables,
            not over the list of all program variables. *)
  let final_tr_symbols = 
    List.map (fun var -> 
      let pre_sym = Cra.V.symbol_of var in 
      let post_sym = post_symbol pre_sym in 
      (pre_sym,post_sym) ) program_vars in 
  let height_based_summary = of_transition_formula final_tr_symbols big_conjunction in 
  logf ~level:`info "@.    ht_summary%t = " (proc_name_triple p_entry p_exit);
  print_indented 17 height_based_summary;
  logf ~level:`info "@.";
  (*let projection x = 
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false final_tr_symbols)
    (*||
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false*)
  in 
  let wedge_summary = Wedge.abstract ~exists:projection Cra.srk big_conjunction in 
  logf ~level:`info "    wedgified = %t@." (fun f -> Wedge.pp f wedge_summary);*)
  height_based_summary
  (* Things to do: 
     - construct a havoc-like transition with post variables,
        but use the solution as a guard
     - the guard needs to be a conjunction of the terms in the
        B_out definitions, but with things postified
     - and I'm constructing a new inequation in each case...
     - MAKE SURE to havoc the B_out variables themselves!
        (by putting them into the transform) *)

let sanity_check_recurrences recurrences term_of_id = 
  (if not ((List.length recurrences.blk_transforms) ==
           (List.length recurrences.blk_adds)) then
     failwith "Matrix recurrence transform/add blocks mismatched.");
  let print_expr i term = 
      logf ~level:`trace "  term_of_id[%d]=%a" i (Srk.Syntax.Expr.pp Cra.srk) term in
  Array.iteri print_expr term_of_id;
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
    logf ~level:`info "  Beginning to build a block of size: %d" (nRecurs);
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
    logf ~level:`info "  Registering add block of size: %d" (Array.length blk_add);
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
    recurrence_candidates (*b_in_symbols*) allow_interdependence = 
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
  let target_inner_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_inner_sym, [])) in 
  let target_outer_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_outer_sym, [])) in 
  (* *) 
  (* This function is applied to each inequation in sub_wedge *)
  let process_inequation vec negate = 
    (* *) 
    (* This function is applied to each (coeff,dim) pair in an inequation *)
    let process_coeff_dim_pair coeff dim =
      begin
      if dim == CoordinateSystem.const_id then (* ----------- CONSTANT *)
        (if is_non_negative coeff
          then UseTerm (coeff,dim)      (* Keep non-negative constants *)
          else DropTerm)                    (* Drop negative constants *)
      else match CoordinateSystem.destruct_coordinate sub_cs dim with 
      | `App (sym,_) -> 
        if sym == target_outer_sym then (* -------------- TARGET B_OUT *)
          (if is_negative coeff   (* Need upper bound on target symbol *)
            then UseTerm (coeff,dim)
            else DropInequation)
        else if sym == target_inner_sym then (* ---------- TARGET B_IN *)
          (if is_non_negative coeff
            then UseTerm (coeff,dim)
            else DropTerm)
        else if have_recurrence sym recurrences then  (* LOWER STRATUM *)
          (if is_non_negative coeff
            then UseTerm (coeff,dim) (* Keep non-negative coefficients *)
            else DropTerm)               (* Drop negative coefficients *)
        else if is_an_inner_symbol sym b_in_b_out_map then
          (* Possible interdependency between variables: we've found
             an inequation relating target_outer_sym, for which we don't
             have a recurrence yet, to sym, for which we also don't have
             a recurrence yet.  We'll need to verify later that these
             two variables are part of a strongly connected comoponent of
             mutual dependency. *)
          (if is_negative coeff
            then DropTerm
            else UseTermWithDependency (coeff,dim,sym))
        else 
          DropInequation
        (* The remaining cases involve non-target B_ins or 
          non-trivial terms over the target B_in *)
        (* We currently do not extract such recurrences *)
        (* In the future, we will change this to allow
            monomials and interdependencies *)
        (* The dual-height analysis will also have to do this differently *)
      | _ -> DropInequation
      end 
    in 
    let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
    let coeffs_and_dims = Srk.Linear.QQVector.enum vec in 
    let rec examine_coeffs_and_dims accum dep_accum = 
      match BatEnum.get coeffs_and_dims with (* Note: "get" consumes an element *)
      | None -> Some (accum, dep_accum)
      | Some (coeff,dim) -> 
        match process_coeff_dim_pair coeff dim with 
        | DropInequation -> None
        | DropTerm -> examine_coeffs_and_dims accum dep_accum
        | UseTerm(new_coeff,new_dim) -> 
          examine_coeffs_and_dims ((new_coeff,new_dim)::accum) dep_accum
        | UseTermWithDependency(new_coeff,new_dim,dep_dim) -> 
          (if allow_interdependence
          then examine_coeffs_and_dims ((new_coeff,new_dim)::accum) (dep_dim::dep_accum)
          else None)
          (* Set this to None to turn off interdependency extraction *)
        in 
    match examine_coeffs_and_dims [] [] with 
    | None -> ()
    | Some (new_coeffs_and_dims, dep_accum) -> 
      logf ~level:`trace "  Found a possible inequation";
      (*
      let target_outer_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_outer_sym, [])) in 
      let target_inner_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_inner_sym, [])) in 
      *)

      (*let sub_dim_to_rec_num = build_sub_dim_to_rec_num_map recurrences sub_cs in*)
      let term = CoordinateSystem.term_of_vec sub_cs vec in 
      (* *)
      let new_vec = Linear.QQVector.of_list new_coeffs_and_dims in
      let outer_coeff = QQ.negate (Linear.QQVector.coeff target_outer_dim new_vec) in 
      (* Drop any inequations that don't even mention the target B_out *)
      if QQ.equal QQ.zero outer_coeff then () else 
      begin 
      (* We've identified a recurrence; now we'll put together the data 
        structures we'll need to solve it.  *)
      logf ~level:`info "  [REC] %a" (Srk.Syntax.Term.pp Cra.srk) term;  
      logf ~level:`trace "    before filter: %a" Linear.QQVector.pp vec;
      logf ~level:`trace "     after filter: %a" Linear.QQVector.pp new_vec;
      let one_over_outer_coeff = QQ.inverse outer_coeff in 
      let new_vec = Linear.QQVector.scalar_mul one_over_outer_coeff new_vec in 
      let inner_coeff = Linear.QQVector.coeff target_inner_dim new_vec in 
      logf ~level:`trace "      inner_coeff: %a" QQ.pp inner_coeff;  

      recurrence_candidates := {outer_sym=target_outer_sym;
                                inner_sym=target_inner_sym;
                                coeff=inner_coeff;
                                sub_cs=sub_cs;
                                inequation=new_coeffs_and_dims;
                                dependencies=dep_accum} :: 
                                (!recurrence_candidates)
      end 
    in
  let process_constraint = function 
    | (`Eq, vec) ->  process_inequation vec true; process_inequation vec false
    | (`Geq, vec) -> process_inequation vec false in 
  List.iter process_constraint (Wedge.polyhedron sub_wedge) 
  end 

let make_outer_bounding_symbol
    (local_b_out_definitions, b_in_b_out_map, b_out_symbols) 
    (inner_sym, term) =
  let outer_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"B_out" `TyInt in
  let lhs = Srk.Syntax.mk_const Cra.srk outer_sym in 
  let rhs = term in 
  let b_out_constraint = Srk.Syntax.mk_leq Cra.srk lhs rhs in (* was: mk_eq *)
  logf ~level:`info "  [TERM]: %a ~ %t ~ %t " 
    (Srk.Syntax.Term.pp Cra.srk) term
    (fun f -> Srk.Syntax.pp_symbol Cra.srk f inner_sym)
    (fun f -> Srk.Syntax.pp_symbol Cra.srk f outer_sym);
  (*local_b_out_definitions := b_out_constraint :: (!local_b_out_definitions);
  b_in_b_out_map := Srk.Syntax.Symbol.Map.add inner_sym outer_sym !b_in_b_out_map;
  b_out_symbols := Srk.Syntax.Symbol.Set.add outer_sym (!b_out_symbols) in*)
  (b_out_constraint :: local_b_out_definitions,
   Srk.Syntax.Symbol.Map.add inner_sym outer_sym b_in_b_out_map,
   Srk.Syntax.Symbol.Set.add outer_sym b_out_symbols)

let make_extraction_formula 
  recursive_weight_nobc bounds b_in_b_out_map b_out_symbols =
  (*let local_b_out_definitions = ref [] in*)
  (* REMOVE BASE CASE semantically using the "recursion_flag" *)
  (*let initially_no_recursion = (assign_value_to_literal bounds.recursion_flag 0) in 
  let eventually_recursion = (assume_value_eq_literal bounds.recursion_flag 1) in 
  let recursive_weight_nobc = 
    K.mul (K.mul initially_no_recursion recursive_weight) eventually_recursion in*)
  let (tr_symbols, body) = to_transition_formula recursive_weight_nobc in
  logf ~level:`info "  rec_case_formula_body: @.%a@." (Srk.Syntax.Formula.pp Cra.srk) body;
  (* *)
  logf ~level:`info "[Chora] Listing bounded terms:";
  let (local_b_out_definitions, b_in_b_out_map, b_out_symbols) =
    List.fold_left 
      make_outer_bounding_symbol
      ([], b_in_b_out_map, b_out_symbols)
      bounds.bound_pairs in
  logf ~level:`trace "        Finished with bounded terms.";
  (* *)
  let non_negative_b_in (inner_sym, _) = 
    let lhs = Srk.Syntax.mk_real Cra.srk QQ.zero in 
    let rhs = Srk.Syntax.mk_const Cra.srk inner_sym in 
    Srk.Syntax.mk_leq Cra.srk lhs rhs in
  let all_b_in_non_negative = List.map non_negative_b_in bounds.bound_pairs in 
  let b_in_conjunction = Srk.Syntax.mk_and Cra.srk all_b_in_non_negative in 
  (* *)
  let b_out_conjunction = Srk.Syntax.mk_and Cra.srk local_b_out_definitions in 
  (*logf ~level:`info "  b_out_conjunction: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) b_out_conjunction;*)
  let extraction_formula = Srk.Syntax.mk_and Cra.srk [b_in_conjunction; body; b_out_conjunction] in 
  (extraction_formula, b_in_b_out_map, b_out_symbols)

let make_extraction_wedge extraction_formula bounds b_in_b_out_map b_out_symbols wedge_map = 
  (* NOTE: bounding symbols need to have been analyzed for all procedures in the SCC by this point *)
  let projection sym = 
    (*Srk.Syntax.Symbol.Set.mem sym !b_in_symbols*) 
    is_an_inner_symbol sym b_in_b_out_map || 
    Srk.Syntax.Symbol.Set.mem sym b_out_symbols in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk extraction_formula in 
  logf ~level:`info "  extraction_wedge = @.%t@." (fun f -> Wedge.pp f wedge); 
  (* CHANGES NEEDED: improve/replace our use of wedge projections *)
  (* For each outer bounding symbol (B_out), project the wedge down to that outer
       symbol and all inner bounding symbols *)
  logf ~level:`trace "  Building a wedge map..."; 
  let add_wedge_to_map map (target_inner_sym, _) = 
    let target_outer_sym = Srk.Syntax.Symbol.Map.find target_inner_sym b_in_b_out_map in
    let targeted_projection sym = 
      sym == target_outer_sym || 
      (*Srk.Syntax.Symbol.Set.mem sym !b_in_symbols*)
      is_an_inner_symbol sym b_in_b_out_map in 
    (* Project this wedge down to a sub_wedge that uses only this B_out and some B_ins *)
    let sub_wedge = Wedge.exists targeted_projection wedge in 
    Srk.Syntax.Symbol.Map.add target_inner_sym sub_wedge map in 
  let updated_wedge_map = 
    List.fold_left 
      add_wedge_to_map 
      wedge_map
      bounds.bound_pairs in 
  logf ~level:`trace "  Finished wedge map.";
  updated_wedge_map

(*let make_height_based_summary 
    rec_weight_nobc bounds program_vars post_height_sym top_down_formula = *)
let make_height_based_summaries
      rec_case_map bounds_map program_vars top_down_formula_map 
      (scc:BURG.scc) post_height_sym =
  (* *)
  let b_in_b_out_map = Srk.Syntax.Symbol.Map.empty in 
  let b_out_symbols = Srk.Syntax.Symbol.Set.empty in
  let wedge_map = Srk.Syntax.Symbol.Map.empty in 
  let extraction_formula_map = IntPairMap.empty in 
  (* *)
  (* For each procedure, create a transition formula for use in extraction *)
  let (extraction_formula_map, b_in_b_out_map, b_out_symbols) = 
    List.fold_left 
      (fun 
        (extraction_formula_map, b_in_b_out_map, b_out_symbols)
        (p_entry,p_exit,pathexpr) ->
      let rec_weight_nobc = IntPairMap.find (p_entry,p_exit) rec_case_map in 
      let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
      let (extraction_formula, b_in_b_out_map, b_out_symbols) = 
        make_extraction_formula 
          rec_weight_nobc bounds b_in_b_out_map b_out_symbols in
      let extraction_formula_map = 
        IntPairMap.add 
          (p_entry,p_exit) extraction_formula extraction_formula_map in
      (extraction_formula_map, b_in_b_out_map, b_out_symbols))
    (extraction_formula_map, b_in_b_out_map, b_out_symbols)
    scc.procs in 
  (*let (extraction_formula, b_in_b_out_map, b_out_symbols) = 
      make_extraction_formula 
        rec_weight_nobc bounds b_in_b_out_map b_out_symbols in*)
  (* TODO: Iterate this for all procedures... *)
  let wedge_map = 
    List.fold_left (fun wedge_map (p_entry,p_exit,pathexpr) ->
      let extraction_formula = 
          IntPairMap.find (p_entry,p_exit) extraction_formula_map in 
      let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
      make_extraction_wedge 
        extraction_formula bounds b_in_b_out_map b_out_symbols wedge_map)
    wedge_map
    scc.procs in 
  (*let wedge_map = 
      make_extraction_wedge 
        extraction_formula bounds b_in_b_out_map b_out_symbols wedge_map in*)
  (* *)
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
            recurrence_candidates (*b_in_symbols*) allow_interdependence)
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
  (* Here is the actual call to the recurrence extraction code *)
  let recurrences = extract_recurrences recurrences false in 
  (* Here recurrence extraction is complete *)
  (* *)
  (* *********************************************************************** *)
  (* ********               Recurrence Solving                      ******** *)
  (* *)
  let term_of_id = BatDynArray.to_array recurrences.term_of_id in 
  sanity_check_recurrences recurrences term_of_id;
  (* Change to pairs of transform_add blocks *)
  (* Add the appropriate constraint to the loop counter, so K >= 0 *)
  (* Send the matrix recurrence to OCRS and obtain a solution *)
  logf ~level:`trace "@.    Sending to OCRS ";
  (* Assuming single post-state height symbol shared by all procs in SCC *)
  let loop_counter = Srk.Syntax.mk_const Cra.srk post_height_sym in
  let nb_constants = 0 in
  let solution = SolvablePolynomial.exp_ocrs_external 
                  Cra.srk recurrences.ineq_tr loop_counter term_of_id 
                  nb_constants recurrences.blk_transforms 
                  recurrences.blk_adds in 
  logf ~level:`info "@.    solution: %a" 
      (Srk.Syntax.Formula.pp Cra.srk) solution;
  (* *)
  (* *********************************************************************** *)
  (* ********      Building summaries using recurrence solution     ******** *)
  let summary_list = 
    List.fold_left (fun sums (p_entry,p_exit,pathexpr) ->
      let top_down_formula = 
          IntPairMap.find (p_entry,p_exit) top_down_formula_map in 
      let bounds = IntPairMap.find (p_entry,p_exit) bounds_map in 
      let summary = build_summary_from_solution 
        solution b_in_b_out_map bounds top_down_formula program_vars p_entry p_exit in
      (p_entry,p_exit,summary)::sums)
    []
    scc.procs in 
  summary_list
  (* Old, single-procedure version: *)    
  (*build_summary_from_solution 
    solution b_in_b_out_map bounds top_down_formula program_vars*)
;;
 
let make_top_down_weight_multi 
    procs top (ts : Cra.K.t Cra.label Cra.WG.t) is_scc_call lower_summaries =
  (* Note: this height variable really represents depth *)
  let height_var = Core.Var.mk (Core.Varinfo.mk_global "H" (Core.Concrete (Core.Int 32))) in 
  let height_var_val = Cra.VVal height_var in 
  let height_var_sym = Cra.V.symbol_of height_var_val in (* NOTE: symbol_of puts symbol into hash table *)
  let set_height_zero = assign_value_to_literal height_var_val 0 in 
  let increment_height = increment_variable height_var_val in 
  let top_graph = ref BURG.empty in
  let dummy_exit_node = ref 0 in (* A dummy exit node representing having finished a base case *)
  List.iter (fun (p_entry,p_exit,pathexpr) ->
      let add_edges_alg = function
        | `Edge (s, t) ->
          dummy_exit_node := min !dummy_exit_node (min s t);
          begin match WeightedGraph.edge_weight ts s t with
            | Call (en, ex) -> 
              if not (is_scc_call s t) then 
                (* Call to a procedure that's in a lower SCC *)
                let low = M.find (en,ex) lower_summaries in
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight low) t
              else begin
                (* Call from this SCC back into this SCC *)
                (* I should add a half-projection weight here, maybe... *)
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight increment_height) en;
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight (project top)) t
              end
            | Weight w ->
              (* Regular (non-call) edge *)
              top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight w) t
          end
        | _ -> () (* Add, Mul, Star, etc. *) in
      NPathexpr.eval add_edges_alg pathexpr) procs; (* FIXME use eval table here for more speed *)
  dummy_exit_node := !dummy_exit_node - 1; (* Minimum vertex number minus one *)
  List.iter (fun (p_entry,p_exit,pathexpr) -> (* Add an edge from each proc exit to dummy_exit_node *)
      (* Note: this use of top is a hack; this top isn't really top; it's really
           havoc-all-program-vars.  For one thing, it doesn't havoc the height variable H,
           which is good, because that's the main thing we want to get out of this analysis. *)
      top_graph := Srk.WeightedGraph.add_edge !top_graph p_exit (Weight top) !dummy_exit_node) procs;
  let post_height_sym_ref = ref None in 
  let td_formula_map = (List.fold_left (fun td_formula_map (p_entry,p_exit,pathexpr) ->
      match WeightedGraph.path_weight !top_graph p_entry !dummy_exit_node with
      | Weight cycles ->
        let td_summary = K.mul set_height_zero cycles in
        logf ~level:`info "  multi_phi_td%t = [" (proc_name_triple p_entry p_exit);
        print_indented 15 td_summary; logf ~level:`info "  ]\n";
        let top_down_symbols, top_down_formula = to_transition_formula td_summary in  
        logf ~level:`info "@.  tdf%t: %a" (proc_name_triple p_entry p_exit)
            (Srk.Syntax.Formula.pp Cra.srk) top_down_formula;
        let is_post_height (pre_sym,post_sym) = (pre_sym == height_var_sym) in 
        post_height_sym_ref := Some (snd (List.find is_post_height top_down_symbols));
        IntPairMap.add (p_entry,p_exit) top_down_formula td_formula_map
      | _ -> failwith "A call was found in td_summary")
    IntPairMap.empty procs) in
  match !post_height_sym_ref with | None -> failwith "Missing PHS" | Some post_height_sym -> 
  (td_formula_map, post_height_sym);;

let make_top_down_weight_oneproc p_entry path_weight_internal top scc_call_edges = 
  let height_var = Core.Var.mk (Core.Varinfo.mk_global "H" (Core.Concrete (Core.Int 32))) in 
  let height_var_val = Cra.VVal height_var in 
  let height_var_sym = Cra.V.symbol_of height_var_val in 
  let set_height_zero = assign_value_to_literal height_var_val 0 in 
  let increment_height = increment_variable height_var_val in 
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
  let phi_td = K.mul set_height_zero (K.star (K.mul increment_height sum_of_fragments)) in
  logf ~level:`info "  phi_td = [";
  print_indented 15 phi_td;
  logf ~level:`info "  ]\n";
  phi_td, height_var_sym;;

let get_procedure_summary query rg procedure = 
  let entry = (RG.block_entry rg procedure).did in
  let exit = (RG.block_exit rg procedure).did in
  BURG.path_weight query entry exit

let debug_print_wedge_of_transition tr = 
  let level = if !chora_print_wedges then `always else `info in
  let (tr_symbols, body) = to_transition_formula tr in
  let projection x = 
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
    || 
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false (* false *)
  in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk body in 
  logf ~level:level "  %t@." (fun f -> Wedge.pp f wedge)

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
            match Wedge.symbolic_bounds_formula ~exists Cra.srk guard cost_symbol with
            | `Sat (lower, upper) ->
              begin match lower with
                | Some lower ->
                  logf ~level:`always " %a <= cost" (Syntax.Term.pp Cra.srk) lower;
                  logf ~level:`always " %a is o(%a)"
                    Varinfo.pp procedure
                    BigO.pp (BigO.of_term Cra.srk lower)
                | None -> ()
              end;
              begin match upper with
                | Some upper ->
                  logf ~level:`always " cost <= %a" (Syntax.Term.pp Cra.srk) upper;
                  logf ~level:`always " %a is O(%a)"
                  Varinfo.pp procedure
                  BigO.pp (BigO.of_term Cra.srk upper)
                | None -> ()
              end
            | `Unsat ->
              logf ~level:`always "%a is infeasible"
                Varinfo.pp procedure
          end else
          logf ~level:`always "Procedure %a has zero cost" Varinfo.pp procedure;
          Format.printf "---------------------------------\n")
    end

let check_assertions rg query main assertions = 
    if Srk.SrkUtil.Int.Map.cardinal assertions > 0 then
    Format.printf "======= Assertion Checking ======\n";
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

let find_recursive_calls (ts : Cra.K.t Cra.label Cra.WG.t) pathexpr (scc:BURG.scc) = 
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
(*let factor_pair pathexpr is_within_scc edge (alg:NPathexpr.t WeightedGraph.algebra) =*)
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

let build_summarizer (ts : Cra.K.t Cra.label Cra.WG.t) =  
  let program_vars = 
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
  let top = K.havoc program_vars in 
  let weight_of_call_zero cs ct cen cex = K.zero in
  (*let summarizer (scc : BURG.scc) path_weight_internal context pathexp_algebra =*)
  let summarizer (scc : BURG.scc) path_graph context lower_summaries = 
    (* Entry-point of summarizer.  Here we have been given an SCC to work on. *)
    logf ~level:`info "Processing a call-graph SCC:";

    (*let is_within_scc (s,t) = List.mem (s,t) callgraph_scc in*)
    let is_scc_call s t = match WeightedGraph.edge_weight ts s t with
                          | Call (en, ex) -> scc_mem scc en ex 
                          | _ -> false in
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
    (* *)
    let call_edge_map = List.fold_left (fun pe_map (p_entry,p_exit,pathexpr) ->
        let scc_call_edges = find_recursive_calls ts pathexpr scc in
        IntPairMap.add (p_entry,p_exit) scc_call_edges pe_map)
      IntPairMap.empty 
      scc.procs in 

    (* ---------------------- Check for non-recursive SCC ------------------------- *)
    if (List.length scc.procs == 1 
        && (let (p_entry,p_exit,pathexpr) = List.hd scc.procs in
        IntPairSet.cardinal 
          (IntPairMap.find (p_entry,p_exit) call_edge_map) == 0)) then
      (logf ~level:`info "  Non-recursive SCC.";
      let (p_entry,p_exit,pathexpr) = List.hd scc.procs in
      let single_proc_weight = 
        path_weight_internal p_entry p_exit weight_of_call_zero in
      [(p_entry,p_exit,project single_proc_weight)])
    else 
    begin
      (* ---------------------------- Recursive SCC ------------------------------- *)
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


      logf ~level:`info "  Beginning top-down analysis"; 
      (*   ***   Compute top-down summaries for each procedure   ***   *)
      let (top_down_formula_map, post_height_sym) = 
        make_top_down_weight_multi scc.procs top ts is_scc_call lower_summaries in
      logf ~level:`info "  Finished top-down analysis"; 

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

      (*   ***   Compute the abstraction that we will use for a call to each procedure  ***   *)
      let bounds_map = List.fold_left (fun b_map (p_entry,p_exit,pathexpr) ->
          let base_case_weight = IntPairMap.find (p_entry,p_exit) base_case_map in 
          let bounds = mk_call_abstraction base_case_weight in 
          logf ~level:`info "  call_abstration%t = [" (proc_name_triple p_entry p_exit); 
          print_indented 15 bounds.call_abstraction; logf ~level:`info "  ]";
          IntPairMap.add (p_entry,p_exit) bounds b_map)
        IntPairMap.empty 
        scc.procs in 

      (*   ***   Compute the recursive-case weight for each procedure  ***   *)
      let rec_case_map = List.fold_left (fun rc_map (p_entry,p_exit,pathexpr) ->
          (* Define a way of handling calls to each procedure in the SCC *)
          let weight_of_call_rec cs ct cen cex = 
            let callee_bounds = IntPairMap.find (cen,cex) bounds_map in
            callee_bounds.call_abstraction in
          (* Construct the recursive-case weight *)
          (* *)
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
          IntPairMap.add (p_entry,p_exit) recursive_weight_nobc rc_map)
        IntPairMap.empty 
        scc.procs in 

      let summary_list = 
        make_height_based_summaries
          rec_case_map bounds_map program_vars top_down_formula_map scc post_height_sym in 

        summary_list 
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
    ("-chora-wedges",
     Arg.Set chora_print_wedges,
     " Print procedure summaries abstracted to wedges")

(* 
  Format.printf "wedge: @.  %t @.@." (fun f -> Wedge.pp f wedge);
  Format.printf "formula: @.  %a @.@." (Syntax.Formula.pp srk) phi;
*)

(*
      (*   ***   Compute the formula-version of the top-down summary and 
       *           the post-state height symbol for each procedure         ***   *)
      let top_down_formula_map = List.fold_left (fun tdf_map (p_entry,p_exit,pathexpr) ->
          let base_case_weight = IntPairMap.find (p_entry,p_exit) base_case_map in 
          let top_down_weight = IntPairMap.find (p_entry,p_exit) top_down_weight_map in
          (* Note: this use of top is a hack; this top isn't really top; it's really
               havoc-all-program-vars.  For one thing, it doesn't havoc the height variable H. *)
          (* Make a formula from top_down_weight and get the post-state height symbol *)
          let top_down_symbols, top_down_formula = 
            (*K.*)to_transition_formula (K.mul (K.mul top_down_weight base_case_weight) top) in
          logf ~level:`info "@.  tdf%t: %a" (proc_name_triple p_entry p_exit)
              (Srk.Syntax.Formula.pp Cra.srk) top_down_formula;
          let is_post_height (pre_sym,post_sym) = (pre_sym == pre_height_sym) in 
          let new_post_height_sym = 
            try snd (List.find is_post_height top_down_symbols) 
            with Not_found -> failwith "CHORA: Failed to find post-height symbol" in 
          (match !post_height_sym_ref with 
           | Some sym -> if sym != new_post_height_sym 
                         then failwith "Differing post-state height symbols"
                         (* I don't think this happens currently.  If it did happen, we
                             should create the recurrence solution with a single fresh
                             loop counter and equate that loop counter to each proc's
                             post-height symbol at summary-construction time. *)
           | None -> post_height_sym_ref := Some new_post_height_sym);
          IntPairMap.add (p_entry,p_exit) (top_down_formula,new_post_height_sym) tdf_map)
        IntPairMap.empty 
        scc.procs in 
*)


        (*let height_based_summary = 
            make_height_based_summary bounds recursive_weight program_vars post_height_sym 
            top_down_formula in*)
        (*let height_based_summary = 
            make_height_based_summary recursive_weight_nobc bounds program_vars post_height_sym 
            top_down_formula in*)

        
        
      (* *)
      (*
      let summaries = List.map (fun (p_entry,p_exit,pathexpr) ->
        (*let scc_call_edges = find_recursive_calls ts pathexpr scc in*)

        let scc_call_edges = IntPairMap.find (p_entry,p_exit) call_edge_map in 
        assert (IntPairSet.cardinal scc_call_edges != 0); 
        let (rec_pe,nonrec_pe) = IntPairMap.find (p_entry,p_exit) split_expr_map in

        (* TODO Better handle the footprints of weights, rather than using top.
         * Should take a pass over all edge weights to union their footprints.
         * With max, I could allow extraction to use known constants in extraction. *)
        let (top_down_weight, pre_height_sym) = 
          make_top_down_weight_oneproc p_entry path_weight_internal top scc_call_edges in

        let base_case_weight = IntPairMap.find (p_entry,p_exit) base_case_map in 

        let bounds = mk_call_abstraction base_case_weight in 
        logf ~level:`info "  call_abstration = ["; print_indented 15 bounds.call_abstraction; logf ~level:`info "  ]";
        let weight_of_call_rec cs ct cen cex = 
          if cen == p_entry && cex == p_exit then bounds.call_abstraction
          else failwith "Mutual recursion not implemented" in

        (* WARNING: the following line isn't precise unless you take special action to
             remove the base case later... *)
        (*let recursive_weight = path_weight_internal p_entry p_exit weight_of_call_rec in
        logf ~level:`info "  recursive_weight = [";
        print_indented 15 recursive_weight;
        logf ~level:`info "  ]";*)
        let recursive_weight_nobc = project (NPathexpr.eval (edge_weight_with_calls weight_of_call_rec) rec_pe) in
        logf ~level:`info "  recursive_weight-BC = [";
        print_indented 15 recursive_weight_nobc;
        logf ~level:`info "  ]"; 

        (* Note: this use of top is a hack; this top isn't really top; it's really
             havoc-all-program-vars.  For one thing, it doesn't havoc the height variable H. *)
        (* Make a formula from top_down_weight and get the post-state height symbol *)
        let top_down_symbols, top_down_formula = 
          K.to_transition_formula (K.mul (K.mul top_down_weight base_case_weight) top) in
        logf ~level:`info "@.  tdf: %a" 
            (Srk.Syntax.Formula.pp Cra.srk) top_down_formula;
        let is_post_height (pre_sym,post_sym) = (pre_sym == pre_height_sym) in 
        let post_height_sym = 
          try snd (List.find is_post_height top_down_symbols) 
          with Not_found -> failwith "CRA-Nonlinrec: Failed to find post-height symbol" in 

        let height_based_summary = 
            make_height_based_summary recursive_weight_nobc bounds program_vars post_height_sym 
            top_down_formula in

        (p_entry,p_exit,height_based_summary)) scc.procs in
      let one_summary = List.hd summaries in
      [one_summary] *)
        
(*
 * Mostly-functional old version...
 
let make_top_down_weight_multi 
    procs top (ts : Cra.K.t Cra.label Cra.WG.t) is_scc_call lower_summaries =
  (* Note: this height variable really represents depth *)
  let height_var = Core.Var.mk (Core.Varinfo.mk_global "H" (Core.Concrete (Core.Int 32))) in 
  let height_var_val = Cra.VVal height_var in 
  let height_var_sym = Cra.V.symbol_of height_var_val in 
  let set_height_zero = assign_value_to_literal height_var_val 0 in 
  let increment_height = increment_variable height_var_val in 
  let top_graph = ref BURG.empty in
  let dummy_exit = ref 0 in (* A dummy exit node representing having finished a base case *)
  List.iter (fun (p_entry,p_exit,pathexpr) ->
      let add_edges_alg = function
        | `Edge (s, t) ->
          dummy_exit := min !dummy_exit (min s t);
          begin match WeightedGraph.edge_weight ts s t with
            | Call (en, ex) -> 
              if not (is_scc_call s t) then 
                (* Call to a procedure that's in a lower SCC *)
                let low = M.find (en,ex) lower_summaries in
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight low) t
              else begin
                (* Call from this SCC back into this SCC *)
                (* I should add a half-projection weight here, maybe... *)
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight increment_height) en;
                top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight (project top)) t
              end
            | Weight w ->
              (* Regular (non-call) edge *)
              top_graph := Srk.WeightedGraph.add_edge !top_graph s (Weight w) t
          end
        | _ -> () (* Add, Mul, Star, etc. *) in
      NPathexpr.eval add_edges_alg pathexpr)
    procs;
  List.iter (fun (p_entry,p_exit,pathexpr) -> (* Add an edge from each proc exit to dummy_exit *)
      (* Note: this use of top is a hack; this top isn't really top; it's really
           havoc-all-program-vars.  For one thing, it doesn't havoc the height variable H,
           which is good, because that's the main thing we want to get out of this analysis. *)
      top_graph := Srk.WeightedGraph.add_edge !top_graph p_exit (Weight top) dummy_exit-1)
    procs;
  let td_summary_map = List.fold_left 
    (fun td_summary_map (p_entry,p_exit,pathexpr) ->
      match WeightedGraph.path_weight !top_graph p_entry p_exit with
      | Weight cycles ->
        let td_summary = K.mul set_height_zero cycles in
        logf ~level:`info "  multi_phi_td%t = [" (proc_name_triple p_entry p_exit);
        print_indented 15 td_summary;
        logf ~level:`info "  ]\n";
        IntPairMap.add (p_entry,p_exit) td_summary td_summary_map
      | _ -> failwith "Call returned td_summary")
    IntPairMap.empty
    procs in
  (td_summary_map, height_var_sym);;
*)
        
        
        (*List.iter (fun vi -> (logf ~level:`info "       var %t @." (fun f -> Varinfo.pp f vi))) file.vars; *)
    (* let vars = List.filter (fun vi -> not (CfgIr.defined_function vi file)) file.vars in *)
    (*let vars = List.filter (fun vi -> 
      match Core.Varinfo.get_type vi with 
      | Concrete ctyp ->
        (match ctyp with 
         | Func (_,_) -> false 
         | _ -> true ) 
      | _ -> true ) file.vars in *)
    (*List.iter (fun vi -> (logf ~level:`info "  true var %t @." (fun f -> Varinfo.pp f vi))) vars;*)

      (*let weight =
        BURG.weight_algebra (fun s t ->
            match M.find (s, t) (!top_graph).labels with
            | Weight w -> w
            | Call (en, ex) -> failwith "Error: call in top_graph") in
      let td_summary = NPathexpr.eval ~table:tab weight cycles in*)
  (*let context = NPathexpr.mk_context () in
  let top_path_graph =
    { graph = !top_graph.graph;
      labels = M.mapi (fun (u,v) _ -> NPathexpr.mk_edge context u v) rg.labels;
      algebra = pathexp_algebra context } in *)
(*
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
*)


