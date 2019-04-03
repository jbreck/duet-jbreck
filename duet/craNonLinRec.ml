open Core
open Apak
open CfgIr
open Srk

module RG = Interproc.RG
module G = RG.G
module K = NewtonDomain.ICRASum
module Ctx = NewtonDomain.Ctx

include Log.Make(struct let name = "cra_nonlinrec" end)
module A = Interproc.MakePathExpr(Cra.K)

(* As from CRA *)

(*

  - convert to formula? to transition (better!)?
  - extract information?
  - and then what should we produce, finally?

*)

(* As from weightedGraph *)

(*
   code used from wG to be replaced or retargeted

*)

(*
module IntPair = struct
  type t = int * int [@@deriving ord]
  let equal (x,y) (x',y') = (x=x' && y=y')
  let hash = Hashtbl.hash
end
module M = BatMap.Make(IntPair)
module U = WeightedGraph.U
type weighted_graph 

module MakeNonLinRecGraph (W : WeightedGraph.Weight) = struct

  include WeightedGraph.MakeRecGraph(W)

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
  module CallGraphWTO = Graph.WeakTopological.Make(CallGraph)

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
      graph : Pathexpr.t t; (* Path expression weighted graph *)
      table : W.t table; (* Path expression memo table  *)
      context : Pathexpr.context (* Path expression context *) }


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
    { mul = mk_mul context;
      add = mk_add context;
      star = mk_star context;
      zero = mk_zero context;
      one = mk_one context }

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
             |> eval ~table:query.table weight_algebra
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
               add_edge query'.graph src (mk_edge query.context src call) call
             in
             let labels' = M.add (src, call) (Weight weight) query'.labels in
             { query' with graph = graph';
                           labels = labels' }
         | _ -> query')
      query.graph
      src
      query

  let mk_query ?(delay=1) rg =
    let table = mk_table () in
    let context = mk_context () in
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
        labels = M.mapi (fun (u,v) _ -> mk_edge context u v) rg.labels;
        algebra = pathexp_algebra context }
    in

    if CallSet.is_empty calls then
      { summaries = M.empty;
        table;
        graph = path_graph;
        context;
        labels = rg.labels }
    else begin
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
      (* Compute summaries *************************************************)
      let callgraph_wto =
        let pe_calls = function
          | `Edge (s, t) ->
            begin match M.find (s, t) rg.labels with
              | Call (en, ex) -> CallSet.singleton (en, ex)
              | _ -> CallSet.empty
            end
          | `Mul (x, y) | `Add (x, y) -> CallSet.union x y
          | `Star x -> x
          | `Zero | `One -> CallSet.empty
        in
        let table = mk_table () in
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
                (eval ~table pe_calls pathexpr)
                callgraph)
            call_pathexpr
            initial_callgraph
        in
        CallGraphWTO.recursive_scc callgraph callgraph_entry
      in
      let summaries = ref (M.map (fun _ -> W.zero) call_pathexpr) in
      let weight =
        weight_algebra (fun s t ->
            match M.find (s, t) rg.labels with
            | Weight w -> w
            | Call (en, ex) -> M.find (en, ex) (!summaries))
      in
      let is_stable_edge unstable s t =
        match M.find (s, t) rg.labels with
        | Weight _ -> true
        | Call (s, t) -> not (CallSet.mem (s, t) unstable)
      in
      let rec loop_calls vertices wto = (* Collect all calls within an SCC *)
        let open Graph.WeakTopological in
        match wto with
        | Vertex v -> CallSet.add v vertices
        | Component (v, rest) ->
          fold_left loop_calls (CallSet.add v vertices) rest
      in

      (* stabilize summaries within a WTO component, and add to unstable all
         calls whose summary (may have) changed as a result. *)
      let rec fix () wto =
        let open Graph.WeakTopological in
        match wto with
        | Vertex call when call = callgraph_entry -> ()
        | Vertex call ->
          let pathexpr = M.find call call_pathexpr in
          let new_weight =
            eval ~table weight pathexpr
            |> W.project
          in
          summaries := M.add call new_weight (!summaries)
        | Component (call, rest) ->
          let pathexpr = M.find call call_pathexpr in
          let unstable = loop_calls CallSet.empty wto in
          let rec fix_component delay =
            let old_weight = M.find call (!summaries) in
            let new_weight =
              eval ~table weight pathexpr
              |> W.project
            in
            let new_weight =
              if delay > 0 then new_weight
              else W.widen old_weight new_weight
            in
            summaries := M.add call new_weight (!summaries);
            fold_left fix () rest;
            if not (W.equal old_weight new_weight) then begin
              forget table (is_stable_edge unstable);
              fix_component (delay - 1)
            end
          in
          fix_component delay
      in
      Graph.WeakTopological.fold_left fix () callgraph_wto;
      let query =
        { summaries = !summaries;
          table;
          graph = path_graph;
          context;
          labels = rg.labels }
      in
      (* For each (s,t) call containing a call (s',t'), add an edge from s to s'
         with the path weight from s to call(s',t'). *)
      CallSet.fold
        (fun (src, tgt) query' -> add_call_edges query' src)
        calls
        query
    end

  let path_weight query src tgt =
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
    |> eval ~table:query.table weight
end

*) 

(*

New version over top of TransitionRelation...

*)

(* As from CRA *)

(*
external add_wpds_rule: K.t -> int -> int -> unit = "add_wpds_rule"
external set_vertices: int -> int -> unit = "set_vertices_wfa"
external set_cWeight: K.t -> unit = "set_compare_weight"
external add_wpds_call_rule: K.t -> int -> int -> int -> unit = "add_wpds_call_rule"
external add_wpds_epsilon_rule: K.t -> int -> unit = "add_wpds_epsilon_rule"
external add_wpds_error_rule: K.t -> int -> int -> unit = "add_wpds_error_rule"
external add_wpds_print_hull_rule: int -> int -> int -> unit = "add_wpds_print_hull_rule"
*)

let analyze_nonlinrec file =
  Cra.populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let (ts, assertions) = Cra.make_transition_system rg in

      (*let query = TS.mk_query ts in*)
      ()
    end
  (*
      ts |> WeightedGraph.iter_edges (fun (u, label, v) ->
          match label with
          | WeightedGraph.Call (s, t) ->
            add_wpds_epsilon_rule (K.one ()) t;
            add_wpds_call_rule (K.one ()) u s v
          | WeightedGraph.Weight tr ->  
            if !K.use_left then
              add_wpds_rule (K.make_left tr) u v
            else
              add_wpds_rule (K.make_right (NewtonDomain.RK.lift_dnf tr)) u v);
      assertions |> SrkUtil.Int.Map.iter (fun v (phi, loc, msg) ->
            add_wpds_error_rule
              (K.assume (Ctx.mk_not phi))
              v
              loc.Cil.line);
      RG.vertices rg |> BatEnum.iter (fun (_, def) ->
          match def.dkind with
          | Builtin (PrintBounds v) ->
            add_wpds_print_hull_rule
              def.did
              (Def.get_location def).Cil.line
              (Var.get_id v)
          | _ -> ());
      add_wpds_epsilon_rule (K.one ()) (RG.block_exit rg main).did;
      set_vertices (RG.block_entry rg main).did (RG.block_exit rg main).did;
      set_cWeight (K.zero ());
      Callback.register "procedure_of_vertex_callback" (fun vertex ->
          (Interproc.RG.vertices rg)
          |> BatEnum.find (fun (block, v) -> vertex = v.did)
          |> fst
          |> Varinfo.show)
    end
  *)
  | _ -> assert false;;

let _ =
  CmdLine.register_pass
    ("-cra-nonlinrec",
     analyze_nonlinrec,
     " Compositional recurrence analysis for non-linear recursion")


