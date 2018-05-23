(* Solve a max-plus recurrence *)

open Graph;;

(* Requisite types:
 *    weights: eventually GMP rationals; initially may be int; but, I do 
 *       need them to be allowed to be negative infinity
 *
 * Requisite data structures:
 *    Some numeric type...
 *    Matrix for input
 *        integer access, weight elements
 *    Digraph for matrix 
 *        Vertices have integers
 *        Edges have weight-type (eventually GMP rationals, I guess)
 *    Condensed (acyclic) digraph
 *        Vertices are addressed by integers
 *        Each vertex stands for a set of integers
 *        Edges are unweighted
 *
 *    Convenience data structures / operations:
 *         - map from components to contents
 *         - map from node to component ID
 *
 * Requisite operations:
 *    Compute a graph condensation:
 *    Topologically sort the strongly-connected components
 *    Find the ancestors of a component
 *    Find the descendants of a component
 *    Compute the simple cycles
 *
 * Better operations:
 *    Use a faster algorithm to compute slopes
 *)

type fweight = float;;  (* Finite weight. *) 
(* These are integers for now, but eventually we'll use GMP rationals *)

(* For easy dualization, I'm putting all maxes and mins in terms of best and worst *)
let fwt_best x y = max x y;;
let fwt_worst x y = min x y;;

let fwt_sub fw1 fw2 = fw1 -. fw2;;

type weight = Worst | Fin of fweight;;

let wt_add w1 w2 = 
    match w1 with | Worst -> Worst | Fin v1 ->
        match w2 with | Worst -> Worst | Fin v2 -> Fin (v1 +. v2)
;;

let wt_best w1 w2 = 
    match w1 with | Worst -> w2 | Fin v1 ->
        match w2 with | Worst -> w1 | Fin v2 -> Fin (fwt_best v1 v2)
;;

module V = struct
  type t = int (* vertex number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;
module E = struct
  type t = fweight
  let compare = Pervasives.compare
  let default = 0.0
end;;

(* Max-plus recurrence graph *)
module MPGraph = Imperative.Graph.ConcreteLabeled(V)(E);;

module V2 = struct
  type t = int (* SCC number *)
  let compare = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;

module SCCGraph = Imperative.Graph.Concrete(V2);;

(* module MPGraph = Graph.Pack.Digraph;; *)

module Tests = struct
    module Knee1 = struct
        let matrix = [| [| (Fin 0.0);     Worst;     Worst     |];
                        [| (Fin (-14.0)); (Fin 3.0); Worst     |];
                        [| Worst;         (Fin 0.0); (Fin 1.0) |] |]
    end;;
end;;

let matrixToGraph matrix = 
    let graph = MPGraph.create () in
    let add_edges_in_row i row =
        let add_edge j wt = 
            match wt with | Worst -> () | Fin fwt ->
            MPGraph.add_edge_e graph (MPGraph.E.create i fwt j) in
        Array.iteri add_edge row in
    Array.iteri add_edges_in_row matrix
;;

module MPComponents = Graph.Components.Make(MPGraph);;
module IntMap = Map.Make(struct type t = int let compare = compare end);;
module IntIntMap = Map.Make(struct type t = int * int let compare = compare end);;

(* I chose Karp's algorithm because it was easy. *)
(*   We could use a faster alternative if time complexity becomes a concern. *)
let karpBestCycleMean graph nSCCs mapVertexToSCC mapSCCToVertices =
    (* Edges between SCCs are irrelevant, so we filter them out: *)
    let predecessors i =
        let unfiltered = MPGraph.pred graph i in
        List.filter (fun j -> ((mapVertexToSCC i) = (mapVertexToSCC j)))
                    unfiltered in
    let edge_weight i j = MPGraph.E.label (MPGraph.find_edge graph i j) in
    (* Loop over iSCC:, the SCC index *)
    let rec karpForSCC iSCC bestCycleMean =
        (* We run Karp's algorithm on one SCC, the one having number iSCC   *)
        if (iSCC >= nSCCs) then bestCycleMean else
        let vertices = mapSCCToVertices iSCC in 
        let nVertices = Array.length vertices in
        let startVertex = vertices.(0) in (* arbitrary start vertex      *)
        (* In the following, fMap (which Karp calls "F") is an important *)
        (*   data structure.  The (k,v) entry in fMap encodes the best   *)
        (*   total weight that can be achieved in k steps starting at    *)
        (*   startVertex and ending at v.                                *)
        (* Set initial conditions for fMap *)
        let fMap = Array.fold_left
            (fun fMap uVertex -> IntIntMap.add 
                (0, uVertex)
                (if (uVertex = startVertex) then (Fin 0.0) else Worst) 
                fMap) IntIntMap.empty vertices in
        (* Now, we will compute fMap (Karp's F_k(v)) using a recurrence. *)
        (* Loop over the number of steps in a progression (Karp's "k"):  *)
        let rec findProgressions steps fMap =
            if (steps > nVertices) then fMap else
            (* Loop over vVertex (the target vertex, Karp's "v") *)
            let fMap = (Array.fold_left
                (fun fMap vVertex -> IntIntMap.add 
                    (steps, vVertex)

                    (let candidates = (List.map
                            (fun uVertex -> 
                                wt_add 
                                    (Fin (edge_weight uVertex vVertex)) 
                                    (IntIntMap.find (steps-1, uVertex) fMap))
                            (predecessors vVertex)) in

                        (List.fold_left wt_best Worst candidates))

                    fMap) fMap vertices) in
            findProgressions (steps + 1) fMap in
        let fMap = findProgressions 1 fMap in

        (* The heart of Karp's algorithm: *)
        let iSCCBestCycleMean = (Array.fold_left (fun wt vVertex->
            (* The best, over all vertices (vVertex) ... *)
            wt_best wt (
              match (IntIntMap.find (nVertices, vVertex) fMap) with 
              | Worst -> Worst
              | Fin fnv -> 
                (* The worst, over all numbers of steps (steps) ...         *)
                (*                                                          *)
                (* First, we scan over all numbers of steps;                *)
                (*   we will filter out infinite F_k(v) values.             *)
                let rec scanOverSteps steps pairs = 
                    if (steps >= nVertices) then pairs else
                    (* Karp's F_k(v) *)
                    let fkv = (IntIntMap.find (nVertices, vVertex) fMap) in
                    let pairs = match fkv with 
                                (* Ignore the F_k(v) for this k if          *)
                                (*    this F_k(v) is infinite.              *)
                                | Worst -> pairs
                                | Fin fin_fkv -> (steps, fin_fkv) :: pairs in
                    scanOverSteps (steps + 1) pairs
                in let pairs = (scanOverSteps 0 []) in
                (* Now scan over pairs (steps, fkv) having finite fkv       *)
                match pairs with 
                | [] -> failwith "Failure in Karp's algorithm"
                | (steps, fkv) :: tail ->
                  (* Compute a cycle mean using F_n(v), F_k(v), k, and n    *)
                  let cycleMean steps fnv fkv = 
                      (fwt_sub fnv fkv) /. (float_of_int (nVertices - steps)) in
                  (* There had better be at least one finite fkv...         *)
                  let firstCycleMean = cycleMean steps fnv fkv in
                  let foldHelper fwt (steps, fkv) = 
                      fwt_worst fwt (cycleMean steps fnv fkv) in
                  (* Worst cycle mean among progressions ending at vVertex: *)
                  Fin (List.fold_left foldHelper firstCycleMean tail)
                  
              ) ) Worst vertices ) in

        let bestCycleMean = (IntMap.add iSCC iSCCBestCycleMean bestCycleMean) in

        karpForSCC (iSCC + 1) bestCycleMean in
    let bestCycleMean = karpForSCC 0 IntMap.empty in
    bestCycleMean 
;;

let createUpperBound graph = 
    let nVertices = MPGraph.nb_vertex graph in
    let (nSCCs, mapVertexToSCC) = (MPComponents.scc graph) in
    let mapSCCToVertices = Array.make nSCCs [] in
    let rec makeVertexLists uVertex =
        if uVertex >= nVertices then () else 
            let iSCC = (mapVertexToSCC uVertex) in
            mapSCCToVertices.(iSCC) <- uVertex :: mapSCCToVertices.(iSCC)
    in makeVertexLists 0;
    let criticalWeight = Array.make nSCCs Worst in
    ()
;;

(*
let createUpperBound () = 
  (*  1. Construct a graph representation of the loop body matrix *) 
  (*  2. Compute the condensation of our graph *)
  (*  3. Compute critical circuit average weights (a.k.a. "critical weights") *)
  (*  4. Compute the bounding slopes: *)
  (*    First, initialize the values *)

  (*    The bounding slope in position (i,k) is the highest critical weight that is found    *)
  (*      in any circuit that is reachable from i and that can reach k.                      *)
  (*    So, we loop over each SCC (call it j),                                               *)
  (*      find all upstream SCCs (call each such i),                                         *)
  (*      and downstream SCCs (call each such k);                                            *)
  (*      then, what we have is (SCC_i) --*--> (SCC_j) --*--> (SCC_k)                        *)
  (*    Each time we find such a j, we update our slope for (i,k) to be j's critical weight  *)
  (*      if j's critical weight is greater than our current slope for (i,k).                *)
  (*  5. Compute the bounding intercepts (perform the "intercept propagation" steps)         *)

;;
*)



