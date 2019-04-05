open Core
open Apak
open CfgIr
open Srk

module RG = Interproc.RG
module G = RG.G
(*module K = NewtonDomain.ICRASum*)
module K = Cra.K
module Ctx = NewtonDomain.Ctx

include Log.Make(struct let name = "cra_nonlinrec" end)
module A = Interproc.MakePathExpr(Cra.K)

open Pathexpr


module IntPair = struct
  type t = int * int [@@deriving ord]
  let equal (x,y) (x',y') = (x=x' && y=y')
  let hash = Hashtbl.hash
end
(*module IntPairMap = BatMap.Make(IntPair)*)
module IntPairSet = BatSet.Make(IntPair)

let project = K.exists Cra.V.is_global

module BURG = WeightedGraph.MakeBottomUpRecGraph(struct
  include K
  let project = project
end)

(* ugly: copied from newtonDomain just for debugging *)
let print_indented indent k =
      Printf.printf "%s"
      (SrkUtil.mk_show (fun formatter tr ->
          Format.pp_open_vbox formatter indent;
          Format.pp_print_break formatter 0 0;
          Format.fprintf formatter "%a" K.pp tr;
          Format.pp_close_box formatter ()) k)

let analyze_nonlinrec file =
  Cra.populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let (ts, assertions) = Cra.make_transition_system rg in
      let top = 
        (* let open CfgIr in let file = get_gfile() in *)
        K.havoc (List.map (fun vi -> Cra.VVal (Var.mk vi)) file.vars) in
      let summarizer (scc : BURG.scc) path_weight_internal = 
        print_endline "I saw an SCC:";
        List.iter (fun (u,v,p) -> (Format.printf "  Proc(%d,%d) = %t \n" u v (fun f -> Pathexpr.pp f p))) scc.procs;
        List.iter (fun (p_entry,p_exit,pathexpr) ->
            let pe_call_edge_set = function
              | `Edge (s, t) ->
                begin match WeightedGraph.edge_weight ts s t with
                  | Call (en, ex) -> IntPairSet.singleton (s,t)
                  | _ -> IntPairSet.empty
                end
              | `Mul (x, y) | `Add (x, y) -> IntPairSet.union x y
              | `Star x -> x
              | `Zero | `One -> IntPairSet.empty
            in
            let call_edges = eval pe_call_edge_set pathexpr in
            Format.printf "  calls = [ ";
            IntPairSet.iter (fun (s,t) -> Format.printf "(%d,%d) " s t) call_edges;
            Format.printf "]\n";
            let weight_of_call_top cs ct cen cex = project top in
            Format.printf "  fragments = [";
            let sum_of_fragments = IntPairSet.fold (fun (s,t) running_total -> 
              let fragment_weight = path_weight_internal p_entry s weight_of_call_top in
              (* (Format.printf "  << %t >> \n" (fun f -> Pathexpr.pp f fragment_weight)) *)
              (* Format.fprintf Format.std_formatter "<<( %a )>> \n" K.pp fragment_weight *)
              print_indented 15 fragment_weight;
              Format.printf "\n";
              K.add running_total fragment_weight
              ) call_edges K.zero in
            Format.printf "  ]\n";
            let phi_td = (K.star sum_of_fragments) in
            Format.printf "  phi_td = [";
            print_indented 15 phi_td;
            Format.printf "  ]\n";
            let weight_of_call_zero cs ct cen cex = K.zero in
            let base_case_weight = path_weight_internal p_entry p_exit weight_of_call_zero in
            Format.printf "  base_case = [";
            print_indented 15 base_case_weight;
            Format.printf "  ]\n";
            ()) scc.procs;
        [] in
      (* *) 
      let query = BURG.mk_query ts summarizer in
       ()
      (* let query = TS.mk_query ts in *)
    end
  (* *)
  | _ -> assert false;;

let _ =
  CmdLine.register_pass
    ("-cra-nonlinrec",
     analyze_nonlinrec,
     " Compositional recurrence analysis for non-linear recursion")


