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

(* *) (* let name = "a[" ^ (Term.show srk t) ^ "]" in *)
(*let abstract ?(exists=fun x -> true) srk tr_symbols phi =
  let post_symbols = post_symbols tr_symbols in
  let subterm x = not (Symbol.Set.mem x post_symbols) in
  Wedge.abstract ~exists ~subterm srk phi
  |> abstract_wedge srk tr_symbols *)
(* *)
(*let closure iter =
    let srk = iter.srk in
    let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
    let loop_counter = mk_const srk loop_counter_sym in
    mk_and srk [(**)Iter.exp(**) iter.srk iter.tr_symbols loop_counter iter.iter;
                mk_leq srk (mk_real srk QQ.zero) loop_counter] *)
(*let abstract ?(exists=fun x -> true) srk tr_symbols body =
    let iter = (**)Iter.abstract(**) ~exists srk tr_symbols body in
    { srk; tr_symbols; iter } *)
(*let alpha tr =
    let (tr_symbols, body) = to_transition_formula tr in
    let exists =
      let post_symbols =
        List.fold_left
          (fun set (_, sym') -> Symbol.Set.add sym' set)
          Symbol.Set.empty
          tr_symbols
      in
      fun x ->
        match Var.of_symbol x with
        | Some _ -> true
        | None -> Symbol.Set.mem x post_symbols
    in
    (**)D.abstract(**) ~exists srk tr_symbols body *)
(*let closure iter =
    let transform =
      List.fold_left (fun tr (pre, post) ->
          match Var.of_symbol pre with
          | Some v -> M.add v (mk_const srk post) tr
          | None -> assert false)
        M.empty
        (D.tr_symbols iter)
    in
    { transform = transform;
      guard = (**)D.closure(**) iter } *)



let post_symbol =
  Memo.memo (fun sym ->
      match Var.of_symbol sym with
      | Some var ->
        Srk.Syntax.mk_symbol Cra.srk ~name:("postrec_" ^ Var.show var) (Var.typ var :> Srk.Syntax.typ)
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

let mk_call_abstraction base_case_weight = 
  let (tr_symbols, body) = to_transition_formula base_case_weight in
  Format.printf "  transition_formula_body: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) body;
  let projection x = 
    (* FIXME: THIS IS QUICK AND VERY DIRTY *)
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
    || 
    match Cra.V.of_symbol x with 
    | Some v -> true (* Cra.V.is_global v *)
    | None -> false (* false *)
  in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk body in 
  Format.printf "\n  base_case_wedge = %t \n\n" (fun f -> Wedge.pp f wedge);
  let cs = Wedge.coordinate_system wedge in 
  let make_bounding_var t = 
      let term = CoordinateSystem.term_of_vec cs t in 
      Format.printf "  base-case-bounded term: %a \n" (Srk.Syntax.Term.pp Cra.srk) term;
    let bounding_var = Core.Var.mk (Core.Varinfo.mk_global "B" ( Core.Concrete (Core.Int 32))) in 
    let bounding_var_sym = Cra.V.symbol_of (Cra.VVal bounding_var) in 
    (*let bounding_var_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"B" `TyInt in *)
    let bounding_term = Srk.Syntax.mk_const Cra.srk bounding_var_sym in 
    let bounding_atom = Srk.Syntax.mk_leq Cra.srk term bounding_term in 
    bounding_atom in
    (* PROBABLY KEEP TRACK OF SEVERAL OF THESE THINGS... *)
  let bounding_atoms = ref [] in
  let analyze_recurrence = 
    function
    | (`Eq, t) ->
      Format.printf "EQ\n";
      bounding_atoms := (make_bounding_var t) :: (!bounding_atoms) ;
      (* NEED TO DO NEGATED ONE ALSO *)
      ()
      (*Format.printf "  rec equation: %a \n" Linear.QQVector.pp t;*)
    | (`Geq, t) ->
      Format.printf "GEQ\n";
      (* NEED TO DO NEGATED ONE ONLY *)
      ()
  in
  List.iter analyze_recurrence (Wedge.polyhedron wedge);
  let call_abstraction_fmla = Srk.Syntax.mk_and Cra.srk (!bounding_atoms) in 
  of_transition_formula tr_symbols call_abstraction_fmla

(*
    let mul left right =
    let fresh_skolem =
      Memo.memo (fun sym ->
          let name = show_symbol Cra.srk sym in
          let typ = typ_symbol Cra.srk sym in
          mk_const Cra.srk (mk_symbol Cra.srk ~name typ))
    in
    let left_subst sym =
      match Var.of_symbol sym with
      | Some var ->
        if M.mem var left.transform then
          M.find var left.transform
        else
          mk_const Cra.srk sym
      | None -> fresh_skolem sym
    in
    let guard =
      mk_and srk [left.guard;
                  Srk.Syntax.substitute_const Cra.srk left_subst right.guard]
    in
    let transform =
      M.fold (fun var term transform ->
          if M.mem var transform then
            transform
          else
            M.add var term transform)
        left.transform
        (M.map (Srk.Syntax.substitute_const Cra.srk left_subst) right.transform)
    in
    K.construct guard transform
    *)

let analyze_nonlinrec file =
  Cra.populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let (ts, assertions) = Cra.make_transition_system rg in
      let top = 
        (* let open CfgIr in let file = get_gfile() in *)
        K.havoc (List.map (fun vi -> Cra.VVal (Core.Var.mk vi)) file.vars) in
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
            let base_case_weight = project (path_weight_internal p_entry p_exit weight_of_call_zero) in
            Format.printf "  base_case = [";
            print_indented 15 base_case_weight;
            Format.printf "  ]\n";
            (* *)
            let call_abstraction = mk_call_abstraction base_case_weight in 
            Format.printf "  call_abstration = [";
            print_indented 15 call_abstraction;
            Format.printf "  ]\n";
            let weight_of_call_rec cs ct cen cex = 
              if cen == p_entry && cex == p_exit then call_abstraction
              else failwith "Mutual recursion not implemented"
            in
            let recursive_weight = path_weight_internal p_entry p_exit weight_of_call_rec in
            Format.printf "  recursive_weight = [";
            print_indented 15 recursive_weight;
            Format.printf "  ]\n";
            (* WHICH VARIABLES TO PROJECT OUT? *)
            (*
            let atom_evaluator (formula_node : ('x, 'y) Srk.Syntax.open_formula) = 
            match formula_node with
            |  in
            let analyze_atom atom = 
              Srk.Syntax.Formula.eval Cra.srk atom_evaluator atom in
            let atoms = Wedge.to_atoms wedge in
            List.iter analyze_atom atoms;
            *)
            ();
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


