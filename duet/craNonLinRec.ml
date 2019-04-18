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
      Format.printf "%s"
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
        let newsym = Srk.Syntax.mk_symbol Cra.srk ~name:("postrec_" ^ Var.show var) (Var.typ var :> Srk.Syntax.typ) in
        (*Format.printf "New Symbol Created!  old=%s  new=%s\n" 
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

(* PASS REC FLAG IN FROM OUTSIDE *)
(* Make bound analysis? *)
let mk_call_abstraction base_case_weight = 
  let (tr_symbols, body) = to_transition_formula base_case_weight in
  (*Format.printf "  transition_formula_body: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) body;*)
  let projection x = 
    (* FIXME: THIS IS QUICK AND DIRTY *)
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
    || 
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false (* false *)
  in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk body in 
  Format.printf "\n  base_case_wedge = %t \n\n" (fun f -> Wedge.pp f wedge);
  let cs = Wedge.coordinate_system wedge in 
  let bounding_atoms = ref [] in
  let bound_list = ref [] in
  let add_bounding_var vec negate =
      let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
      let term = CoordinateSystem.term_of_vec cs vec in 
      (*Format.printf "  base-case-bounded term: %a \n" (Srk.Syntax.Term.pp Cra.srk) term;*)
    let bounding_var = Core.Var.mk (Core.Varinfo.mk_global "B_in" ( Core.Concrete (Core.Int 32))) in 
    let bounding_var_sym = Cra.V.symbol_of (Cra.VVal bounding_var) in 
    (*let bounding_var_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"B_in" `TyInt in *)
    let bounding_term = Srk.Syntax.mk_const Cra.srk bounding_var_sym in 
    let bounding_atom = Srk.Syntax.mk_leq Cra.srk term bounding_term in 
    bounding_atoms := bounding_atom            :: (!bounding_atoms);
    bound_list     := (bounding_var_sym, term) :: (!bound_list) in
  let handle_constraint = function 
    | (`Eq, vec) ->
      (*Format.printf "  rec equation: %a \n" Linear.QQVector.pp vec;*)
      add_bounding_var vec true; 
      add_bounding_var vec false
    | (`Geq, vec) ->
      add_bounding_var vec true in 
  List.iter handle_constraint (Wedge.polyhedron wedge);
  let rec_flag_var = Core.Var.mk (Core.Varinfo.mk_global "Recursion_Flag" ( Core.Concrete (Core.Int 32))) in 
  let rec_flag_val = Cra.VVal rec_flag_var in 
  let rec_flag_var_sym = Cra.V.symbol_of rec_flag_val in (* Add to symbol table... (HACK!) *)
  let set_rec_flag = assign_value_to_literal rec_flag_val 1 in 
  let call_abstraction_fmla = Srk.Syntax.mk_and Cra.srk (!bounding_atoms) in 
  let call_abstraction_weight = of_transition_formula tr_symbols call_abstraction_fmla in 
    {bound_pairs = !bound_list;
     recursion_flag = rec_flag_val; 
     call_abstraction = K.mul set_rec_flag call_abstraction_weight}

let mk_height_based_summary bounds recursive_weight = 
  (* REMOVE BASE CASE? *)
  let initially_no_recursion = (assign_value_to_literal bounds.recursion_flag 0) in 
  let eventually_recursion = (assume_value_eq_literal bounds.recursion_flag 1) in 
  let recursive_weight = 
    K.mul (K.mul initially_no_recursion recursive_weight) eventually_recursion in
  (* ASSUME B_in NON-NEGATIVE*)
  let (tr_symbols, body) = to_transition_formula recursive_weight in
  Format.printf "  transition_formula_body: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) body;
  let b_out_definitions = ref [] in 
  let b_in_b_out_pairs = ref [] in
  let add_b_out_definition (inner_sym, term) =
      (* I'm 90% sure this should be a different symbol *)
      let outer_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"B_out" `TyInt in
      let lhs = Srk.Syntax.mk_const Cra.srk outer_sym in 
      (*let lhs = Srk.Syntax.mk_const Cra.srk sym in *) 
      let rhs = term in 
      let equation = Srk.Syntax.mk_eq Cra.srk lhs rhs in 
      Format.printf "  bounded term: %a ~ %t ~ %t @." 
        (Srk.Syntax.Term.pp Cra.srk) term
        (fun f -> Srk.Syntax.pp_symbol Cra.srk f inner_sym)
        (fun f -> Srk.Syntax.pp_symbol Cra.srk f outer_sym);
      b_out_definitions := equation :: (!b_out_definitions);
      b_in_b_out_pairs := (inner_sym, outer_sym) :: (!b_in_b_out_pairs) in 
  List.iter add_b_out_definition bounds.bound_pairs;
  let b_out_conjunction = Srk.Syntax.mk_and Cra.srk (!b_out_definitions) in 
  (*Format.printf "  b_out_conjunction: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) b_out_conjunction;*)
  let full_conjunction = Srk.Syntax.mk_and Cra.srk [body; b_out_conjunction] in 
    let projection x = 
    (* FIXME: THIS IS QUICK AND DIRTY *)
    (List.fold_left (fun found (inner_sym,outer_sym) -> 
      found || inner_sym == x || outer_sym == x) false (!b_in_b_out_pairs))
    (*(List.fold_left (fun found (vpre,vpost) -> found || vpost == x) false tr_symbols)*)
    (*|| match Cra.V.of_symbol x with | Some v -> Cra.V.is_global v | None -> false (* false *) *)
  in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk full_conjunction in 
  Format.printf "\n  extraction_wedge = @.%t@. \n\n" (fun f -> Wedge.pp f wedge); 
  let direct_recurrence_extraction (inner_sym, target_outer_sym) = 
      let targeted_projection x = 
        (List.fold_left (fun found (inner_sym, _) -> 
          found || inner_sym == x || target_outer_sym == x) false (!b_in_b_out_pairs)) in 
      let sub_wedge = Wedge.exists targeted_projection wedge in 
      let sub_cs = Wedge.coordinate_system sub_wedge in 
      let target_vec = CoordinateSystem.vec_of_term 
        sub_cs (Srk.Syntax.mk_const Cra.srk target_outer_sym) in 
      let examine_inequation vec negate =
          let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
          let term = CoordinateSystem.term_of_vec sub_cs vec in 
          (* FIXME: the following test should be made faster *)
          (if ((QQ.compare (Srk.Linear.QQVector.dot vec target_vec) QQ.zero) < 0) then
          begin
            Format.printf "  extracted recurrence inequation: %a@." (Srk.Syntax.Term.pp Cra.srk) term;
            () 
          end
          else ()) in
      let handle_constraint = function 
        | (`Eq, vec) ->  examine_inequation vec true; examine_inequation vec false
        | (`Geq, vec) -> examine_inequation vec false 
        in 
      List.iter handle_constraint (Wedge.polyhedron sub_wedge) 
        in
  List.iter direct_recurrence_extraction (!b_in_b_out_pairs);
  (* *)
  ()
  (*  - Create B_out variables
      - Associate each B_out variable to the appropriate outer-call term
      ? How do I get things connected properly to pre- and post- variables?
      - Build the inequation atom for each B_out and its term
      - Make recursive_weight into a transition formula
      - Conjoin these transition formulas
      - Make a wedge out of the formula, projecting down to B_outs and B_ins
      - Walk over the B_out inequations, dump ones that break some rules

      * Consider: Make a second set of variables for the unchanging bounds?  *)
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
        Format.printf "I saw an SCC:\n";
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
            let bounds = mk_call_abstraction base_case_weight in 
            Format.printf "  call_abstration = [";
            print_indented 15 bounds.call_abstraction;
            Format.printf "  ]\n";
            let weight_of_call_rec cs ct cen cex = 
              if cen == p_entry && cex == p_exit then bounds.call_abstraction
              else failwith "Mutual recursion not implemented"
            in
            let recursive_weight = path_weight_internal p_entry p_exit weight_of_call_rec in
            Format.printf "  recursive_weight = [";
            print_indented 15 recursive_weight;
            Format.printf "  ]\n";
            let height_based_summary = mk_height_based_summary bounds recursive_weight in
            (* *)
            (*let bounding_var_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"Bpost" `TyInt in *)
            (* *)
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


