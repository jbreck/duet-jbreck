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
open BatPervasives

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
  let b_in_symbols = ref Srk.Syntax.Symbol.Set.empty in 
  let b_out_symbols = ref Srk.Syntax.Symbol.Set.empty in 
  let add_b_out_definition (inner_sym, term) =
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
    b_in_b_out_pairs := (inner_sym, outer_sym) :: (!b_in_b_out_pairs);
    b_in_symbols  := Srk.Syntax.Symbol.Set.add inner_sym (!b_in_symbols);
    b_out_symbols := Srk.Syntax.Symbol.Set.add outer_sym (!b_out_symbols) in 
  List.iter add_b_out_definition bounds.bound_pairs;
  let b_out_conjunction = Srk.Syntax.mk_and Cra.srk (!b_out_definitions) in 
  (*Format.printf "  b_out_conjunction: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) b_out_conjunction;*)
  let full_conjunction = Srk.Syntax.mk_and Cra.srk [body; b_out_conjunction] in 
  let projection sym = 
    Srk.Syntax.Symbol.Set.mem sym !b_in_symbols || 
    Srk.Syntax.Symbol.Set.mem sym !b_out_symbols in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk full_conjunction in 
  Format.printf "\n  extraction_wedge = @.%t@. \n\n" (fun f -> Wedge.pp f wedge); 
  (* *)
  let recurrence_candidates = ref [] in
  let best_outer_coefficient = ref Srk.Syntax.Symbol.Map.empty in 
  (* There's a need for an outer loop for stratification levels, although we should avoid
     redoing the expensive steps.  *)
  (* *)
  (* Obviously, these loops could have a simpler, faster structure... *)
  (*   Main idea: use symbols sets or maps... *)
  let direct_recurrence_extraction (target_inner_sym, target_outer_sym) = 
      let targeted_projection sym = 
        sym == target_outer_sym || Srk.Syntax.Symbol.Set.mem sym !b_in_symbols in     
      let sub_wedge = Wedge.exists targeted_projection wedge in 
      let sub_cs = Wedge.coordinate_system sub_wedge in
      let target_outer_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_outer_sym, [])) in 
      let target_inner_dim = CoordinateSystem.cs_term_id sub_cs (`App (target_inner_sym, [])) in 
      let target_vec = CoordinateSystem.vec_of_term sub_cs (Srk.Syntax.mk_const Cra.srk target_outer_sym) in 
      (* *)  
      let examine_inequation vec negate =
        let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
        let term = CoordinateSystem.term_of_vec sub_cs vec in
        let is_negative q = ((QQ.compare q QQ.zero) < 0) in
        let is_non_negative q = ((QQ.compare q QQ.zero) >= 0) in
        let is_at_least_one q = ((QQ.compare q QQ.one) >= 0) in
        let rec examine_coeff_dim_pair coeff dim accum =
            if dim == target_outer_dim then 
              (if is_negative coeff (* Did we get an upper bound on the target dimension? *)
                then Some ((coeff,dim)::accum) 
                else None)
            else if dim == target_inner_dim then 
              (if is_at_least_one coeff
                then Some ((coeff,dim)::accum)    
                else Some ((QQ.one,dim)::accum))  (* Minimal self-coefficient is one*)
            else if dim == CoordinateSystem.const_id then
              (if is_non_negative coeff
                then Some ((coeff,dim)::accum)    (* Keep non-negative constants *)
                else Some accum)                  (* Drop negative constants *)
            else 
              (* The remaining case is a non-target B_in dimension *)
              None
              (* In the future, we will change this to allow stratification and
                  interdependencies *)
        in 
        let coeffs_and_dims = Srk.Linear.QQVector.enum vec in 
        let rec examine_coeffs_and_dims accum = 
          match BatEnum.get coeffs_and_dims with 
          | None -> Some accum
          | Some (coeff,dim) -> 
            match examine_coeff_dim_pair coeff dim accum with 
            | None -> None
            | Some new_accum -> examine_coeffs_and_dims new_accum 
        in 
        match examine_coeffs_and_dims [] with 
        | None -> ()
        | Some new_coeffs_and_dims -> 
          Format.printf "  identified recurrence inequation: %a@." 
              (Srk.Syntax.Term.pp Cra.srk) term;  
          Format.printf "    before filter: %a @." Linear.QQVector.pp vec;
          let new_vec = Linear.QQVector.of_list new_coeffs_and_dims in
          Format.printf "     after filter: %a @." Linear.QQVector.pp new_vec;
          let outer_coeff = QQ.negate ( Linear.QQVector.coeff target_outer_dim new_vec) in 
          let inner_coeff = Linear.QQVector.coeff target_inner_dim new_vec in 
          let const_coeff = Linear.QQVector.coeff CoordinateSystem.const_id new_vec in 
          let blk_transform = [| [| QQ.div inner_coeff outer_coeff |] |] in 
          let blk_add = [| Polynomial.QQXs.scalar (QQ.div const_coeff outer_coeff) |] in 
          recurrence_candidates := (target_outer_sym,
                                    target_inner_sym,
                                    outer_coeff, 
                                    blk_transform,
                                    blk_add) :: (!recurrence_candidates);
          let old_coeff = Srk.Syntax.Symbol.Map.find_default 
            (QQ.add outer_coeff QQ.one) 
            target_inner_sym 
            !best_outer_coefficient in 
          if (QQ.compare outer_coeff old_coeff) <= 0 then 
            best_outer_coefficient := 
              Srk.Syntax.Symbol.Map.add 
              target_outer_sym 
              outer_coeff 
              !best_outer_coefficient;
          (* *)
          (*
          let ineq_tr = [(target_inner_sym, target_outer_sym)] in 
          let loop_counter_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"K" `TyInt in
          let loop_counter = Srk.Syntax.mk_const Cra.srk loop_counter_sym in
          let term_of_id = [| Srk.Syntax.mk_const Cra.srk target_inner_sym |] in (* Maybe put term in here? *)
          let nb_constants = 0 in 
          (* Change to pairs of transform_add blocks *)
          (* Add the appropriate constraint to the loop counter, so K >= 0 *)
          let solution = SolvablePolynomial.exp_ocrs_external 
                         Cra.srk ineq_tr loop_counter term_of_id 
                         nb_constants [ blk_transform ] [ blk_add ] in 
          (* *)
          Format.printf "    solution: %a@." 
              (Srk.Syntax.Formula.pp Cra.srk) solution; *)
          ()
           
          in
      let process_constraint = function 
        | (`Eq, vec) ->  examine_inequation vec true; examine_inequation vec false
        | (`Geq, vec) -> examine_inequation vec false 
        in 
      List.iter process_constraint (Wedge.polyhedron sub_wedge) 
        in
  List.iter direct_recurrence_extraction (!b_in_b_out_pairs);
  (* *)
  ();
  (* let done_symbols = ref Srk.Syntax.Symbol.Map.empty in *)

  (* Build up a matrix recurrence to give to OCRS *)
  (* let matrix_recurrence = build_matrix_recurrence *)
  (* List.iter !best_outer_coefficient *)
  
  let handle_candidate 
    (done_symbols,ineq_tr,blk_transforms,blk_adds,term_of_id) 
    (target_outer_sym,target_inner_sym,outer_coeff,blk_transform,blk_add) = 
    if not (Srk.Syntax.Symbol.Set.mem target_outer_sym done_symbols) &&
      (QQ.equal outer_coeff
       (Srk.Syntax.Symbol.Map.find target_outer_sym !best_outer_coefficient))
    then 
      (Srk.Syntax.Symbol.Set.add target_outer_sym done_symbols,
       (target_inner_sym, target_outer_sym)::ineq_tr,
       blk_transform::blk_transforms,
       blk_add::blk_adds,
       (Srk.Syntax.mk_const Cra.srk target_inner_sym)::term_of_id) 
    else 
      (done_symbols,ineq_tr,blk_transforms,blk_adds,term_of_id) in 
  let done_symbols,ineq_tr,blk_transforms,blk_adds,term_of_id =
    List.fold_left handle_candidate 
      (Srk.Syntax.Symbol.Set.empty, [],[],[],[]) !recurrence_candidates in 
  let term_of_id = Array.of_list (List.rev term_of_id) in 
  let loop_counter_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"K" `TyInt in
  let loop_counter = Srk.Syntax.mk_const Cra.srk loop_counter_sym in
  let nb_constants = 0 in 
  (* Change to pairs of transform_add blocks *)
  (* Add the appropriate constraint to the loop counter, so K >= 0 *)
  let solution = SolvablePolynomial.exp_ocrs_external 
                  Cra.srk ineq_tr loop_counter term_of_id 
                  nb_constants blk_transforms blk_adds in 
  Format.printf "@.    solution: %a@." 
      (Srk.Syntax.Formula.pp Cra.srk) solution
  (* *)
    



    

(*
            let closure iter =
            let srk = iter.srk in
            let loop_counter_sym = mk_symbol srk ~name:"K" `TyInt in
            let loop_counter = mk_const srk loop_counter_sym in
            mk_and srk [Iter.exp iter.srk iter.tr_symbols loop_counter iter.iter;
                        mk_leq srk (mk_real srk QQ.zero) loop_counter] 
          *)

          (* Need to walk over the coeffs and dims and get a block
              which is so far just a single entry with the B_out_self coeff
              and a blk_add which is a constant polynomial with the
              constant term, if it's non-zero, otherwise the blk_add is 0.
             Also, need to build a term_of_id,
             need to craft a loop counter
             need to build tr_symbols of b_in and b_out that I'm using
             (* *)
          *)
          (*
            match accum with | None -> None | Some accum_list ->
            match BatEnum.get coeffs_and_dims with 
            | None -> Some accum_list
            | Some (coeff,dim) ->
          *)
          (* Iterate over the coefficients and dimensions of this inequation,
               checking whether various conditions apply *)


          (* BatEnum.fold (fun ) *)
          (* We check the coefficient on the target B_out symbol to determine whether
             or not this inequation constitutes an upper bound on the target B_out *)
             (*
          (if ((QQ.compare (Srk.Linear.QQVector.coeff target_outer_dim vec) QQ.zero) < 0) then 
          begin
              (*let newvec_opt = BatEnum.fold (fun newvec_opt dim ->
                match newvec_opt with None -> None | Some newvec ->
                let coeff = Srk.Linear.QQVector.coeff dim vec in 
                if dim == CoordinateSystem.const_id then
                  if (QQ.compare coeff 0 ) then 
                else if dim == target_inner_dim then 
                  (Some newvec)
                else 
                  (Some newvec))
              (Some Srk.Linear.QQVector.zero) (-1 -- (CoordinateSystem.dim sub_cs)) in *)
          (* FIXME: the following test should be made faster *)
          (*(if ((QQ.compare (Srk.Linear.QQVector.dot vec target_vec) QQ.zero) < 0) then*)
            Format.printf "  identified recurrence inequation: %a@." 
              (Srk.Syntax.Term.pp Cra.srk) term;
            (*let newvec_opt = BatEnum.fold (fun newvec dim ->
                  if dim == target_inner_dim then 
                    Srk.Linear.QQVector.coeff dim
                  newvec)
                Some vec
                (1 -- (CoordinateSystem.dim sub_cs)); *)
            (*Format.printf "  term_dimension: %d@." (CoordinateSystem.cs_term_id sub_cs (`App (inner_sym, [])));*)
            (* Iterate over the usable inequations, and check:
                 - Check conditions of stratification
                 - Check conditions of interdependence
            *)
            (* Need to produce: 
               - 
            *)
            (* Note: use subterm, not exists, eventually... *)
            (* Note: worry about multiple recs per B_out *)
            (* Note: divide everything by B_out's coefficient *)
            () 
            end  
          else ()) *) 

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


