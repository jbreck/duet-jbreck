open Srk

include Log.Make(struct let name = "chora" end)

module type AuxVarModule = sig
  type val_t (* type of an auxiliary variable *)
             (*   e.g., a Cra.value; but, unit is also okay *)
  type val_sym = { 
      value: val_t; 
      symbol: Srk.Syntax.symbol
  }
  val make_aux_variable : string -> val_sym

  val post_symbol : Srk.Syntax.symbol -> Srk.Syntax.symbol

  type srk_ctx_magic
  val srk : srk_ctx_magic Srk.Syntax.context
end;;

module type ProcModule = sig
  module ProcMap : BatMap.S
  val proc_name_string : ProcMap.key -> string
  (*val proc_name_string : ProcMap.key -> string*)
end;;

module MakeChoraCore (Proc:ProcModule)(Aux:AuxVarModule) = struct
  include Proc
  include Aux

  type height_model_type = 
    (* Root to baseline of tree *)
    | RB of val_sym 
    (* Root to baseline, root to midline, midline to baseline *)
    (*   where the midline is defined as the depth of the shallowest leaf *)
    | RB_RM_MB of val_sym * val_sym * val_sym 

  open BatPervasives (* Gives you the "--" operator, maybe among other things *)

  let chora_debug_recs = ref false
  let chora_dual = ref false (* compute non-trivial lower bounds in addition to upper bounds *)
  let chora_fallback = ref false
  let chora_just_allow_decrease = ref false (* WARNING: it's unsound to set this to true *)

  let log_fmla_proc ?(level=`info) formatter proc_key formula = 
    logf ~level formatter (proc_name_string proc_key)
        (Srk.Syntax.Formula.pp srk) formula

  let upper_symbol =
    Memo.memo (fun sym ->
     Srk.Syntax.mk_symbol srk 
       ~name:("Rm_"^(Srk.Syntax.show_symbol srk sym)) 
       (Srk.Syntax.typ_symbol srk sym))
  
  let lower_symbol =
    Memo.memo (fun sym ->
     Srk.Syntax.mk_symbol srk 
       ~name:("Mb_"^(Srk.Syntax.show_symbol srk sym)) 
       (Srk.Syntax.typ_symbol srk sym))
  
  let rb_symbol =
    Memo.memo (fun sym ->
     Srk.Syntax.mk_symbol srk 
       ~name:("Rb_"^(Srk.Syntax.show_symbol srk sym)) 
       (Srk.Syntax.typ_symbol srk sym))

  type 'a bound_info = {
    bound_pairs : (Srk.Syntax.symbol * 'a Srk.Syntax.term) list;
    (*recursion_flag : Cra.value;*)
    (*call_abstraction_weight : K.t;*)
    (*tr_symbols : (Srk.Syntax.symbol * Srk.Syntax.symbol) list;*)
    call_abstraction_fmla : 'a Srk.Syntax.formula
  }

  (* This function is one of the main entrypoints of choraCore *)
  let make_hypothetical_summary base_case_fmla projection = 
    let wedge = Wedge.abstract ~exists:projection srk base_case_fmla in 
    logf ~level:`info "\n  base_case_wedge = %t \n\n" (fun f -> Wedge.pp f wedge);
    let cs = Wedge.coordinate_system wedge in 
    let bounding_atoms = ref [] in
    let bound_list = ref [] in
    let add_bounding_var vec negate =
      let vec = if negate then Srk.Linear.QQVector.negate vec else vec in 
      if CoordinateSystem.type_of_vec cs vec = `TyInt then
      begin
        let term = CoordinateSystem.term_of_vec cs vec in 
        (*logf ~level:`info "  base-case-bounded term: %a \n" (Srk.Syntax.Term.pp srk) term;*)
        (* *)
        (* Hacky Optional Behavior: Ignore CRA's auto-generated array-position and array-width variables *)
        let name = Srk.Syntax.Term.show srk term in
        match String.index_opt name '@' with | Some i -> () | None ->
        begin
          let bounding_var_sym_pair = make_aux_variable "B_in" in
          (*let bounding_var = Core.Var.mk (Core.Varinfo.mk_global "B_in" (Core.Concrete (Core.Int 32))) in 
            let bounding_var_sym = Cra.V.symbol_of (Cra.VVal bounding_var) in  *)
          let bounding_term = Srk.Syntax.mk_const srk bounding_var_sym_pair.symbol in 
          let bounding_atom = Srk.Syntax.mk_leq srk term bounding_term in 
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
    (*let rec_flag_var_sym_pair = make_aux_variable "Recursion_Flag" in *)
    (*let set_rec_flag = assign_value_to_literal rec_flag_var_sym_pair.value 1 in *)
    let call_abstraction_fmla = Srk.Syntax.mk_and srk (!bounding_atoms) in 
    (*let call_abstraction_weight = of_transition_formula tr_symbols call_abstraction_fmla in*)
      {bound_pairs = !bound_list;
       (*recursion_flag = rec_flag_var_sym_pair.value;*)
       (*call_abstraction_weight = K.mul set_rec_flag call_abstraction_weight *)(*}*)
       (*tr_symbols = tr_symbols;*)
       call_abstraction_fmla = call_abstraction_fmla}

  type 'a recurrence_collection = {
    done_symbols: int Srk.Syntax.Symbol.Map.t; (* accepted *)
    ineq_tr: (Srk.Syntax.Symbol.Map.key * Srk.Syntax.Symbol.Map.key) list;
    blk_transforms: Srk.QQ.t array array list;
    blk_adds: Srk.Polynomial.QQXs.t array list;
    term_of_id: ((srk_ctx_magic, 'a) Srk.Syntax.expr) BatDynArray.t;
    n_recs_accepted: int;
    n_recs_specified: int
  }
  
  type recurrence_candidate = {
    outer_sym: Srk.Syntax.symbol;
    inner_sym: Srk.Syntax.symbol;
    sub_cs: srk_ctx_magic Srk.CoordinateSystem.t;
    inequation: (Srk.QQ.t * int) list;
    dependencies: Srk.Syntax.symbol list (* what other same-stratum symbols does this depend on? *)
  }
  
  let accept_candidate candidate recurrences = 
    BatDynArray.add recurrences.term_of_id (Srk.Syntax.mk_const srk candidate.inner_sym);
    let new_num = recurrences.n_recs_accepted in 
    logf ~level:`trace "   Accepted candidate recurrence: inner_sym=%d rec_num=%d" (Srk.Syntax.int_of_symbol candidate.inner_sym) new_num;
    {done_symbols = 
        if Srk.Syntax.Symbol.Map.mem candidate.inner_sym recurrences.done_symbols 
        then recurrences.done_symbols
        else Srk.Syntax.Symbol.Map.add candidate.inner_sym new_num recurrences.done_symbols;
     ineq_tr = (candidate.inner_sym, candidate.outer_sym)::recurrences.ineq_tr;
     blk_transforms = recurrences.blk_transforms;
     blk_adds = recurrences.blk_adds;
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
  
  let rename_b_in_to_zero b_in_b_out_map solution = 
    let subst_b_in_with_zeros sym = 
      if is_an_inner_symbol sym b_in_b_out_map
      then Srk.Syntax.mk_real srk QQ.zero 
      else Srk.Syntax.mk_const srk sym in 
    Srk.Syntax.substitute_const srk subst_b_in_with_zeros solution 
  
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
      solution b_in_b_out_map bounds depth_bound_formula 
      proc_key = 
    (* b_in = 0: In the height-based analysis, initial b_in values equal zero *)
    let solution_starting_at_zero = rename_b_in_to_zero b_in_b_out_map solution in 
    let level = if !chora_debug_recs then `always else `info in
    log_fmla_proc ~level "@.    simplified%s: @.    %a" proc_key solution_starting_at_zero;
    (* each term <= each b_out:  *)
    let bounding_conjunction = 
      let make_bounding_conjuncts (in_sym,term) =
        let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in 
        Srk.Syntax.mk_leq srk term (Srk.Syntax.mk_const srk out_sym)
      in
      let bounding_conjuncts = 
        List.map make_bounding_conjuncts bounds.bound_pairs in 
      Srk.Syntax.mk_and srk bounding_conjuncts in 
    log_fmla_proc "@.    bddg conj%s: %a" proc_key bounding_conjunction; 
    (* depth_bound formula /\ (solution with b_in = 0) /\ each term <= each b_out *)
    let height_based_summary_fmla = 
      Srk.Syntax.mk_and srk [depth_bound_formula; 
                                 solution_starting_at_zero;
                                 bounding_conjunction] in
    log_fmla_proc "@.    HBA_summary_fmla%s: %a" proc_key height_based_summary_fmla; 
    height_based_summary_fmla
  
  let substitute_one_sym formula old_sym new_sym =  
    let subst_rule sym = 
      if sym == old_sym 
      then Srk.Syntax.mk_const srk new_sym  
      else Srk.Syntax.mk_const srk sym in
    Srk.Syntax.substitute_const srk subst_rule formula
  
  let lower_some_symbols formula excepting = 
    let subst_rule sym = 
      if Srk.Syntax.Symbol.Set.mem sym excepting 
      then Srk.Syntax.mk_const srk sym
      else Srk.Syntax.mk_const srk (lower_symbol sym) in 
    Srk.Syntax.substitute_const srk subst_rule formula
  
  let upper_some_symbols formula excepting = 
    let subst_rule sym = 
      if Srk.Syntax.Symbol.Set.mem sym excepting 
      then Srk.Syntax.mk_const srk sym
      else Srk.Syntax.mk_const srk (upper_symbol sym) in 
    Srk.Syntax.substitute_const srk subst_rule formula
  
  let rb_some_symbols formula excepting = 
    let subst_rule sym = 
      if Srk.Syntax.Symbol.Set.mem sym excepting 
      then Srk.Syntax.mk_const srk sym
      else Srk.Syntax.mk_const srk (rb_symbol sym) in 
    Srk.Syntax.substitute_const srk subst_rule formula
  
  (* In this function, we build up a bunch of formulas F1...F8 and then
       we conjoin them.  To ensure that the different conjuncts are "wired
       together" correctly, we do a lot of renaming the symbols in the
       different formulas so that the ones that are supposed to talk to
       each other do so, and the ones that aren't don't. *)
  let build_dual_height_summary 
        rb rm mb rm_solution mb_solution b_in_b_out_map bounds depth_bound_formula 
        excepting proc_key height_model = 
    (* F1: rb depth-bound formula (Root-->Baseline), serving to constrain rb *)
    let rb_depthbound = lower_some_symbols depth_bound_formula excepting in
    log_fmla_proc "@.    rb_dbf%s: %a" proc_key rb_depthbound;
    (* F2: rm depth-bound formula (Root-->Midline), serving to constrain rm *)
    let rm_depthbound = substitute_one_sym 
      depth_bound_formula (post_symbol rb.symbol) (post_symbol rm.symbol) in
    let rm_depthbound = upper_some_symbols rm_depthbound excepting in
    log_fmla_proc "@.    rm_dbf%s: %a" proc_key rm_depthbound;
    (* F3: height equation: rb = rm + mb*)
    let rb_const = Srk.Syntax.mk_const srk (post_symbol rb.symbol) in 
    let rm_const = Srk.Syntax.mk_const srk (post_symbol rm.symbol) in 
    let mb_const = Srk.Syntax.mk_const srk (post_symbol mb.symbol) in 
    let height_eq = Srk.Syntax.mk_eq srk rb_const
      (Srk.Syntax.mk_add srk [rm_const; mb_const]) in
    log_fmla_proc "@.    ht_eq%s: %a" proc_key height_eq;
    (* F3: height inequation: rm <= rb *)
    let height_ineq = Srk.Syntax.mk_leq srk rm_const rb_const in
    log_fmla_proc "@.    ht_ineq%s: %a" proc_key height_ineq;
    (* F5: mb solution relating mb, b_in_low, b_out_low, with b_in_low = 0 *)
    let original_mb_solution = mb_solution in 
    let mb_solution = rename_b_in_to_zero b_in_b_out_map mb_solution in 
    let mb_solution = lower_some_symbols mb_solution excepting in
    log_fmla_proc "@.    mb_simplified%s: %a" proc_key mb_solution;
    (* F6: rm solution relating rm, b_in_up, b_out_up *)
    let rm_solution = upper_some_symbols rm_solution excepting in
    log_fmla_proc "@.    rm_unsimplified%s: %a" proc_key rm_solution;
    (* F7: bound_upper: each prog. var. term <= each b_out_up:  *)
    let bound_upper = 
      let make_bounding_conjuncts (in_sym,term) =
        let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in 
        Srk.Syntax.mk_leq srk term (Srk.Syntax.mk_const srk out_sym) in
      let bounding_conjuncts = 
        List.map make_bounding_conjuncts bounds.bound_pairs in 
      Srk.Syntax.mk_and srk bounding_conjuncts in 
    let bound_upper = upper_some_symbols bound_upper excepting in 
    log_fmla_proc "@.    bd_up conj%s: %a" proc_key bound_upper;
    (* F8: bound_bridge: 0 <= b_in_up /\ b_in_up <= b_out_low *)
    let bound_bridge = 
      let make_bridging_conjuncts in_sym =
        let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in
        let up_in_const = Srk.Syntax.mk_const srk (upper_symbol in_sym) in 
        let low_out_const = Srk.Syntax.mk_const srk (lower_symbol out_sym) in
        let zero = Srk.Syntax.mk_real srk QQ.zero in
        Srk.Syntax.mk_and srk
          [Srk.Syntax.mk_leq srk zero up_in_const;
           Srk.Syntax.mk_leq srk up_in_const low_out_const] in
      let scc_b_in_symbols = 
        Srk.Syntax.Symbol.Map.fold
          (fun in_sym _ rest -> in_sym::rest)
          b_in_b_out_map
          [] in 
      let bridging_conjuncts = 
        List.map make_bridging_conjuncts scc_b_in_symbols in 
      Srk.Syntax.mk_and srk bridging_conjuncts in 
    log_fmla_proc "@.    bd_bridge conj%s: %a" proc_key bound_bridge;
    let first_part = [rb_depthbound;rm_depthbound;height_eq;height_ineq] in
    let last_part = [mb_solution;bound_bridge;rm_solution;bound_upper] in
    (* ===== Optional "Fallback" to height-based analysis ===== *)
    (* F9(optional) bound_rb: each prog. var. term <= each b_out_rb *)
    let fallback = if !chora_fallback then begin
      let bound_rb = 
        let make_bounding_conjuncts (in_sym,term) =
          let out_sym = Srk.Syntax.Symbol.Map.find in_sym b_in_b_out_map in 
          Srk.Syntax.mk_leq srk term (Srk.Syntax.mk_const srk out_sym) in
        let bounding_conjuncts = 
          List.map make_bounding_conjuncts bounds.bound_pairs in 
        Srk.Syntax.mk_and srk bounding_conjuncts in 
      let bound_rb = rb_some_symbols bound_rb excepting in 
      log_fmla_proc "@.    bd_rb conj%s: %a" proc_key bound_rb;
      (* F10(optional) rb solution relating rb, b_in_rb, b_out_rb with b_in_rb=0 *)
      let rb_solution = substitute_one_sym 
        original_mb_solution (post_symbol mb.symbol) (post_symbol rb.symbol) in
      let rb_solution = rename_b_in_to_zero b_in_b_out_map rb_solution in 
      let rb_solution = rb_some_symbols rb_solution excepting in
      log_fmla_proc "@.    rb_simplified%s: %a" proc_key rb_solution;
      [bound_rb;rb_solution]
    end else [] in 
    (* ==============  End of Fallback section   ============== *)
    (* big_conjunction *)
    let dual_height_summary_fmla = Srk.Syntax.mk_and srk 
      (first_part @ fallback @ last_part) in
    log_fmla_proc "@.    DHA conj%s: %a" proc_key dual_height_summary_fmla; 
    dual_height_summary_fmla
  
  let sanity_check_recurrences recurrences term_of_id = 
    (if not ((List.length recurrences.blk_transforms) ==
             (List.length recurrences.blk_adds)) then
       failwith "Matrix recurrence transform/add blocks mismatched.");
    let print_expr i term = 
        logf ~level:`trace "  term_of_id[%d]=%a" i (Srk.Syntax.Expr.pp srk) term in
    let pp_dim f i = 
        Format.fprintf f "%a" (Srk.Syntax.Expr.pp srk) (term_of_id.(i)) in
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
      (fun f -> Srk.Syntax.pp_symbol srk f target_inner_sym);*)
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
    if not (CoordinateSystem.admits sub_cs (Srk.Syntax.mk_const srk target_inner_sym)) then () else
    if not (CoordinateSystem.admits sub_cs (Srk.Syntax.mk_const srk target_outer_sym)) then () else
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
        logf ~level:lev "  [PRE-REC] %a" (Srk.Syntax.Term.pp srk) term);
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
    let outer_sym = Srk.Syntax.mk_symbol srk ~name:"B_out" `TyInt in
    let lhs = Srk.Syntax.mk_const srk outer_sym in 
    let rhs = term in 
    let b_out_constraint = 
      (* Drop any b_outs associated with terms that we don't know to be ints *)
      if Srk.Syntax.term_typ srk term = `TyInt then
        ((let lev = if !chora_debug_recs then `always else `info in
          logf ~level:lev "  [TERM]: %a  @@{h}:  %t  @@{h+1}:  %t " 
          (Srk.Syntax.Term.pp srk) term
          (fun f -> Srk.Syntax.pp_symbol srk f inner_sym)
          (fun f -> Srk.Syntax.pp_symbol srk f outer_sym));
          (* B_out <= term *)
          Srk.Syntax.mk_leq srk lhs rhs)
      else (let lev = if !chora_debug_recs then `always else `info in 
          logf ~level:lev "  Note: dropped a real term ";
          (* B_out = ? *)
          Srk.Syntax.mk_true srk) in
    (*local_b_out_definitions := b_out_constraint :: (!local_b_out_definitions);
    b_in_b_out_map := Srk.Syntax.Symbol.Map.add inner_sym outer_sym !b_in_b_out_map;
    b_out_symbols := Srk.Syntax.Symbol.Set.add outer_sym (!b_out_symbols) in*)
    (b_out_constraint :: local_b_out_definitions,
     Srk.Syntax.Symbol.Map.add inner_sym outer_sym b_in_b_out_map,
     Srk.Syntax.Symbol.Set.add outer_sym b_out_symbols)
  
  (* Called once per proc *)
  let make_outer_bounding_symbols_for_proc 
      bounds b_in_b_out_map b_out_symbols =
    logf ~level:`info "[Chora] Listing bounded terms:";
    let (local_b_out_definitions, b_in_b_out_map, b_out_symbols) =
      List.fold_left 
        make_outer_bounding_symbol
        ([], b_in_b_out_map, b_out_symbols)
        bounds.bound_pairs in
    logf ~level:`trace "        Finished with bounded terms.";
    let lev = if !chora_debug_recs then `always else `info in
    logf ~level:lev "  ";
    (local_b_out_definitions, b_in_b_out_map, b_out_symbols)
  
  (* Called once per SCC *)
  let make_outer_bounding_symbols proc_key_list bounds_map =
    let b_in_b_out_map = Srk.Syntax.Symbol.Map.empty in 
    let b_out_symbols = Srk.Syntax.Symbol.Set.empty in
    let b_out_definitions_map = ProcMap.empty in 
    List.fold_left 
      (fun 
        (b_out_definitions_map, b_in_b_out_map, b_out_symbols)
        proc_key ->
        let bounds = ProcMap.find proc_key bounds_map in 
        let local_b_out_definitions, b_in_b_out_map, b_out_symbols = 
          make_outer_bounding_symbols_for_proc 
            bounds b_in_b_out_map b_out_symbols in
        let b_out_definitions_map = 
            ProcMap.add proc_key local_b_out_definitions 
              b_out_definitions_map in
        (b_out_definitions_map, b_in_b_out_map, b_out_symbols))
      (b_out_definitions_map, b_in_b_out_map, b_out_symbols)
      proc_key_list
  
  (* Called once per procedure per value of allow_decrease *)
  let make_extraction_formula 
      bounds local_b_out_definitions b_in_b_out_map 
      b_out_symbols rec_fmla ~allow_decrease =
    (* *)
    (* ----- These lines assume every b_in is non-negative. ----- *)
    (* They are only used, and only sound, when allow_decrease is false. *)
    let b_in_conjunction = 
      if allow_decrease
      then []
      else begin
           let non_negative_b_in (inner_sym, _) = 
           let lhs = Srk.Syntax.mk_real srk QQ.zero in 
           let rhs = Srk.Syntax.mk_const srk inner_sym in 
           Srk.Syntax.mk_leq srk lhs rhs in
           (* *)
           let all_b_in_non_negative = 
             List.map non_negative_b_in bounds.bound_pairs in 
           [Srk.Syntax.mk_and srk all_b_in_non_negative] 
      end in 
    (* ---------------------------------------------------------- *)
    (* *)
    let b_out_conjunction = Srk.Syntax.mk_and srk local_b_out_definitions in 
    (*logf ~level:`info "  b_out_conjunction: \n%a \n" (Srk.Syntax.Formula.pp srk) b_out_conjunction;*)
    let conjuncts = b_in_conjunction @ [rec_fmla; b_out_conjunction] in
    let extraction_formula = Srk.Syntax.mk_and srk conjuncts in 
    logf ~level:`trace "  extraction_formula: \n%a \n" (Srk.Syntax.Formula.pp srk) extraction_formula;
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
    let wedge = Wedge.abstract ~exists:projection ~subterm:projection srk extraction_formula in 
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
        (fun f -> Srk.Syntax.pp_symbol srk f target_outer_sym)
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
    (*logf ~level:`info "   Not using extraction_wedge; using formula instead"; *)
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
                        srk extraction_formula in 
      (*Wedge.strengthen sub_wedge; (* NOTE: Added just for debugging... *) *)
      (logf ~level:`trace "  sub_wedge_for[%t] = @.%t@." 
        (fun f -> Srk.Syntax.pp_symbol srk f target_outer_sym)
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
    let loop_counter = Srk.Syntax.mk_const srk post_height_sym in
    let nb_constants = 0 in
    let solution = SolvablePolynomial.exp_ocrs_external 
                    srk recurrences.ineq_tr loop_counter term_of_id 
                    nb_constants recurrences.blk_transforms 
                    recurrences.blk_adds in 
    logf ~level:`info "@.    solution: %a" 
        (Srk.Syntax.Formula.pp srk) solution;
    (* *)
    solution
  
  (* Called once per SCC per value of allow_decrease *)
  let build_wedge_map 
        b_out_definitions_map b_in_b_out_map b_out_symbols bounds_map 
        depth_bound_formula_map proc_key_list rec_fmla_map ~allow_decrease =
    (* For each procedure, create a transition formula for use in extraction *)
    let extraction_formula_map = 
      List.fold_left 
        (fun extraction_formula_map proc_key ->
          let bounds = ProcMap.find proc_key bounds_map in 
          let rec_fmla = ProcMap.find proc_key rec_fmla_map in 
          let local_b_out_definitions = 
            ProcMap.find proc_key b_out_definitions_map in 
          let extraction_formula = 
            make_extraction_formula 
              bounds local_b_out_definitions
              b_in_b_out_map b_out_symbols rec_fmla ~allow_decrease in
          ProcMap.add proc_key extraction_formula extraction_formula_map)
      ProcMap.empty
      proc_key_list in 
    (* For each procedure, create a wedge for use in extraction *)
    let wedge_map = 
      List.fold_left (fun wedge_map proc_key ->
        let extraction_formula = 
            ProcMap.find proc_key extraction_formula_map in 
        let bounds = ProcMap.find proc_key bounds_map in 
        make_extraction_wedges_from_formula
          extraction_formula bounds b_in_b_out_map b_out_symbols wedge_map)
      Srk.Syntax.Symbol.Map.empty
      proc_key_list in 
    wedge_map
  
  (* Called once per SCC per value of allow_decrease *)
  let build_wedges_and_extract_recurrences 
        b_out_definitions_map b_in_b_out_map b_out_symbols 
        bounds_map depth_bound_formula_map 
        proc_key_list post_height_sym rec_fmla_map ~allow_decrease =
    let wedge_map = build_wedge_map
      b_out_definitions_map b_in_b_out_map b_out_symbols 
      bounds_map depth_bound_formula_map 
      proc_key_list rec_fmla_map ~allow_decrease in
    extract_and_solve_recurrences 
      b_in_b_out_map wedge_map post_height_sym ~allow_decrease
    (* returns solution *)
 
  (* This function is one of the main entrypoints of choraCore *)
  let make_height_based_summaries
        rec_fmla_map bounds_map depth_bound_formula_map 
        proc_key_list height_model excepting =
    (* *)
    let (b_out_definitions_map, b_in_b_out_map, b_out_symbols) = 
      make_outer_bounding_symbols proc_key_list bounds_map in 
    match height_model with 
    (* *********************************************************************** *)
    (* ********                Height-based Analysis                  ******** *)
    | RB rb -> 
      begin
      assert (not !chora_dual);
      (* ---------- Extract and solve recurrences --------- *)
      let solution = build_wedges_and_extract_recurrences 
        b_out_definitions_map b_in_b_out_map b_out_symbols 
        bounds_map depth_bound_formula_map 
        proc_key_list (post_symbol rb.symbol) rec_fmla_map ~allow_decrease:!chora_just_allow_decrease in
      (* ---------- Build summaries using recurrence solution --------- *)
      let summary_list = 
        List.fold_left (fun sums proc_key ->
          let depth_bound_formula = 
              ProcMap.find proc_key depth_bound_formula_map in 
          let bounds = ProcMap.find proc_key bounds_map in 
          let summary = build_height_based_summary 
            solution b_in_b_out_map bounds depth_bound_formula proc_key in
          (proc_key,summary)::sums)
        []
        proc_key_list in 
      summary_list
      end
    (* *********************************************************************** *)
    (* ********                 Dual-height Analysis                  ******** *)
    | RB_RM_MB (rb, rm, mb) -> 
      begin 
      assert (!chora_dual);
      (* ---------- Extract and solve recurrences --------- *)
      let rm_solution = build_wedges_and_extract_recurrences 
        b_out_definitions_map b_in_b_out_map b_out_symbols 
        bounds_map depth_bound_formula_map 
        proc_key_list (post_symbol rm.symbol) rec_fmla_map ~allow_decrease:true in
      (* *)
      let mb_solution = build_wedges_and_extract_recurrences 
        b_out_definitions_map b_in_b_out_map b_out_symbols 
        bounds_map depth_bound_formula_map 
        proc_key_list (post_symbol mb.symbol) rec_fmla_map ~allow_decrease:false in
      (* ---------- Build summaries using recurrence solution --------- *)
      let summary_list = 
        List.fold_left (fun sums proc_key ->
          let depth_bound_formula = 
              ProcMap.find proc_key depth_bound_formula_map in 
          let bounds = ProcMap.find proc_key bounds_map in 
          let summary = build_dual_height_summary
            rb rm mb rm_solution mb_solution b_in_b_out_map bounds 
            depth_bound_formula excepting proc_key 
            height_model in
          (proc_key,summary)::sums)
        []
        proc_key_list in 
      summary_list
      end
  ;;

end (* End of MakeChoraCore functor *)


