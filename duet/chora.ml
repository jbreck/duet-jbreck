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
      logf ~level:`info "%s"
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

(*let debug_print_wedge_of_transition tr = 
  let (tr_symbols, body) = to_transition_formula tr in
  let projection x = 
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false tr_symbols)
    || 
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false (* false *)
  in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk body in 
  logf ~level:`info "\n  wedgified for debugging = %t \n\n" (fun f -> Wedge.pp f wedge)*)

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
  logf ~level:`trace "   Accepted candidate recurrence: inner_sym=%d rec_num=%d@." (Srk.Syntax.int_of_symbol candidate.inner_sym) new_num;
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
  Srk.Syntax.Symbol.Map.fold
    (fun sym recurrence_number old_map -> 
      let sub_dim = (CoordinateSystem.cs_term_id sub_cs (`App (sym, []))) in 
      BatMap.Int.add sub_dim (recurrence_number) old_map)
    recurrences.done_symbols
    BatMap.Int.empty 

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
  logf ~level:`trace "   blk_start %d@.   max_rec_number %d@.   inner_rec_num %d@.   nb_recs_in_block %d@.   blk_last %d@.   target_inner_sym %d@." 
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
            (* REV: I write blk_last-x here so that I flip the recurrences backwards to match term_of_id *)
            (blk_transform.(blk_last-(inner_rec_num-blk_start)).(blk_last-(rec_num-blk_start)) <- coeff;
            poly)
        end
      else (failwith "Unrecognized component of recurrence inequation"))
    const_add_poly
    new_coeffs_and_dims in 
  blk_add_entry;;

let mk_height_based_summary 
  bounds recursive_weight top_down_summary ht_var_sym program_vars base top =  
  (* FIXME add a base case to the top_down? *)
  (* Note: this use of top is a hack; this top isn't really top; it's really
       havoc-all-program-vars; that is, it doesn't havoc the height variable H *)
  (* Make a formula from top_down_summary and get the post-state height symbol *)
  let top_down_symbols, top_down_formula = 
    K.to_transition_formula (K.mul (K.mul top_down_summary base) top) in
  logf ~level:`info "@.  tdf: %a@." 
      (Srk.Syntax.Formula.pp Cra.srk) top_down_formula; 
  let is_post_height (pre_sym,post_sym) = (pre_sym == ht_var_sym) in 
  let post_height_sym = 
    try snd (List.find is_post_height top_down_symbols) 
    with Not_found -> failwith "CRA-Nonlinrec: Failed to find post-height symbol" in 
  (* REMOVE BASE CASE *)
  let initially_no_recursion = (assign_value_to_literal bounds.recursion_flag 0) in 
  let eventually_recursion = (assume_value_eq_literal bounds.recursion_flag 1) in 
  let recursive_weight = 
    K.mul (K.mul initially_no_recursion recursive_weight) eventually_recursion in
  (* ASSUME B_in NON-NEGATIVE*)
  let (tr_symbols, body) = to_transition_formula recursive_weight in
  logf ~level:`info "  transition_formula_body: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) body;
  let b_out_definitions = ref [] in 
  let b_in_b_out_pairs = ref [] in 
  let b_in_b_out_map = ref Srk.Syntax.Symbol.Map.empty in 
  let b_in_symbols = ref Srk.Syntax.Symbol.Set.empty in 
  let b_out_symbols = ref Srk.Syntax.Symbol.Set.empty in 
  let add_b_out_definition (inner_sym, term) =
    let outer_sym = Srk.Syntax.mk_symbol Cra.srk ~name:"B_out" `TyInt in
    let lhs = Srk.Syntax.mk_const Cra.srk outer_sym in 
    (*let lhs = Srk.Syntax.mk_const Cra.srk sym in *) 
    let rhs = term in 
    let b_out_constraint = Srk.Syntax.mk_leq Cra.srk lhs rhs in (* was: mk_eq *)
    logf ~level:`info "  [TERM]: %a ~ %t ~ %t @." 
      (Srk.Syntax.Term.pp Cra.srk) term
      (fun f -> Srk.Syntax.pp_symbol Cra.srk f inner_sym)
      (fun f -> Srk.Syntax.pp_symbol Cra.srk f outer_sym);
    b_out_definitions := b_out_constraint :: (!b_out_definitions);
    b_in_b_out_pairs := (inner_sym, outer_sym) :: (!b_in_b_out_pairs);
    b_in_b_out_map := Srk.Syntax.Symbol.Map.add inner_sym outer_sym !b_in_b_out_map;
    b_in_symbols  := Srk.Syntax.Symbol.Set.add inner_sym (!b_in_symbols);
    b_out_symbols := Srk.Syntax.Symbol.Set.add outer_sym (!b_out_symbols) in 
  logf ~level:`info "[Chora] Finding bounded terms:@.";
  List.iter add_b_out_definition bounds.bound_pairs; 
  logf ~level:`trace "        Finished bounded terms.@.";
  let b_out_conjunction = Srk.Syntax.mk_and Cra.srk (!b_out_definitions) in 
  (*logf ~level:`info "  b_out_conjunction: \n%a \n" (Srk.Syntax.Formula.pp Cra.srk) b_out_conjunction;*)
  let full_conjunction = Srk.Syntax.mk_and Cra.srk [body; b_out_conjunction] in 
  let projection sym = 
    Srk.Syntax.Symbol.Set.mem sym !b_in_symbols || 
    Srk.Syntax.Symbol.Set.mem sym !b_out_symbols in 
  let wedge = Wedge.abstract ~exists:projection Cra.srk full_conjunction in 
  logf ~level:`info "  extraction_wedge = @.%t@. @.@." (fun f -> Wedge.pp f wedge); 
  (* *)
  let recurrence_candidates = ref [] in
  (*let best_self_coefficient = ref Srk.Syntax.Symbol.Map.empty in *)
  (* 
      CHANGES NEEDED:
        * improve/replace our use of wedge projections
  *)
  (* let target_vec = CoordinateSystem.vec_of_term sub_cs (Srk.Syntax.mk_const Cra.srk target_outer_sym) in *)
  (* For each outer bounding symbol (B_out), project the wedge down to that outer
       symbol and all inner bounding symbols *)
  (* Note: we do all projections together, before the stratum-loop *)
  (* Change this to iterate over b_in_symbols, maybe? *)
  logf ~level:`trace "  Building wedge map...@."; 
  let wedge_map = 
    let add_wedge_to_map map (target_inner_sym, _) = 
      let target_outer_sym = Srk.Syntax.Symbol.Map.find target_inner_sym !b_in_b_out_map in
      let targeted_projection sym = 
        sym == target_outer_sym || Srk.Syntax.Symbol.Set.mem sym !b_in_symbols in 
      (* Project this wedge down to a sub_wedge that uses only this B_out and some B_ins *)
      let sub_wedge = Wedge.exists targeted_projection wedge in 
      Srk.Syntax.Symbol.Map.add target_inner_sym sub_wedge map in 
    List.fold_left 
      add_wedge_to_map 
      Srk.Syntax.Symbol.Map.empty
      bounds.bound_pairs in 
  logf ~level:`trace "  Finished wedge map.@."; 
  (* *)
  let is_negative q = ((QQ.compare q QQ.zero) < 0) in
  let is_non_negative q = ((QQ.compare q QQ.zero) >= 0) in
  (*let is_at_least_one q = ((QQ.compare q QQ.one) >= 0) in*)
  let have_recurrence sym recurrences = 
    Srk.Syntax.Symbol.Map.mem sym recurrences.done_symbols in
  (* There's a need for an outer loop for stratification levels, although we 
    should avoid redoing the expensive steps.  *)
  (* *)
  (* These loops could be changed to have a simpler, faster structure... *)
  (* *)
  (* This function is applied twice for each stratification level:
      first looking for non-interdependent variables and
      a second time allowing for interdependent variables *)
  let rec extract_recurrences recurrences allow_interdependence = 
    begin
    let nb_previous_recurrences = count_recurrences recurrences in 
    (* Change this to iterate over b_in_symbols, maybe? *)
    (* *) 
    (* This function is applied to each B_in symbol *) 
    let extract_recurrence_for_symbol (target_inner_sym, _) = 
      (*logf ~level:`info "  Attempting extraction for %t DELETEME.@." 
        (fun f -> Srk.Syntax.pp_symbol Cra.srk f target_inner_sym);*)
      (* First, check whether we've already extracted a recurrence for this symbol *)
      if have_recurrence target_inner_sym recurrences then () else 
      if not (Srk.Syntax.Symbol.Map.mem target_inner_sym !b_in_b_out_map) then () else 
      if not (Srk.Syntax.Symbol.Map.mem target_inner_sym wedge_map) then () else 
      let target_outer_sym = Srk.Syntax.Symbol.Map.find target_inner_sym !b_in_b_out_map in
      let sub_wedge = Srk.Syntax.Symbol.Map.find target_inner_sym wedge_map in 
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
            else if Srk.Syntax.Symbol.Set.mem sym !b_in_symbols then
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
          logf ~level:`trace "  Found a possible inequation...DELETEME@.";
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
          logf ~level:`info "  [REC] %a@." (Srk.Syntax.Term.pp Cra.srk) term;  
          logf ~level:`trace "    before filter: %a @." Linear.QQVector.pp vec;
          logf ~level:`trace "     after filter: %a @." Linear.QQVector.pp new_vec;
          let one_over_outer_coeff = QQ.inverse outer_coeff in 
          let new_vec = Linear.QQVector.scalar_mul one_over_outer_coeff new_vec in 
          let inner_coeff = Linear.QQVector.coeff target_inner_dim new_vec in 
          logf ~level:`trace "      inner_coeff: %a @." QQ.pp inner_coeff;  

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
      in
    logf ~level:`trace "[Chora] Recurrence extraction:@.";
    List.iter extract_recurrence_for_symbol bounds.bound_pairs;
    logf ~level:`trace "        Finished recurrence extraction. DELETEME@.";
    (* *)
    (* 
    (* Scan for the lowest self-coefficent that each B_out has*)
    let find_best_self_coefficient candidate = 
      let old_coeff = Srk.Syntax.Symbol.Map.find_default 
        (QQ.add candidate.coeff QQ.one) 
        candidate.outer_sym 
        !best_self_coefficient in 
      if (QQ.compare candidate.coeff old_coeff) <= 0 then 
        best_self_coefficient := 
          Srk.Syntax.Symbol.Map.add 
          candidate.outer_sym 
          candidate.coeff 
          !best_self_coefficient
      in 
    List.iter find_best_self_coefficient !recurrence_candidates;
    *)
    (* *)
    (* PHASE: filter out recurrences having unmet dependencies  *)
    (*        AND in the future maybe prioritize recurrences    *)
    (*   Don't extract more than one recurrence for each symbol *)
    let rec filter_candidates () =
      logf ~level:`trace "  Filtering recurrence candidates DELETEME @.";
      begin
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
          result 
          in 
          (*
          List.fold_left (fun ok dep -> let result = ok && 
              (not (Srk.Syntax.Symbol.Set.mem recur.inner_sym !earlier_candidates)) 
              in 
              earlier_candidates := 
                Srk.Syntax.Symbol.Set.add recur.inner_sym !earlier_candidates; 
              result) 
            true 
            recur.dependencies in 
          *)
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
        then filter_candidates ()
      end in 
    (*logf ~level:`info "  N candidates before filter: %d@." (List.length !recurrence_candidates);*)
    filter_candidates ();
    (*logf ~level:`info "  N candidates after filter:  %d@." (List.length !recurrence_candidates);*)
    
    (* PHASE: accept remaining recurrence candidates *) 
    let foreach_candidate_accept recurrences candidate = 
      accept_candidate candidate recurrences in 
    let recurrences = 
      List.fold_left 
        foreach_candidate_accept recurrences !recurrence_candidates in 
      
    (* PHASE: build recurrence matrices *) 
    let foreach_block_build recurrences candidate_block = 
      if List.length candidate_block = 0 then recurrences else
      let nRecurs = List.length candidate_block in 
      (*logf ~level:`info "  Beginning a block of size: %d@." (nRecurs);*)
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
      (*logf ~level:`info "  Registering add block of size: %d@." (Array.length blk_add);*)
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
    logf ~level:`trace "  [ -- end of stratum -- ]@.";
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
  (*let term_of_id = Array.of_list (List.rev recurrences.rev_term_of_id) in *)
  let term_of_id = BatDynArray.to_array recurrences.term_of_id in 
  let loop_counter = Srk.Syntax.mk_const Cra.srk post_height_sym in
  let nb_constants = (* just inserting a test print *)
          0 (*(logf ~level:`info "      got here@."; 0)*)
  in
  (* Sanity check sizes... *)
  (if not ((List.length recurrences.blk_transforms) ==
           (List.length recurrences.blk_adds)) then
     failwith "Matrix recurrence transform/add blocks mismatched.");
  let print_expr i term = 
      logf ~level:`trace "  term_of_id[%d]=%a @." i (Srk.Syntax.Expr.pp Cra.srk) term in
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
  List.iter2 check_block_sizes recurrences.blk_transforms recurrences.blk_adds;
  (* *)
  (* Change to pairs of transform_add blocks *)
  (* Add the appropriate constraint to the loop counter, so K >= 0 *)
  (* Send the matrix recurrence to OCRS and obtain a solution *)
  logf ~level:`trace "@.    Sending to OCRS [DELETEME]@.";
  let solution = SolvablePolynomial.exp_ocrs_external 
                  Cra.srk recurrences.ineq_tr loop_counter term_of_id 
                  nb_constants recurrences.blk_transforms 
                  recurrences.blk_adds in 
  logf ~level:`info "@.    solution: %a@." 
      (Srk.Syntax.Formula.pp Cra.srk) solution;
  (* *)
  let subst_b_in_with_zeros sym = 
    if Srk.Syntax.Symbol.Set.mem sym !b_in_symbols 
    then Srk.Syntax.mk_real Cra.srk QQ.zero 
    else Srk.Syntax.mk_const Cra.srk sym in 
  let solution_starting_at_zero = 
    Srk.Syntax.substitute_const Cra.srk subst_b_in_with_zeros solution in 
  (* let simpler = SrkSimplify.simplify_terms Cra.srk with_zeros in *)
  logf ~level:`info "@.    simplified: %a@." 
      (Srk.Syntax.Formula.pp Cra.srk) solution_starting_at_zero;
  let bounding_conjunction = 
    let make_bounding_conjuncts (in_sym,term) =
      let out_sym = Srk.Syntax.Symbol.Map.find in_sym !b_in_b_out_map in 
      (* let subst_post sym = Srk.Syntax.mk_const Cra.srk (post_symbol sym) in 
      let post_term = Srk.Syntax.substitute_const Cra.srk subst_post term in *)
      Srk.Syntax.mk_leq Cra.srk term (Srk.Syntax.mk_const Cra.srk out_sym)
    in
    let bounding_conjuncts = 
      List.map make_bounding_conjuncts bounds.bound_pairs in 
    Srk.Syntax.mk_and Cra.srk bounding_conjuncts in 
  logf ~level:`info "@.    bddg conj: %a@." 
      (Srk.Syntax.Formula.pp Cra.srk) bounding_conjunction; 
  let big_conjunction = 
    Srk.Syntax.mk_and Cra.srk [top_down_formula; 
                               solution_starting_at_zero;
                               bounding_conjunction] in
  logf ~level:`info "@.    big conj: %a@." 
      (Srk.Syntax.Formula.pp Cra.srk) big_conjunction; 
  (* FIXME: I should really be iterating over the SCC footprint variables,
            not over the list of all program variables. *)
  let final_tr_symbols = 
    List.map (fun var -> 
      let pre_sym = Cra.V.symbol_of var in 
      let post_sym = post_symbol pre_sym in 
      (pre_sym,post_sym) ) program_vars in 
  let height_based_summary = of_transition_formula final_tr_symbols big_conjunction in 
  logf ~level:`info "@.    ht_summary = ";
  print_indented 17 height_based_summary;
  logf ~level:`info "\n";
  let projection x = 
    (List.fold_left (fun found (vpre,vpost) -> found || vpre == x || vpost == x) false final_tr_symbols)
    (*||
    match Cra.V.of_symbol x with 
    | Some v -> Cra.V.is_global v
    | None -> false*)
  in 
  let wedge_summary = Wedge.abstract ~exists:projection Cra.srk big_conjunction in 
  logf ~level:`info "\n    wedgified = %t \n\n" (fun f -> Wedge.pp f wedge_summary);
  height_based_summary
  (* Things to do: 
     - construct a havoc-like transition with post variables,
        but use the solution as a guard
     - the guard needs to be a conjunction of the terms in the
        B_out definitions, but with things postified
     - and I'm constructing a new inequation in each case...
     - MAKE SURE to havoc the B_out variables themselves!
        (by putting them into the transform) *)
;;

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
  let call_edges = eval pe_call_edge_set pathexpr in 
  logf ~level:`info "  calls = [ ";
  IntPairSet.iter (fun (s,t) -> logf ~level:`info "(%d,%d) " s t) call_edges;
  logf ~level:`info "]\n";
  call_edges

let make_top_down_summary p_entry path_weight_internal top call_edges = 
  let height_var = Core.Var.mk (Core.Varinfo.mk_global "H" (Core.Concrete (Core.Int 32))) in 
  let height_var_val = Cra.VVal height_var in 
  let height_var_sym = Cra.V.symbol_of height_var_val in 
  let set_height_zero = assign_value_to_literal height_var_val 0 in 
  let increment_height = increment_variable height_var_val in 
  let weight_of_call_top cs ct cen cex = project top in 
  logf ~level:`info "  fragments = [";
  let sum_of_fragments = IntPairSet.fold (fun (s,t) running_total -> 
    let fragment_weight = path_weight_internal p_entry s weight_of_call_top in
    (* (logf ~level:`info "  << %t >> \n" (fun f -> Pathexpr.pp f fragment_weight)) *)
    (* Format.fprintf Format.std_formatter "<<( %a )>> \n" K.pp fragment_weight *)
    print_indented 15 fragment_weight;
    logf ~level:`info "\n";
    K.add running_total fragment_weight
    ) call_edges K.zero in
  logf ~level:`info "  ]\n";
  let phi_td = K.mul set_height_zero (K.star (K.mul increment_height sum_of_fragments)) in
  logf ~level:`info "  phi_td = [";
  print_indented 15 phi_td;
  logf ~level:`info "  ]\n";
  phi_td, height_var_sym;;

let analyze_chora file =
  Cra.populate_offset_table file;
  match file.entry_points with
  | [main] -> begin
    let rg = Interproc.make_recgraph file in
    let (ts, assertions) = Cra.make_transition_system rg in
    let program_vars = 
      let open CfgIr in let file = get_gfile() in
      (*List.iter (fun vi -> (logf ~level:`info "       var %t @." (fun f -> Varinfo.pp f vi))) file.vars; *)
      (* let vars = List.filter (fun vi -> not (CfgIr.defined_function vi file)) file.vars in *)
      (*let vars = List.filter (fun vi -> 
        match Core.Varinfo.get_type vi with 
        | Concrete ctyp ->
          (match ctyp with 
           | Func (_,_) -> false 
           | _ -> true ) 
        | _ -> true ) file.vars in *)
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
  
      (*List.iter (fun vi -> (logf ~level:`info "  true var %t @." (fun f -> Varinfo.pp f vi))) vars;*)
      List.map (fun vi -> Cra.VVal (Core.Var.mk vi)) vars in 
    let top = K.havoc program_vars in 
    let summarizer (scc : BURG.scc) path_weight_internal = 
      logf ~level:`info "I saw an SCC:\n";
      List.iter (fun (u,v,p) -> (logf ~level:`info "  Proc(%d,%d) = %t \n" u v (fun f -> Pathexpr.pp f p))) scc.procs;
      let summaries = List.map (fun (p_entry,p_exit,pathexpr) ->
        let weight_of_call_zero cs ct cen cex = K.zero in
        let call_edges = find_recursive_calls ts pathexpr scc in 
        if IntPairSet.cardinal call_edges = 0 then 
          (p_entry,p_exit, project (path_weight_internal p_entry p_exit weight_of_call_zero))
        else 
        let (top_down_summary, ht_var_sym) = 
          make_top_down_summary p_entry path_weight_internal top call_edges in
        let base_case_weight = project (path_weight_internal p_entry p_exit weight_of_call_zero) in
        logf ~level:`info "  base_case = [";
        print_indented 15 base_case_weight;
        logf ~level:`info "  ]\n";
        (* *)
        let bounds = mk_call_abstraction base_case_weight in 
        logf ~level:`info "  call_abstration = [";
        print_indented 15 bounds.call_abstraction;
        logf ~level:`info "  ]\n";
        let weight_of_call_rec cs ct cen cex = 
          if cen == p_entry && cex == p_exit then bounds.call_abstraction
          else failwith "Mutual recursion not implemented"
        in
        let recursive_weight = path_weight_internal p_entry p_exit weight_of_call_rec in
        logf ~level:`info "  recursive_weight = [";
        print_indented 15 recursive_weight;
        logf ~level:`info "  ]\n";
        let height_based_summary = 
          mk_height_based_summary bounds recursive_weight top_down_summary ht_var_sym program_vars base_case_weight top in
        (p_entry,p_exit,height_based_summary)) scc.procs in 
      let one_summary = List.hd summaries in 
      [one_summary] in 
    (* *) 
    let query = BURG.mk_query ts summarizer in
    (* Resource-bound analysis *)
    begin
      let cost_opt =
        let open CfgIr in
        let file = get_gfile () in
        let is_cost v = (Varinfo.show v) = "__cost" in
        try
          Some (Cra.VVal (Core.Var.mk (List.find is_cost file.vars)))
        with Not_found -> None
      in
      match cost_opt with 
      | None -> (logf ~level:`info "Could not find __cost variable\n")
      | Some cost ->
        (let cost_symbol = Cra.V.symbol_of cost in
        let exists x =
          match Cra.V.of_symbol x with
          | Some v -> Core.Var.is_global (Cra.var_of_value v)
          | None -> false
        in
        Format.printf "===== Resource-Usage Bounds =====\n";
        RG.blocks rg |> BatEnum.iter (fun procedure ->
            (*Format.printf "\n";*)
            let entry = (RG.block_entry rg procedure).did in
            let exit = (RG.block_exit rg procedure).did in
            let summary = BURG.path_weight query entry exit in
            logf ~level:`info "---------------------------------\n";
            logf ~level:`info "@. -- Procedure summary for %a = @." Varinfo.pp procedure;
                print_indented 0 summary;
                logf ~level:`info "@.@.";
            (*debug_print_wedge_of_transition summary;*)
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
        )
    end;
    (* Assertion checking *)
    if Srk.SrkUtil.Int.Map.cardinal assertions > 0 then
    begin
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
      Format.printf "=================================\n";
    end

    end
  (* *)
  | _ -> assert false;;

let _ =
  CmdLine.register_pass
    ("-chora",
     analyze_chora,
     " Compositional recurrence analysis for non-linear recursion")


(* 

  Format.printf "@.  SPPR::abstract_wedge called on: @.  %t @.@." (fun f -> Wedge.pp f wedge);

  Format.printf "@.  SPPR::abstract called on: @.  %a @.@." 
      (Syntax.Formula.pp srk) phi;

  let exp srk tr_symbols loop_counter iter =
    let result = exp srk tr_symbols loop_counter iter in 
    Format.printf "@.  SPPR::exp result: @.  %a @.@." 
      (Syntax.Formula.pp srk) result;
    result

*)

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

(* HANDLING COEFFICIENTS AND DIMENSIONS *)

(* newer one: *)
(* in
if dim == target_outer_dim then (* ------------------- TARGET B_OUT *)
  (if is_negative coeff (* Did we get an upper bound on the target dimension? *)
    then UseTerm (coeff,dim)
    else DropInequation)
else if dim == target_inner_dim then (* --------------- TARGET B_IN *)
  (if is_at_least_one coeff
    then UseTerm (coeff,dim)
    else UseTerm (QQ.zero,dim)) (* Need not restrict to >=1 *)
else if dim == CoordinateSystem.const_id then (* --------- CONSTANT *)
  (if is_non_negative coeff
    then UseTerm (coeff,dim)    (* Keep non-negative constants *)
    else DropTerm)                  (* Drop negative constants *)
else if BatMap.Int.mem dim sub_dim_to_rec_num then (* LOWER STRATUM *)
  (if is_non_negative coeff
    then UseTerm (coeff,dim)    (* Keep non-negative coefficients *)
    else DropTerm)                  (* Drop negative coefficients *)
else  
  DropInequation *)



(* OLDER ONE *)

          (*if dim == target_outer_dim then (* ------------------- TARGET B_OUT *)
            (if is_negative coeff (* Did we get an upper bound on the target dimension? *)
              then Some ((coeff,dim)::accum) 
              else None)
          else if dim == target_inner_dim then (* --------------- TARGET B_IN *)
            (if is_at_least_one coeff
              then Some ((coeff,dim)::accum)    
              else Some ((QQ.zero,dim)::accum)) (* Need not restrict to >=1 *)
          else if dim == CoordinateSystem.const_id then (* --------- CONSTANT *)
            (if is_non_negative coeff
              then Some ((coeff,dim)::accum)    (* Keep non-negative constants *)
              else Some accum)                  (* Drop negative constants *)
          else if BatMap.Int.mem dim sub_dim_to_rec_num then (* LOWER STRATUM *)
            (if is_non_negative coeff
              then Some ((coeff,dim)::accum)    (* Keep non-negative coefficients *)
              else Some accum)                  (* Drop negative coefficients *)
          else 
            None *)
