open Core
open Apak
open Ark
open CfgIr
open BatPervasives
open ArkPervasives

module RG = Interproc.RG
module G = RG.G

include Log.Make(struct let name = "cra" end)

(* Decorate the program with numerical invariants *)

module MakeDecorator(M : sig
  type t
  val manager_alloc : unit -> t Apron.Manager.t
end) = struct

  module ApronI =
    Ai.ApronInterpretation
  module I = Ai.IExtra(ApronI)

  module SCCG = Loop.SccGraph(G)
  let enum_loop_headers rg = SCCG.enum_headers (SCCG.construct rg)

  module NA = struct
    type absval = I.t
    type st = unit
    module G = Interproc.RG.G
    let nonvariable = function
      | Variable _ -> false
      | Deref _ -> true
    let safe_cyl av aps = I.cyl (I.inject av aps) aps
    let transfer _ flow_in def =
(*
      Log.logf 0 "Transfer: %a" Def.format def;
      let flow_in_i = I.inject flow_in (Def.get_uses def) in
      Log.logf 0 "Input: %a" I.format flow_in_i;
*)
      let res = 
      match def.dkind with
      | Call (None, AddrOf (Variable (func, OffsetFixed 0)), []) ->
	if CfgIr.defined_function func (CfgIr.get_gfile()) then
	(* Havoc the global variables *)
	  let open ApronI in
	  let global_aps =
	    Env.fold
	      (fun ap _ aps ->
		if AP.is_global ap then AP.Set.add ap aps else aps)
	      flow_in.env
	      AP.Set.empty
	  in
	  I.cyl flow_in global_aps
	else flow_in (* Treat undefined functions as no-ops *)
      | Assign (var, expr) ->
	begin
	  match resolve_type (Var.get_type var) with
	  | Int _ | Pointer _ | Dynamic ->
	    if AP.Set.exists nonvariable (Expr.get_uses expr)
	    then safe_cyl flow_in (AP.Set.singleton (Variable var))
	    else I.transfer def (I.inject flow_in (Def.get_uses def))
	  | _ -> flow_in
	end
      | Store (lhs, _) ->
	(* Havoc all the variables lhs could point to *)
	let open Pa in
	let add_target memloc set = match memloc with
	  | (MAddr v, offset) -> AP.Set.add (Variable (v, offset)) set
	  | _, _ -> set
	in
	let vars = MemLoc.Set.fold add_target (resolve_ap lhs) AP.Set.empty in
	safe_cyl flow_in vars
      | Assume bexpr | Assert (bexpr, _) ->
	if AP.Set.exists nonvariable (Bexpr.get_uses bexpr)
	then flow_in
	else I.transfer def (I.inject flow_in (Def.get_uses def))
      | Builtin (Alloc (v, _, _)) ->
	safe_cyl flow_in (AP.Set.singleton (Variable v))
      | Initial -> I.transfer def flow_in
      | _ -> flow_in
      in
      res
    let flow_in _ graph val_map v =
      let add_pred v value = I.join (val_map v) value in
      G.fold_pred add_pred graph v (I.bottom AP.Set.empty)
    let join _ _ x y =
      let newv = I.join x y in
      if I.equal x newv then None else Some newv
    let widen =
      let f _ _ old_val new_val =
	let wide_val = I.widen old_val new_val in
	if I.equal old_val wide_val then None else Some wide_val
      in
      Some f
    let name = "Numerical analysis"
    let format_vertex = Def.format
    let format_absval = I.format
  end
  module NumAnalysis = Solve.Mk(NA)

  let decorate rg =
    let decorate_block block body =
      let result = NumAnalysis.empty_result () body in
      let entry = RG.block_entry rg block in
      NumAnalysis.init_result result body (fun d ->
	if Def.equal entry d
	then I.top AP.Set.empty
	else I.bottom AP.Set.empty);
      NumAnalysis.solve result (G.fold_vertex (fun x xs -> x::xs) body []);
      let f body v =
	let value = NumAnalysis.output result v in
	let bexpr = ApronI.bexpr_of_av value in
	let def = Def.mk (Assume bexpr) in
	G.split body v ~pred:v ~succ:def
      in
      BatEnum.fold f body (enum_loop_headers body)
    in
    RG.map decorate_block rg
end

type abstract_domain = Box | Octagon | Polyhedron
let default_domain = ref Box

let decorate rg =
  match !default_domain with
  | Box ->
    let module D = MakeDecorator(Box) in
    D.decorate rg
  | Octagon ->
    let module D = MakeDecorator(Oct) in
    D.decorate rg
  | Polyhedron ->
    let module D = MakeDecorator(struct
      type t = Polka.loose Polka.t
      let manager_alloc = Polka.manager_alloc_loose
    end) in
    D.decorate rg

let tr_typ typ = match resolve_type typ with
  | Int _   -> TyInt
  | Float _ -> TyReal
  | Pointer _ -> TyInt
  | Enum _ -> TyInt
  | Array _ -> TyInt
  | Dynamic -> TyReal
  | _ -> TyInt

type value =
| VVal of Var.t
| VPos of Var.t
| VWidth of Var.t
    deriving (Compare)

let var_of_value = function
  | VVal v | VPos v | VWidth v -> v
let map_value f = function
  | VVal v -> VVal (f v)
  | VPos v -> VPos (f v)
  | VWidth v -> VWidth (f v)

module V = struct

  module I = struct
    type t = value deriving (Compare)
    include Putil.MakeFmt(struct
      type a = t
      let format formatter = function
	| VVal v -> Var.format formatter v
	| VWidth v -> Format.fprintf formatter "%a@@width" Var.format v
	| VPos v -> Format.fprintf formatter "%a@@pos" Var.format v
    end)
    let compare = Compare_t.compare
    let show = Show_t.show
    let format = Show_t.format
    let equal x y = compare x y = 0
    let hash = function
      | VVal v -> Hashtbl.hash (Var.hash v, 0)
      | VPos v -> Hashtbl.hash (Var.hash v, 1)
      | VWidth v -> Hashtbl.hash (Var.hash v, 2)
  end
  include I

  let prime = map_value (flip Var.subscript 1)

  module E = Enumeration.Make(I)
  let enum = E.empty ()
  let of_smt sym = match Smt.symbol_refine sym with
    | Smt.Symbol_int id -> E.from_int enum id
    | Smt.Symbol_string _ -> assert false
  let typ v = tr_typ (Var.get_type (var_of_value v))
  let to_smt v =
    let id = E.to_int enum v in
    match typ v with
    | TyInt -> Smt.mk_int_const (Smt.mk_int_symbol id)
    | TyReal -> Smt.mk_real_const (Smt.mk_int_symbol id)
  let tag = E.to_int enum
end

module K = struct
  include Transition.Make(V)
(*
  let simplify tr =
    logf
      "Simplifying formula: %d atoms, %d size, %d max dnf, %d program, %d tmp"
      (F.nb_atoms tr.guard)
      (F.size tr.guard)
      (F.dnf_size tr.guard)
      (VarSet.cardinal (formula_free_program_vars tr.guard))
      (VSet.cardinal (formula_free_tmp_vars tr.guard));
    let simplified = simplify tr in
    logf
      "Simplified:          %d atoms, %d size, %d max dnf, %d program, %d tmp"
      (F.nb_atoms simplified.guard)
      (F.size simplified.guard)
      (F.dnf_size simplified.guard)
      (VarSet.cardinal (formula_free_program_vars simplified.guard))
      (VSet.cardinal (formula_free_tmp_vars simplified.guard));
    simplified
*)
  let exists p tr =
    let abstract p x =
      let x = F.linearize (fun () -> V.mk_tmp "nonlin" TyInt) x in
      let man = Oct.manager_alloc () in
      F.of_abstract (F.abstract ~exists:(Some p) man x)
    in
    F.opt_simplify_strategy := [abstract];
    let res = simplify (exists p tr) in
    F.opt_simplify_strategy := [];
    res
  let exists p tr =
    Log.time "Existential quantification" (exists p) tr

  let simplify tr = tr

  let add x y =
    if equal x zero then y
    else if equal y zero then x
    else Log.time "cra:add" (add (simplify x)) (simplify y)

  let mul x y =
    if equal x zero || equal y zero then zero
    else if equal x one then y
    else if equal y one then x
    else simplify (Log.time "cra:mul" (mul x) y)
  let star x =
    Log.time "cra:star" star x
  let widen x y = Log.time "cra:widen" (widen x) y
end
module A = Interproc.MakePathExpr(K)

(* Linearization as a simplifier *)
let linearize _ = K.F.linearize (fun () -> K.V.mk_tmp "nonlin" TyInt)

let _ =
  let open K in
  opt_higher_recurrence := true;
  opt_disjunctive_recurrence_eq := false;
  opt_loop_guard := Some F.exists;
  opt_recurrence_ineq := false;
  opt_higher_recurrence_ineq := false;
  opt_unroll_loop := false;
  opt_polyrec := true;
  F.opt_qe_strategy := F.qe_lme;
  F.opt_linearize_strategy := F.linearize_opt;
  F.opt_simplify_strategy := []


type ptr_term =
  { ptr_val : K.T.t;
    ptr_pos : K.T.t;
    ptr_width : K.T.t }

type term =
| TInt of K.T.t
| TPointer of ptr_term

let int_binop op left right =
  let open K in
  match op with
  | Add -> T.add left right
  | Minus -> T.sub left right
  | Mult -> T.mul left right
  | Div -> T.idiv left right
  | Mod -> T.modulo left right
  | _ -> T.var (V.mk_tmp "havoc" TyInt)

let term_binop op left right = match left, op, right with
  | (TInt left, op, TInt right) ->
    TInt (int_binop op left right)
  | (TPointer ptr, Add, TInt offset)
  | (TInt offset, Add, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Add ptr.ptr_val offset;
	ptr_pos = int_binop Add ptr.ptr_pos offset;
	ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer ptr, Minus, TInt offset) ->
    let p =
      { ptr_val = int_binop Minus ptr.ptr_val offset;
	ptr_pos = int_binop Minus ptr.ptr_pos offset;
	ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TInt offset, Minus, TPointer ptr) ->
    let p =
      { ptr_val = int_binop Minus offset ptr.ptr_val;
	ptr_pos = int_binop Minus offset ptr.ptr_pos;
	ptr_width = ptr.ptr_width }
    in
    TPointer p
  | (TPointer left, op, TInt right) ->
    TInt (int_binop op left.ptr_val right)
  | (TInt left, op, TPointer right) ->
    TInt (int_binop op left right.ptr_val)
  | (TPointer left, op, TPointer right) ->
    TInt (int_binop op left.ptr_val right.ptr_val)

let typ_has_offsets typ = is_pointer_type typ || typ = Concrete Dynamic

let tr_expr expr =
  let open K in
  let alg = function
    | OHavoc typ -> TInt (T.var (V.mk_tmp "havoc" (tr_typ typ)))
    | OConstant (CInt (k, _)) -> TInt (T.int (ZZ.of_int k))
    | OConstant (CFloat (k, _)) -> TInt (T.const (QQ.of_float k))
    | OCast (_, expr) -> expr
    | OBinaryOp (a, op, b, _) -> term_binop op a b

    | OUnaryOp (Neg, TInt a, _) -> TInt (T.neg a)
    | OUnaryOp (Neg, TPointer a, _) -> TInt (T.neg a.ptr_val)
    | OAccessPath (Variable v) ->
      if typ_has_offsets (Var.get_type v) then
	TPointer { ptr_val = T.var (V.mk_var (VVal v));
		   ptr_width = T.var (V.mk_var (VWidth v));
		   ptr_pos = T.var (V.mk_var (VPos v)) }
      else TInt (T.var (V.mk_var (VVal v)))

    | OAddrOf _ ->
      (* Todo: width and pos aren't correct. *)
      TPointer { ptr_val = T.var (V.mk_tmp "tr" TyInt);
		 ptr_width = T.one;
		 ptr_pos = T.zero }

    (* No real translations for anything else -- just return a free var "tr"
       (which just acts like a havoc). *)
    | OUnaryOp (_, _, typ) -> TInt (T.var (V.mk_tmp "tr" (tr_typ typ)))
    | OBoolExpr _ -> TInt (T.var (V.mk_int_tmp "tr"))
    | OAccessPath ap -> TInt (T.var (V.mk_tmp "tr" (tr_typ (AP.get_type ap))))
    | OConstant _ -> TInt (T.var (V.mk_int_tmp "tr"))
  in
  Expr.fold alg expr


let tr_expr_val expr = match tr_expr expr with
  | TInt x -> x
  | TPointer x -> x.ptr_val

let tr_bexpr bexpr =
  let open K in
  let alg = function
    | Core.OAnd (a, b) -> F.conj a b
    | Core.OOr (a, b) -> F.disj a b
    | Core.OAtom (pred, x, y) ->
      let x = tr_expr_val x in
      let y = tr_expr_val y in
      begin
	match pred with
	| Lt -> F.lt x y
	| Le -> F.leq x y
	| Eq -> F.eq x y
	| Ne -> F.disj (F.lt x y) (F.gt x y)
      end
  in
  Bexpr.fold alg bexpr

let weight def =
  let open K in
  match def.dkind with
  | Assume phi | Assert (phi, _) -> K.assume (tr_bexpr phi)
  | Assign (lhs, rhs) ->
    if typ_has_offsets (Var.get_type lhs) then begin
      match tr_expr rhs with
      | TPointer rhs ->
	BatList.reduce K.mul [
	  K.assign (VVal lhs) rhs.ptr_val;
	  K.assign (VPos lhs) rhs.ptr_pos;
	  K.assign (VWidth lhs) rhs.ptr_width;
	]
      | TInt tint -> begin
	(match Var.get_type lhs, rhs with
	| (_, Havoc _) | (Concrete Dynamic, _) -> ()
	| _ -> Log.errorf "Ill-typed pointer assignment: %a" Def.format def);
	BatList.reduce K.mul [
	  K.assign (VVal lhs) tint;
	  K.assign (VPos lhs) (T.var (V.mk_tmp "type_err" TyInt));
	  K.assign (VWidth lhs) (T.var (V.mk_tmp "type_err" TyInt))
	]
      end
    end else K.assign (VVal lhs) (tr_expr_val rhs)
  | Store (lhs, _) ->
    (* Havoc all the variables lhs could point to *)
    let open Pa in
    let add_target memloc tr = match memloc with
      | (MAddr v, offset) ->
	if typ_has_offsets (Var.get_type (v,offset)) then begin
	  BatList.reduce K.mul [
	    tr;
	    K.assign (VVal (v,offset)) (T.var (V.mk_tmp "store" TyInt));
	    K.assign (VPos (v,offset)) (T.var (V.mk_tmp "store" TyInt));
	    K.assign (VWidth (v,offset)) (T.var (V.mk_tmp "store" TyInt))
	  ]
	end else begin
	  K.mul tr (K.assign (VVal (v,offset)) (T.var (V.mk_tmp "store" TyInt)))
	end
      | _, _ -> tr
    in
    MemLoc.Set.fold add_target (resolve_ap lhs) one
  | Builtin Exit -> zero
  | Builtin (Alloc (v, size, _)) ->
    BatList.reduce K.mul [
      K.assign (VVal v) (T.var (V.mk_tmp "alloc" TyInt));
      K.assign (VWidth v) (tr_expr_val size);
      K.assign (VPos v) T.zero
    ]
  | Builtin AtomicBegin | Builtin AtomicEnd
  | Builtin (Acquire _) | Builtin (Release _)
  | Builtin (Free _)
  | Initial | AssertMemSafe (_, _) | Return None -> one
  | _ ->
    Log.errorf "No translation for definition: %a" Def.format def;
    assert false

let forward_inv_gen = ref false
let set_qe = function
  | "lme" -> K.F.opt_qe_strategy := K.F.qe_lme
  | "cover" -> K.F.opt_qe_strategy := K.F.qe_cover
  | "z3" -> K.F.opt_qe_strategy := K.F.qe_z3
  | "trivial" -> K.F.opt_qe_strategy := K.F.qe_trivial
  | s -> Log.errorf "Unrecognized QE strategy: `%s`" s; assert false


let abstract_guard man p phi =
  K.F.of_abstract (K.F.abstract man ~exists:(Some p) phi)

let set_guard s =
  if s = "none" then K.opt_loop_guard := None else
    let guard = match s with
      | "qe" -> K.F.exists
      | "box" -> abstract_guard (Box.manager_of_box (Box.manager_alloc ()))
      | "oct" -> abstract_guard (Oct.manager_of_oct (Oct.manager_alloc ()))
      | "polka" ->
	abstract_guard (Polka.manager_of_polka (Polka.manager_alloc_loose ()))
      | _ ->
	Log.errorf "Unrecognized option for -cra-guard: `%s'" s;
	assert false
    in
    K.opt_loop_guard := Some guard

let _ =
  CmdLine.register_config
    ("-cra-forward-inv",
     Arg.Set forward_inv_gen,
     " Forward invariant generation");
  CmdLine.register_config
    ("-cra-unroll-loop",
     Arg.Set K.opt_unroll_loop,
     " Unroll loops");
  CmdLine.register_config
    ("-cra-rec-ineq",
     Arg.Set K.opt_recurrence_ineq,
     " Solve simple recurrence inequations");
  CmdLine.register_config
    ("-cra-higher-rec-ineq",
     Arg.Set K.opt_higher_recurrence_ineq,
     " Solve higher recurrence inequations");
  CmdLine.register_config
    ("-cra-no-polyrec",
     Arg.Clear K.opt_polyrec,
     " Turn off polyhedral recurrences");
  CmdLine.register_config
    ("-cra-guard",
     Arg.String set_guard,
     " Turn off loop guards");
  CmdLine.register_config
    ("-qe",
     Arg.String set_qe,
     " Set default quantifier elimination strategy (lme,cover,z3)")
  

let analyze file =
  match file.entry_points with
  | [main] -> begin
    let rg = Interproc.make_recgraph file in
    let rg =
      if !forward_inv_gen
      then Log.phase "Forward invariant generation" decorate rg
      else rg
    in
    let local func_name =
      if defined_function func_name (get_gfile()) then begin
	let func = lookup_function func_name (get_gfile()) in
	let vars =
	  Varinfo.Set.remove (return_var func_name)
	    (Varinfo.Set.of_enum
	       (BatEnum.append
		  (BatList.enum func.formals)
		  (BatList.enum func.locals)))
	in
	logf "Locals for %a: %a"
	  Varinfo.format func_name
	  Varinfo.Set.format vars;
	fun x -> (Varinfo.Set.mem (fst (var_of_value x)) vars)
      end else (fun _ -> false)
    in
    let query = A.mk_query rg weight local main in
    let is_assert def = match def.dkind with
      | Assert (_, _) | AssertMemSafe _ -> true
      | _             -> false
    in
    let s = new Smt.solver in
    let check_assert def path =
      match def.dkind with
      | AssertMemSafe (expr, msg) -> begin
	match tr_expr expr with
	| TInt _ ->
	  Report.log_error (Def.get_location def) "Memory safety (type error)"
	| TPointer p ->
	  begin
	    let sigma v = match K.V.lower v with
	      | None -> K.T.var v
	      | Some v ->
		try K.M.find v path.K.transform
		with Not_found -> K.T.var (K.V.mk_var v)
	    in
	    let phi =
	      K.F.conj
		(K.F.geq p.ptr_pos K.T.zero)
		(K.F.lt p.ptr_pos p.ptr_width)
	    in
	    let phi = K.F.subst sigma phi in

	    let mk_tmp () = K.V.mk_tmp "nonlin" TyInt in
	    let path_condition =
	      K.F.conj (K.to_formula path) (K.F.negate phi)
	    in

	    s#push ();
	    s#assrt (K.F.to_smt path_condition);
	    let checked =
	      try
		begin match Log.time "Assertion checking" s#check () with
		| Smt.Unsat -> (Report.log_safe (); true)
		| Smt.Sat -> (Report.log_error (Def.get_location def) msg; true)
		| Smt.Undef -> false
		end
	      with Z3.Error _ -> false
	    in
	    if (not checked) && not (K.F.is_linear path_condition) then begin
	      Log.errorf "Z3 inconclusive; trying to linearize";
	      s#pop ();
	      s#push ();
	      s#assrt (K.F.to_smt (K.F.linearize mk_tmp path_condition));
	      begin match Log.time "Assertion checking" s#check () with
	      | Smt.Unsat -> Report.log_safe ()
	      | Smt.Sat -> Report.log_error (Def.get_location def) msg
	      | Smt.Undef -> Report.log_error (Def.get_location def) msg
	      end
	    end;
	    s#pop ();
	  end
      end
      | Assert (phi, msg) -> begin
	s#push ();

	let phi = tr_bexpr phi in
	let sigma v = match K.V.lower v with
	  | None -> K.T.var v
	  | Some v ->
	    try K.M.find v path.K.transform
	    with Not_found -> K.T.var (K.V.mk_var v)
	in
	let phi = K.F.subst sigma phi in
	let mk_tmp () = K.V.mk_tmp "nonlin" TyInt in
	let path_condition = K.F.conj (K.to_formula path) (K.F.negate phi) in
	logf "Path condition:@\n%a" K.format path;
	s#assrt (K.F.to_smt path_condition);
	let checked =
	  try
	    begin match Log.time "Assertion checking" s#check () with
	    | Smt.Unsat -> (Report.log_safe (); true)
	    | Smt.Sat -> (Report.log_error (Def.get_location def) msg; true)
	    | Smt.Undef -> false
	    end
	  with Z3.Error _ -> false
	in

	if (not checked) && not (K.F.is_linear path_condition) then begin
	  Log.errorf "Z3 inconclusive; trying to linearize";
	  s#pop ();
	  s#push ();
	  s#assrt (K.F.to_smt (K.F.linearize mk_tmp path_condition));
	  begin match Log.time "Assertion checking" s#check () with
	  | Smt.Unsat -> Report.log_safe ()
	  | Smt.Sat -> Report.log_error (Def.get_location def) msg
	  | Smt.Undef -> Report.log_error (Def.get_location def) msg
	  end
	end;
	s#pop ()
      end
      | _ -> ()
    in
    A.single_src_restrict query is_assert check_assert;

    Report.print_errors ();
    Report.print_safe ();
    if !CmdLine.show_stats then begin
      K.T.log_stats ();
      K.F.log_stats ()
    end
  end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-cra", analyze, " Compositional recurrence analysis")