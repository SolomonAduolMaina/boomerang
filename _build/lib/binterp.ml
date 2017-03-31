(******************************************************************************)
(* The Harmony Project                                                        *)
(* harmony@lists.seas.upenn.edu                                               *)
(******************************************************************************)
(* Copyright (C) 2008 J. Nathan Foster and Benjamin C. Pierce                 *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(******************************************************************************)
(* /src/binterp.ml                                                            *)
(* Boomerang interpreter *)
(* $Id: binterp.ml 4999 2011-03-17 12:38:28Z mgree $ *)
(******************************************************************************)

(* -------------------------------------------------------------------------- *)
(* IMPORTS AND ABBREVIATIONS                                               *)

open Bsyntax
open Bident
open Benv
open Bprint
open Bsubst
module V = Bvalue
module G = Bregistry

(* -------------------------------------------------------------------------- *)
(* ERRORS / DEBUGGING                                                      *)

let msg = Util.format

let test_error i msg_thk =
	raise (Error.Harmony_error
			(fun () -> msg "@[%s: Unit test failed @ " (Info.string_of_t i);
						msg_thk ();
						msg "@]"))

(* -------------------------------------------------------------------------- *)
(* UNIT TESTS                                                              *)

(* test results: success with a value, or failure with an error message *)
type testresult = OK of Bvalue.t | Error of (unit -> unit)

let tests = Prefs.testPref
let test_all = Prefs.testallPref

(* [check_test m] returns [true] iff the command line arguments            *)
(* '-test-all' or '-test m' are set                                        *)
let check_test ms =
	Safelist.fold_left
		(fun r qs -> r || (Qid.id_prefix (G.parse_qid qs) ms))
		(Prefs.read test_all)
		(Prefs.read tests)

(* -------------------------------------------------------------------------- *)
(* INTERPRETER                                                             *)

(* dynamic match: determine if a value *does* match a pattern; return the  *)
(* list of value bindings for variables.                                   *)
let rec dynamic_match i p0 v0 = match p0, v0 with
	| PWld _, _ -> Some []
	| PVar(_, q, so), _ -> Some [(q, v0, so)]
	| PUnt _, V.Unt(_) -> Some []
	| PInt(_, n1), V.Int(_, n2) -> if n1 = n2 then Some [] else None
	| PBol(_, b1), V.Bol(_, b2) ->
			if (b1 && (b2 = None)) || (not b1 && (b2 <> None)) then Some []
			else None
	| PCex(_, p), V.Bol(vi, Some s) -> dynamic_match i p (V.mk_s vi s)
	| PStr(_, s1), V.Str(_, s2) -> if s1 = s2 then Some [] else None
	| PVnt(_, (_, li), pio), V.Vnt(_, _, lj, vjo) ->
			if Id.equal li lj then
				match pio, vjo with
				| None, None -> Some []
				| Some pi, Some vj -> dynamic_match i pi vj
				| _ ->
						Berror.run_error i
							(fun () ->
										msg "@[wrong@ number@ of@ arguments@ to@ constructor@ %s@]"
											(Id.string_of_t li))
			else None
	| PPar(_, p1, p2), V.Par(_, v1, v2) ->
			(match dynamic_match i p1 v1, dynamic_match i p2 v2 with
				| Some l1, Some l2 -> Some (l1 @ l2)
				| _ -> None)
	| _ -> None

(* ----- interpret casts ----- counters for parallel and in-line checks *)
let pc = ref 0
let ic = ref 0
let mc = ref 0

(* precondition: f and t must be compatible. *)
let rec interp_cast (wq: ((unit -> V.t) -> unit) option) cev b f t =
	(* generates cast into the refinement (x:t where e) *)
	let cast_refinement mandatory f x t e =
		let rec run_check wq v =
			let v = interp_cast wq cev b f t v in
			let cev' = CEnv.update cev (Qid.t_of_id x) (G.Unknown, v) in
			match V.get_x (interp_exp wq cev' e) with
			| None -> v
			| Some cex ->
					let cex_s =
						if cex = "" then ""
						else "; counterexample: " ^ cex in
					Berror.blame_error b
						(fun () ->
							(* TODO show bindings of free vars in e *)
									Util.format "@[%s=%a@ did@ not@ satisfy@ %a%s@]"
										(Id.string_of_t x)
										(fun _ -> V.format) v
										(fun _ -> format_exp) e
										cex_s) in
		if Prefs.read Prefs.unsafePref
		then (* no checking at all *)
		(fun v -> v)
		else if ((not mandatory) && wq <> None)
		then (* parallel checking *)
		(fun v ->
					incr pc;
					let wq = Util.extractValueFromOption wq in
					wq (fun () -> run_check None v);
					v)
		else (* in-line mandatory checking *)
		(fun v ->
					if mandatory then incr mc;
					incr ic;
					run_check wq v) in
	let native_coercion x =
		let q = Qid.mk_native_prelude_t b x in
		match CEnv.lookup cev q with
		| Some(_, v) -> V.get_f v wq
		| None ->
				Berror.run_error b
					(fun () -> msg "@[%s unbound@]"
									(Qid.string_of_t q)) in
	let res =
		if Bcheck.trivial_cast f t then (fun v -> v)
		else
			match f, t with
			| SUnit, SUnit
			| SBool, SBool
			| SInteger, SInteger
			| SChar, SChar
			| SString, SString
			| SRegexp, SRegexp
			| SAregexp, SAregexp
			| SLens, SLens
			| SCanonizer, SCanonizer
			| SVar(_), SVar(_) ->
					(fun v -> v)
			| SPrefs f, SPrefs t when f = t ->
					(fun v -> v)
			| SChar, SString ->
					native_coercion "string_of_char"
			| SChar, SRegexp ->
					(fun v ->
								native_coercion "regexp_of_string"
									(native_coercion "string_of_char" v))
			| SChar, SAregexp ->
					(fun v ->
								native_coercion "rxlift"
									(native_coercion "regexp_of_string"
											(native_coercion "string_of_char" v)))
			| SChar, SLens ->
					(fun v ->
								native_coercion "copy"
									(native_coercion "regexp_of_string"
											(native_coercion "string_of_char" v)))
			| SString, SRegexp ->
					native_coercion "regexp_of_string"
			| SString, SAregexp ->
					(fun v ->
								native_coercion "rxlift"
									(native_coercion "regexp_of_string" v))
			| SString, SLens ->
					(fun v ->
								native_coercion "copy"
									(native_coercion "regexp_of_string" v))
			| SRegexp, SAregexp ->
					native_coercion "rxlift"
			| SRegexp, SLens ->
					native_coercion "copy"
			| SFunction(x, f1, f2), SFunction(y, t1, t2) ->
					let fn = Id.mk b "fn" in
					let c1 = Bcheck.mk_cast "function argument" b t1 f1 (mk_var y) in
					let c2 = Bcheck.mk_cast "function result" b f2 t2 (mk_app b (mk_var fn) (mk_var x)) in
					(fun v ->
								let cev' = CEnv.update cev (Qid.t_of_id fn) (G.Unknown, v) in
								interp_exp wq cev' (mk_fun b y t1 (mk_let b x f1 c1 c2)))
			| SProduct(f1, f2), SProduct(t1, t2) ->
			(* JNF: can this first case happen? why isn't this a trivial cast?   *)
			(* if syneq_sort f1 t1 && syneq_sort f2 t2 then (fun v -> v) else    *)
					(fun v ->
								let x = Id.mk b "x" in
								let y = Id.mk b "y" in
								let v1, v2 = V.get_p v in
								let cev' =
									CEnv.update (CEnv.update cev (Qid.t_of_id x) (G.Unknown, v1))
										(Qid.t_of_id y) (G.Unknown, v2) in
								let c1 = Bcheck.mk_cast "pair fst" b f1 t1 (mk_var x) in
								let c2 = Bcheck.mk_cast "pair snd" b f2 t2 (mk_var y) in
								interp_exp wq cev' (EPair(b, c1, c2)))
			| SData(fl, x), SData(tl, y) when Qid.equal x y ->
					let rec aux acc l1 l2 = acc && match l1, l2 with
						| [],[] -> true
						| h1:: t1, h2:: t2 -> aux (syneq_sort h1 h2) t1 t2
						| _ -> false in
					if aux true fl tl then (fun v -> v)
					else
						let _, (svl, cl) = Bcheck.get_type (CEnv.lookup_type cev) b x in
						let fsubst = Safelist.combine svl fl in
						let tsubst = Safelist.combine svl tl in
						let cl_finst = Bcheck.inst_cases fsubst cl in
						let cl_tinst = Bcheck.inst_cases tsubst cl in
						let x = Id.mk b "x" in
						let qx = Qid.t_of_id x in
						let y = Id.mk b "y" in
						let qy = Qid.t_of_id y in
						let pl = Safelist.map
								(fun ((li, fio), (_, tio)) ->
											match fio, tio with
											| None, None ->
													let pi = PVnt(b, li, None) in
													let ei = EVar(b, qx) in
													(pi, ei)
											| Some fi, Some ti ->
													let li_f =
														Safelist.fold_right
															(fun tj acc -> ETyApp(b, acc, tj))
															tl (EVar(b, li)) in
													let py = PVar(b, y, Some fi) in
													let pi = PVnt(b, li, Some py) in
													(* this cast must not be expanded! (it would     *)
													(* loop on recursive data types)                 *)
													let ei = EApp(b, li_f, ECast(b, fi, ti, b, EVar(b, qy))) in
													(pi, ei)
											| _ ->
													Berror.run_error b
														(fun () ->
																	msg "@[cannot@ cast@ different@ datatypes@]"))
								(Safelist.combine cl_finst cl_tinst) in
						(fun v ->
									let cev' = CEnv.update cev (Qid.t_of_id x) (G.Unknown, v) in
									interp_exp wq cev' (ECase(b, EVar(b, qx), pl, Some t)))
			| SRefine(x, _, t1, e1), SRefine(y, mandatory, t2, e2) ->
					if Id.equal x y && syneq_sort t1 t2 && syneq_exp e1 e2
					then (fun v -> v)
					else cast_refinement mandatory f y t2 e2
			| _, SRefine(x, mandatory, t2, e2) ->
					cast_refinement mandatory f x t2 e2
			| SRefine(x, _, f1, e1), t1 ->
					interp_cast wq cev b f1 t1
			| SForall(x, f1), SForall(y, t1) ->
			(* no need to freshen since compatibility substitutes *)
					(interp_cast wq cev b f1 t1)
			| _ ->
					Berror.run_error b
						(fun () ->
									msg "@[cannot@ cast@ incompatible@ %s@ to@ %s@]"
										(string_of_sort f) (string_of_sort t)) in
	res

(* ----- interpret expressions ----- *)

and interp_exp wq cev e0 =
	match e0 with
	| EVar(i, q) -> begin
				match CEnv.lookup_both cev q with
				| Some((G.Unknown, v), _) -> v
				| Some((G.Sort s, v), s_env) ->
						let s_base = Bsubst.erase_sort s in
						(interp_cast wq s_env i s s_base) v
				| None ->
						Berror.run_error i
							(fun () -> msg "@[%s unbound@]"
											(Qid.string_of_t q))
			end
	
	| EOver(i, op, _) ->
			Berror.run_error i
				(fun () ->
							msg "@[unresolved@ overloaded@ operator %s@]"
								(string_of_op op))
	
	| EApp(_, e1, e2) ->
			let v1 = interp_exp wq cev e1 in
			let v2 = interp_exp wq cev e2 in
			(V.get_f v1) wq v2
	
	| ELet(_, b, e) ->
			let bcev, _ = interp_binding wq cev b in
			interp_exp wq bcev e
	
	| EFun(i, p, _, e) ->
			let f wq v = (* !!! param'd on wq, to determine parallel/mainline eval *)
				let qp = Qid.t_of_id (id_of_param p) in
				let body_cev = CEnv.update cev qp (G.Unknown, v) in
				interp_exp wq body_cev e in
			V.Fun(i, f)
	
	| EPair(i, e1, e2) ->
			let v1 = interp_exp wq cev e1 in
			let v2 = interp_exp wq cev e2 in
			V.Par(i, v1, v2)
	
	| ECase(i, e1, pl, _) ->
			let v1 = interp_exp wq cev e1 in
			let rec find_match = function
				| [] ->
						Berror.run_error i
							(fun () ->
										msg "@[match@ failure@]")
				| (pi, ei):: rest ->
						(match dynamic_match i pi v1 with
							| None -> find_match rest
							| Some l -> l, ei) in
			let binds, ei = find_match pl in
			let qid_binds = Safelist.map
					(fun (x, v, so) ->
								let rs = match so with
									| None -> G.Unknown
									| Some s -> G.Sort s in
								(Qid.t_of_id x, (rs, v))) binds in
			let ei_cev = CEnv.update_list cev qid_binds in
			interp_exp wq ei_cev ei
	
	(* tyfuns are interpreted as functions; tyapps apply to unit *)
	| ETyFun(i, _, e) ->
			interp_exp wq cev (EFun(i, Param(i, Id.wild, SUnit), None, e))
	
	| ETyApp(i, e1, s2) ->
			interp_exp wq cev (EApp(i, e1, EUnit(i)))
	
	| EGrammar(i, ps) ->
			Berror.run_error i (fun () -> msg "@[unexpected@ grammar@ expression@ at@ interpreter@]")
	
	(* constants *)
	| EUnit(i) -> V.Unt(i)
	| EBoolean(i, None) -> V.Bol(i, None)
	| EBoolean(i, Some e1) -> V.Bol(i, Some (V.get_s (interp_exp wq cev e1)))
	| EInteger(i, n) -> V.Int(i, n)
	| EChar(i, c) -> V.Chr(i, c)
	| EString(i, s) -> V.Str(i, s)
	| ECSet(i, pos, cs) ->
			let csi = Safelist.map (fun (ci, cj) -> (Char.code ci, Char.code cj)) cs in
			let mk = if pos then Brx.mk_cset else Brx.mk_neg_ascii_cset in
			V.Rx(i, mk csi)
	
	| ECast(i, f, t, b, e) ->
			(interp_cast wq cev b f t)
				(interp_exp wq cev e)

and interp_binding wq cev b0 = match b0 with
	| Bind(i, p, so, e) ->
			let v = interp_exp wq cev e in
			let xs_rev, bcev = match dynamic_match i p v with
				| None -> Berror.run_error i
							(fun () -> msg "@[in let-binding: %s does not match %s@]"
											(string_of_pat p) (V.string_of_t v))
				| Some binds ->
						Safelist.fold_left
							(fun (xsi, cevi) (xi, vi, soi) ->
										let qxi = Qid.t_of_id xi in
										let rsi = match soi with
											| None -> G.Unknown
											| Some s -> G.Sort s in
										(qxi:: xsi, CEnv.update cevi (Qid.t_of_id xi) (rsi, vi)))
							([], cev) binds in
			(bcev, Safelist.rev xs_rev)

let rec interp_decl wq cev ms d0 = match d0 with
	| DLet(i, b) ->
			interp_binding wq cev b
	| DType(i, svl, qx, cl) ->
			let sx = SData(sl_of_svl svl, qx) in
			let mk_univ s =
				Safelist.fold_right
					(fun svi acc -> SForall(svi, acc))
					svl s in
			let mk_impl v =
				Safelist.fold_right
					(fun _ f -> V.Fun(i, (fun _ v -> f)))
					svl v in
			let new_cev, xs =
				Safelist.fold_left
					(fun (cev, xs) (l, so) ->
								let ql = Qid.t_of_id l in
								let rv = match so with
									| None ->
											let s = mk_univ sx in
											let v = mk_impl (V.Vnt(i, qx, l, None)) in
											(G.Sort s, v)
									| Some s ->
											let s = mk_univ (SFunction(Id.wild, s, sx)) in
											let f _ v = V.Vnt(V.info_of_t v, qx, l, Some v) in
											let v = mk_impl (V.Fun(i, f)) in
											(G.Sort s, v) in
								(CEnv.update cev ql rv, Qid.t_of_id l:: xs))
					(cev,[]) cl in
			let qcl = Safelist.map (fun (x, so) -> (Qid.t_of_id x, so)) cl in
			let new_cev' = CEnv.update_type new_cev svl qx qcl in
			(new_cev', xs)
	
	| DMod(i, n, ds) ->
			let m_cev, names = interp_mod_aux wq cev ms ds in
			let n_cev, names_rev =
				Safelist.fold_left
					(fun (n_cev, names) q ->
								match CEnv.lookup m_cev q with
								| Some rv ->
										let nq = Qid.id_dot n q in
										(CEnv.update n_cev nq rv, nq:: names)
								| None ->
										Berror.run_error i
											(fun () -> msg "@[@ declaration@ for@ %s@ missing@]"
															(Qid.string_of_t q)))
					(cev,[])
					names in
			(n_cev, Safelist.rev names_rev)
	
	| DTest(i, e, tr) ->
			begin
				(* disable parallel checking for [test ... = error] *)
				let wq = if tr = TestError then None else wq in
				if check_test ms then
					let vo =
						try OK(interp_exp wq cev e)
						with
						| (Error.Harmony_error(err)) -> Error err
						| exn ->
								if Prefs.read Prefs.unsafePref
								then
									Error (fun () ->
												msg
													"Test result: native exception@\n%s@\n%!"
													(Printexc.to_string exn))
								else raise exn in
					match vo, tr with
					| OK (v), TestPrint ->
							msg "Test result:@ ";
							V.format v;
							msg "@\n%!"
					| OK (v), TestSortPrint(Some s) ->
							msg "Test result:@ ";
							format_sort s;
							msg "@\n%!"
					| OK (v), TestSortPrint(None)
					| OK (v), TestSortEqual(None, _) ->
							Berror.run_error i
								(fun () -> msg "@[unannotated@ unit@ test@]")
					| Error err, TestPrint
					| Error err, TestSortPrint _ ->
							test_error i
								(fun () ->
											msg "Test result: error@\n";
											err ();
											msg "@\n%!")
					| Error _, TestError -> ()
					| OK v1, TestEqual e2 ->
							let v2 = interp_exp wq cev e2 in
							if not (V.equal v1 v2) then
								test_error i
									(fun () ->
												msg "@\nExpected@ "; V.format v2;
												msg "@ but found@ "; V.format v1;
												msg "@\n%!")
					| OK v1, TestSortEqual(Some s1, s2) ->
							let err () =
								test_error i
									(fun () ->
												msg "@\nExpected@ a@ value@ with@ sort@ ";
												format_sort s1;
												msg "@ but found@ "; V.format v1;
												msg "@ : "; format_sort s2;
												msg "@\n%!") in
							if not (Bcheck.compatible s1 s2) then err ()
							else
								begin
									try
										ignore
											((interp_cast wq cev i s1 s2)
													(interp_exp wq cev e))
									with Error.Harmony_error(e) -> err ()
								end
					| Error err, TestEqual e2 ->
							let v2 = interp_exp wq cev e2 in
							test_error i
								(fun () ->
											msg "@\nExpected@ "; V.format v2;
											msg "@ but found an error:@ ";
											err ();
											msg "@\n%!")
					| Error err, TestSortEqual(_, s2) ->
							test_error i
								(fun () ->
											msg "@\nExpected@ "; format_sort s2;
											msg "@ but found an error:@ ";
											err ();
											msg "@\n%!")
					| OK v, TestError ->
							let msgFun =
								(fun () ->
											msg "@\nExpected an error@ ";
											msg "@ but found:@ ";
											V.format v;
											msg "@\n%!") in
							if Prefs.read Prefs.unsafePref
							then (msgFun (); msg "@\nMISSING ERROR IGNORED, RUNNING UNSAFELY@\n%!")
							else test_error i msgFun
			end;
			(cev, [])

and interp_mod_aux wq cev ms ds =
	Safelist.fold_left
		(fun (cev, names) di ->
					let m_cev, new_names = interp_decl wq cev ms di in
					(m_cev, names@new_names))
		(cev,[])
		ds

module Bridge = struct
	
	open Gen
	open Regexcontext
	open Lenscontext
	module L = Lang
	module BL = Blenses
	module BS = Bstring
	module Perms = BL.Permutations
	
	let info = Info.I ("", (0, 0), (0, 0))
	let synth = Qid.mk [] (Id.mk info "synth_from_regexp")
	let synth_can = Qid.mk [] (Id.mk info "synth_from_canonizers")
	let perm = Qid.mk [] (Id.mk info "perm")
	let project = Qid.mk [] (Id.mk info "project")
	let id = Qid.mk [] (Id.mk info "id")
	let list = Qid.mk [(info, "List")] (Id.mk info "t")
	
	let rec lrxToBrx (r : L.regex) : Brx.t =
		match r with
		| L.RegExEmpty -> Brx.empty
		| L.RegExBase s -> Brx.mk_string s
		| L.RegExConcat (r1, r2) -> Brx.mk_seq (lrxToBrx r1) (lrxToBrx r2)
		| L.RegExOr (r1, r2) -> Brx.mk_alt (lrxToBrx r1) (lrxToBrx r2)
		| L.RegExStar r -> Brx.mk_star (lrxToBrx r)
		| L.RegExVariable _ -> failwith "How did I get a variable?"
	
	let sLensTobLens (l : L.lens) : BL.MLens.t =
		let constLens (s1 : string) (s2 : string) : BL.MLens.t =
			let source = Brx.mk_string s1 in
			let mapTo = fun _ -> s1 in BL.MLens.clobber info source s2 mapTo in
		let rec helper (l : L.lens) : BL.MLens.t =
			match l with
			| L.LensConst (s1, s2) -> constLens s1 s2
			| L.LensConcat (l1, l2) -> BL.MLens.concat info (helper l1) (helper l2)
			| L.LensSwap (l1, l2) -> BL.MLens.concat info (helper l2) (helper l1)
			| L.LensUnion (l1, l2) -> BL.MLens.union info (helper l2) (helper l1)
			| L.LensCompose (l1, l2) -> BL.MLens.compose info (helper l2) (helper l1)
			| L.LensIterate l -> BL.MLens.star info (helper l)
			| L.LensIdentity r -> BL.MLens.copy info (lrxToBrx r)
			| L.LensInverse _ | L.LensVariable _
			| L.LensPermute _ -> failwith "TODO" in
		helper l
	
	let rec toList (v : V.t) (temp : V.t list) : V.t list =
		match v with
		| V.Vnt (_, _, _, None) -> List.rev temp
		| V.Vnt(_, _, _, Some (V.Par(_, hd, tail))) -> toList tail (hd :: temp)
		| _ -> failwith "Malformed List"
	
	let rec brxToLrx (r : Brx.t) : L.regex =
		match r.Brx.M.desc with
		| Brx.M.CSet l -> L.charSet l
		| Brx.M.Seq (r1, r2) -> L.RegExConcat(brxToLrx r1, brxToLrx r2)
		| Brx.M.Alt l ->
				List.fold_left
					(fun r x -> if r = L.RegExEmpty then x else L.RegExOr(r, x)) L.RegExEmpty
					(List.map (fun r -> brxToLrx r) l)
		| Brx.M.Rep (r, n, None) ->
				let r = brxToLrx r in L.RegExConcat(L.iterateNTimes n r, L.RegExStar r)
		| Brx.M.Rep (r, m, Some n) -> L.iterateMtoNTimes m n (brxToLrx r)
		| _ -> failwith "No support for intersection or differences in lenssynth"
	
	let getStrings (l : V.t list) : (string * string) list =
		let helper (temp : (string * string) list) (v : V.t) : (string * string) list =
			match v with
			| V.Par(_, V.Str(_, s1), V.Str(_, s2)) -> (s1, s2) :: temp
			| _ -> failwith "Malformed List"
		in List.fold_left helper [] l
	
	let get_synth : G.rs * V.t =
		let f1 ( _ : ((unit -> V.t) -> unit) option) (v : V.t) : V.t =
			match v with
			| V.Rx (_, r1) ->
					(let f2 ( _ : ((unit -> V.t) -> unit) option) (v : V.t) : V.t =
							match v with
							| V.Rx (_, r2) ->
									(let f3 ( _ : ((unit -> V.t) -> unit) option) (l : V.t) : V.t =
											match l with
											| V.Vnt (_, _, _, _) ->
													let s1, s2 = brxToLrx r1, brxToLrx r2 in
													let l = getStrings (toList l []) in
													let lens = gen_lens RegexContext.empty LensContext.empty s1 s2 l in
													let lens = match lens with
														| None -> failwith "Could not synthesize lens"
														| Some lens -> lens in
													V.Lns(info, sLensTobLens lens)
											| _ -> failwith "Wrong arguments for synth_from_regexp" in
										V.Fun (info, f3))
							| _ -> failwith "Wrong arguments for synth_from_regexp" in
						V.Fun (info, f2))
			| _ -> failwith "Wrong arguments for synth_from_regexp" in
		let sort =
			SFunction ((Id.mk info ""), SRegexp,
				(SFunction ((Id.mk info ""), SRegexp,
						(SFunction ((Id.mk info ""), SData([SProduct(SString, SString)], list),
								SLens))))) in (G.Sort sort, V.Fun (info, f1))
	
	let rec vtoString (id : Qid.t) (v : V.t) =
		match v with
		| V.Rx (_, r) -> "Rx " ^ (Qid.string_of_t id) ^ " = " ^ (Brx.string_of_t r) ^ "\n"
		| V.Unt _ -> "Unt " ^ (Qid.string_of_t id) ^ " = ()" ^ "\n"
		| V.Bol (_, s) -> let s = match s with | None -> "true" | Some s -> s in
				"Bol " ^ (Qid.string_of_t id) ^ " = " ^ s ^ "\n"
		| V.Int (_, i) -> "Int " ^ (Qid.string_of_t id) ^ " = " ^ (string_of_int i) ^ "\n"
		| V.Chr (_, c) -> "Chr " ^ (Qid.string_of_t id) ^ " = " ^ (Char.escaped c) ^ "\n"
		| V.Str (_, s) -> "Str named " ^ (Qid.string_of_t id) ^ " = " ^ s ^ "\n"
		| V.Arx (_, r) -> "Arx " ^ (Qid.string_of_t id) ^ " = " ^ (Barx.string_of_t r) ^ "\n"
		| V.Kty _ -> "Kty " ^ (Qid.string_of_t id) ^ "\n"
		| V.Mty _ -> "Mty " ^ (Qid.string_of_t id) ^ "\n"
		| V.Lns (_, r) -> "Lns " ^ (Qid.string_of_t id) ^ " = " ^ (BL.MLens.string_of_t r) ^ "\n"
		| V.Can (_, r) -> "Lns " ^ (Qid.string_of_t id) ^ " = " ^ (BL.Canonizer.string_of_t r) ^ "\n"
		| V.Prf _ -> "Prf " ^ (Qid.string_of_t id) ^ "\n"
		| V.Fun _ -> "Fun " ^ (Qid.string_of_t id) ^ "\n"
		| V.Par (_, t1, t2) ->
				"Par " ^ (Qid.string_of_t id) ^ " = (" ^ (vtoString id t1) ^ " * " ^
				(vtoString id t2) ^ ")\n"
		| V.Vnt (_, id, _, opt) ->
				match opt with
				| None -> "Vnt " ^ (Qid.string_of_t id) ^ "\n"
				| Some v -> "Vnt " ^ (Qid.string_of_t id) ^ " = (" ^ (vtoString id v) ^ ")"
	
	let rec permutations (l : 'a list) : 'a list list =
		List.map (fun m -> Perms.permute_list m l) (Perms.permutations (List.length l))
	
	let concatList (l : Brx.t list) : Brx.t =
		let rec helper (l : Brx.t list) (temp : Brx.t) : Brx.t =
			match l with
			| [] -> temp
			| x :: xs -> helper xs (Brx.mk_seq temp x) in
		match l with
		| [] -> Brx.empty
		| x :: xs -> helper xs x
	
	let altList (l : Brx.t list) : Brx.t =
		let rec helper (l : Brx.t list) (temp : Brx.t) : Brx.t =
			match l with
			| [] -> temp
			| x :: xs -> helper xs (Brx.mk_alt temp x) in
		match l with
		| [] -> Brx.empty
		| x :: xs -> helper xs x
	
	let rec evenOdd
			(l : 'a list) (even : 'a list) (odd : 'a list) (p : int) : ('a list) * ('a list) =
		match l with
		| [] -> List.rev even, List.rev odd
		| x :: xs -> if p = 0 then evenOdd xs (x :: even) odd ((p + 1) mod 2)
				else evenOdd xs even (x :: odd) ((p + 1) mod 2)
	
	let rec evenOddInv (even : 'a list) (odd : 'a list) (temp : 'a list) (p : int) : 'a list =
		match even, odd with
		| [], [] -> List.rev temp
		| x :: xs, odd when p = 0 -> evenOddInv xs odd (x :: temp) ((p + 1) mod 2)
		| even, y :: ys when p = 1 -> evenOddInv even ys (y :: temp) ((p + 1) mod 2)
		| _ -> failwith "Lists cannot be alternated!"
	
	let intersperse (a : 'a) (l : 'a list) : 'a list =
		let rec helper (first : 'a list) (rest : 'a list) : 'a list =
			match first with
			| [] -> List.rev rest
			| [x] -> List.rev (x :: rest)
			| x :: xs -> helper xs (a :: (x :: rest))
		in helper l []
	
	let rec printList (l : 'a list) (f : 'a -> string) : string =
		let s = List.fold_left
				(fun s a -> if s = "[" then "[" ^ (f a) else s ^ ";" ^ (f a)) "[" l in
		s ^ "]"
	
	let rec getMatches (l : Brx.t list) (s : BS.t) (t : BS.t list) : BS.t list =
		match l with
		| [] -> List.rev t
		| [x] -> List.rev (s :: t)
		| x :: xs -> let s1, s2 = BS.concat_split x (concatList xs) s in
				getMatches xs s2 (s1 :: t)
	
	let langWhole (l : Brx.t list) (sep : Brx.t) : Brx.t =
		altList (List.map (fun l -> concatList (intersperse sep l)) (permutations l))
	
	let rec whichPerm
			(perms : int list list) (l : Brx.t list) (sep : Brx.t) (s : BS.t) :
	((int list) * (Brx.t list)) =
		match perms with
		| [] -> failwith "I have to match at least one!"
		| perm :: perms ->
				let lperm = Perms.permute_list perm l in
				let rgx = concatList (intersperse sep lperm) in
				if not (BS.match_rx rgx s) then whichPerm perms l sep s else perm, lperm
	
	let permCanonizer (cs : BL.Canonizer.t list) (c : BL.Canonizer.t) : BL.Canonizer.t =
		let l = List.fold_left (fun l c -> (BL.Canonizer.uncanonized_type c) :: l) [] cs in
		let l = List.rev l in
		let sep = BL.Canonizer.uncanonized_type c in
		let whole = langWhole l sep in
		let l' = List.fold_left (fun l c -> (BL.Canonizer.canonized_type c) :: l) [] cs in
		let l' = List.rev l' in
		let sep' = BL.Canonizer.canonized_type c in
		let kernel = concatList (intersperse sep' l') in
		let f (s : string) : string =
			let s = BS.of_string s in
			let perms = Perms.permutations (List.length l) in
			let perm, lperm = whichPerm perms l sep s in
			let matches = getMatches (intersperse sep lperm) s [] in
			let real, seps = evenOdd matches [] [] 0 in
			let real = Perms.permute_list (Perms.invert_permutation perm) real in
			let ss = List.map BS.to_string (evenOddInv real seps [] 0) in
			let ss = List.map2
					(fun c s -> BL.Canonizer.canonize c (BS.of_string s)) (intersperse c cs) ss in
			String.concat "" ss in BL.Canonizer.normalize info whole kernel f
	
	let get_id : G.rs * V.t =
		let g ( _ : ((unit -> V.t) -> unit) option) (v : V.t) : V.t =
			match v with
			| V.Rx (_, r) -> V.Can (info, BL.Canonizer.copy info r)
			| _ -> failwith "Wrong Arguments for id" in
		(G.Sort (SFunction ((Id.mk info "id"), SRegexp, SCanonizer)), V.Fun (info, g))
	
	let get_project : G.rs * V.t =
		let g ( _ : ((unit -> V.t) -> unit) option) (v : V.t) : V.t =
			match v with
			| V.Par(_, V.Rx (_, r) , V.Str (_, s)) ->
					V.Can (info, BL.Canonizer.normalize info r (Brx.mk_string s) (fun _ -> s))
			| _ -> failwith "Wrong Arguments for project" in
		let so = SProduct(SRegexp, SString) in
		(G.Sort (SFunction ((Id.mk info "project"), so, SCanonizer)), V.Fun (info, g))
	
	let get_perm : G.rs * V.t =
		let get_cans (l : V.t list) : BL.Canonizer.t list =
			let f (temp : BL.Canonizer.t list) (v : V.t) : BL.Canonizer.t list =
				match v with
				| V.Can (_, c) -> c :: temp
				| _ -> failwith "Malformed List"
			in List.fold_left f [] l in
		let g ( _ : ((unit -> V.t) -> unit) option) (v : V.t) : V.t =
			match v with
			| V.Par(_, l, V.Can (_, sep)) ->
					let l = List.rev (get_cans (toList l [])) in
					V.Can (info, permCanonizer l sep)
			| _ -> failwith "Wrong Arguments for perm" in
		let so = SProduct(SData([SCanonizer], list), SCanonizer) in
		(G.Sort (SFunction ((Id.mk info "perm"), so, SCanonizer)), V.Fun (info, g))
	
	let get_synth_can : G.rs * V.t =
		let f1 ( _ : ((unit -> V.t) -> unit) option) (v : V.t) : V.t =
			match v with
			| V.Can (_, c1) ->
					(let f2 ( _ : ((unit -> V.t) -> unit) option) (v : V.t) : V.t =
							match v with
							| V.Can (_, c2) ->
									(let f3 ( _ : ((unit -> V.t) -> unit) option) (l : V.t) : V.t =
											match l with
											| V.Vnt (_, _, _, _) ->
													let s1, s2 = brxToLrx (BL.Canonizer.canonized_type c1),
														brxToLrx (BL.Canonizer.canonized_type c2) in
													let l = getStrings (toList l []) in
													let lens = gen_lens RegexContext.empty LensContext.empty s1 s2 l in
													let lens = match lens with
														| None -> failwith "Could not synth_from_regexp lens"
														| Some lens -> sLensTobLens lens in
													let lens = (BL.MLens.left_quot info c1 lens) in
													V.Lns(info, BL.MLens.right_quot info lens c2)
											| _ -> failwith "Wrong arguments for synth_from_canonizers" in
										V.Fun (info, f3))
							| _ -> failwith "Wrong arguments for synth_from_canonizers" in
						V.Fun (info, f2))
			| _ -> failwith "Wrong arguments for synth_from_canonizers" in
		let sort =
			SFunction ((Id.mk info ""), SCanonizer,
				(SFunction ((Id.mk info ""), SCanonizer,
						(SFunction ((Id.mk info ""), SData([SProduct(SString, SString)], list),
								SLens))))) in (G.Sort sort, V.Fun (info, f1))
	
end

let interp_module m0 = match m0 with
	| Mod(i, m, nctx, ds) ->
			pc := 0;
			ic := 0;
			mc := 0;
			let qm = Qid.t_of_id m in
			let nctx' = nctx in
			let cev = CEnv.set_ctx (CEnv.empty qm) (qm:: nctx') in
			let wqo : ((unit -> V.t) -> unit) option =
				if Prefs.read Prefs.parallelPref
				then
					let wq = Workqueue.create () in
					Some (fun (f: unit -> V.t) -> Workqueue.enq f wq)
				else None in
			let new_cev = CEnv.push_ctx cev Bridge.synth in
			let new_cev = CEnv.update new_cev Bridge.synth Bridge.get_synth in
			let new_cev = CEnv.push_ctx new_cev Bridge.perm in
			let new_cev = CEnv.update new_cev Bridge.perm Bridge.get_perm in
			let new_cev = CEnv.push_ctx new_cev Bridge.project in
			let new_cev = CEnv.update new_cev Bridge.project Bridge.get_project in
			let new_cev = CEnv.push_ctx new_cev Bridge.id in
			let new_cev = CEnv.update new_cev Bridge.id Bridge.get_id in
			let new_cev = CEnv.push_ctx new_cev Bridge.synth_can in
			let new_cev = CEnv.update new_cev Bridge.synth_can Bridge.get_synth_can in
			let new_cev, _ = interp_mod_aux wqo new_cev [m] ds in
			(*let trying id (_, v) _ : unit = print_string (Bridge.vtoString id v) in
			let _ = CEnv.fold trying new_cev () in*)
			G.register_env (CEnv.get_ev new_cev) nctx' m;
			Trace.debug "parallel"
				(fun () ->
							msg "@[Checks:@ %d parallel, %d inline, %d mandatory@]@\n"
								!pc !ic !mc)