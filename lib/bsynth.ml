open Gen
open Regexcontext
open Lenscontext

module L = Lang
module V = Bvalue
module BL = Blenses
module Perm = Permutation.Permutation

let msg = Util.format

(** let print_list (f : 'a -> string) (l : 'a list) : string =
	let rec helper (l : 'a list) (temp : string): string =
		match l with
		| [] -> temp ^ "]"
		| [x] -> temp ^ (f x) ^ "]"
		| x :: xs -> helper xs (temp ^ (f x) ^ "; ")
	in helper l "[" **)

let rec lrx_to_brx (r : L.Regex.t) (rc: RegexContext.t) (i : Info.t) : Brx.t =
	match r with
	| L.Regex.RegExEmpty -> Brx.empty
	| L.Regex.RegExBase s -> Brx.mk_string s
	| L.Regex.RegExConcat (r1, r2) -> Brx.mk_seq (lrx_to_brx r1 rc i) (lrx_to_brx r2 rc i)
	| L.Regex.RegExOr (r1, r2) -> Brx.mk_alt (lrx_to_brx r1 rc i) (lrx_to_brx r2 rc i)
	| L.Regex.RegExStar r -> Brx.mk_star (lrx_to_brx r rc i)
	| L.Regex.RegExVariable s ->
			match RegexContext.lookup rc s with
			| Some r -> Brx.mk_var (Lang.Id.string_of_id s) (lrx_to_brx r rc i)
			| None -> Berror.run_error i
						(fun () -> msg "@[%s is unbound" (Lang.Id.string_of_id s) )

let slens_to_blens
		(l : L.Lens.t) (rc: RegexContext.t) (lc : LensContext.t) (i : Info.t) : BL.MLens.t =
	let constLens (s1 : string) (s2 : string) : BL.MLens.t =
		BL.MLens.clobber i (Brx.mk_string s1) s2 (fun _ -> s1) in
	let rec helper (l : L.Lens.t) : BL.MLens.t =
		match l with
		| L.Lens.LensConst (s1, s2) -> constLens s1 s2
		| L.Lens.LensConcat (l1, l2) -> BL.MLens.concat i (helper l1) (helper l2)
		| L.Lens.LensSwap (l1, l2) -> BL.MLens.permute i [1;0] [(helper l1); (helper l2)]
		| L.Lens.LensUnion (l1, l2) -> BL.MLens.union i (helper l1) (helper l2)
		| L.Lens.LensCompose (l1, l2) -> BL.MLens.compose i (helper l2) (helper l1)
		| L.Lens.LensIterate l -> BL.MLens.star i (helper l)
		| L.Lens.LensIdentity r -> BL.MLens.copy i (lrx_to_brx r rc i)
		| L.Lens.LensInverse l -> BL.MLens.invert i (helper l)
		| L.Lens.LensVariable s ->
				BL.MLens.mk_var i (L.Id.string_of_id s)
					(helper (LensContext.lookup_impl_exn lc s))
		| L.Lens.LensPermute (s, l) ->
				BL.MLens.permute i (Perm.to_int_list s) (List.map (fun l -> helper l) l) in
	helper l

let get_strings (l : V.t list) : (string * string) list =
	let helper (temp : (string * string) list) (v : V.t) : (string * string) list =
		match v with
		| V.Par(_, V.Str(_, s1), V.Str(_, s2)) -> (s1, s2) :: temp
		| _ -> Berror.run_error (V.info_of_t v) (fun () -> msg "Expected a list here")
	in List.fold_left helper [] l

let synth (v1 : V.t) (v2 : V.t) (l : V.t) (rc : RegexContext.t) (lc : LensContext.t) =
	match v1 with
	| V.Rx (i1, r1) ->
			begin
				match v2 with
				| V.Rx (i2, r2) ->
						begin
							match l with
							| V.Vnt (i3, _, _, _) ->
									let s1 = Brx.brx_to_lrx r1 i1 rc in
									let s2 = Brx.brx_to_lrx r2 i2 rc in
									let l = get_strings (V.to_list l) in
									let lens = gen_lens rc lc s1 s2 (List.rev l) in
									let lens =
										match lens with
										| None -> Berror.run_error (Info.merge_inc i1 i2)
													(fun () -> msg "Could not synthesize lens" )
										| Some lens -> lens in
									let info = Info.merge_inc i1 i3 in
									let lens' = slens_to_blens lens rc lc info in
									info, lens'
							| _ -> Berror.run_error (V.info_of_t l)
										(fun () -> msg "Synth_from_regexp expects a list here" )
						end
				| _ -> Berror.run_error (V.info_of_t v2)
							(fun () -> msg "Synth_from_regexp expects a regular expression here" )
			end
	| V.Can (i1, c1) ->
			begin
				match v2 with
				| V.Can (i2, c2) ->
						begin
							match l with
							| V.Vnt (i3, _, _, _) ->
									let s1 = Brx.brx_to_lrx (BL.Canonizer.canonized_type c1) i1 rc in
									let s2 = Brx.brx_to_lrx (BL.Canonizer.canonized_type c2) i2 rc in
									let l = get_strings (V.to_list l) in
									let lens = gen_lens rc lc s1 s2 l in
									let info = Info.merge_inc i1 i3 in
									let lens = match lens with
										| None -> Berror.run_error info
													(fun () -> msg "Could not synthesize lens" )
										| Some lens -> slens_to_blens lens rc lc info in
									let lens = (BL.MLens.left_quot info c1 lens) in
									info, BL.MLens.right_quot info lens c2
							| _ -> Berror.run_error (V.info_of_t l)
										(fun () -> msg "synth expects a list here" )
						end
				| _ -> Berror.run_error (V.info_of_t v2)
							(fun () -> msg "synth expects a canonizer here" )
			end
	| _ -> Berror.run_error (V.info_of_t v1)
				(fun () -> msg "synth expects a regular expression or canonizer" )

(**let rec vtoString (id : Qid.t) (v : V.t) =
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
			| Some v -> "Vnt " ^ (Qid.string_of_t id) ^ " = (" ^ (vtoString id v) ^ ")"**)