open Core.Std
open Util1
open String_utilities
open Lang
open Lens_utilities

(***** The main LensContext module {{{ *****)

module type LensContext_Sig = sig
    type t

    val empty                    : t
		val lookup		               : t -> id -> (lens * regex * regex) option
    val lookup_exn               : t -> id -> (lens * regex * regex)
    val lookup_type_exn          : t -> id -> regex * regex
    val lookup_impl_exn          : t -> id -> lens
    val insert_exn               : t -> id -> lens -> regex -> regex -> t
    val insert_list_exn          : t -> (id * lens * regex * regex) list -> t
    val create_from_list_exn     : (id * lens * regex * regex) list -> t
    val shortest_path            : t -> id -> id -> lens option
    val shortest_path_exn        : t -> id -> id -> lens
    val shortest_path_to_rep_elt : t -> id -> (id * lens)
    val autogen_id_from_base     : t -> string -> id
    val autogen_id               : t -> lens -> id
    val autogen_fresh_id         : t -> id
    val compare                  : t -> t -> comparison
    val to_string                : t -> string
    val hash                     : t -> int
		val fold                     : (id -> (lens * regex * regex) -> 'a -> 'a) -> 'a -> t -> 'a
end

(* add comments *)
(* declarative comments: google *)
(* SPECS not impl *)
(* here is the GOAL / meaning of what I'm doing *)
(* denotational semantics style *)
(* need to know as black box *)
module LensContext : LensContext_Sig = struct
  module DefsD = Dict.Make(
    struct
      type key = id
      type value = lens * regex * regex
      let compare_key = comparison_compare
      let compare_value =
        triple_compare
          lens_compare
          regex_compare
          regex_compare
      let key_to_string = ident
      let value_to_string =
        string_of_triple
          lens_to_string
          regex_to_string
          regex_to_string
    end)

  module OutgoingD = Dict.Make(
    struct
      type key = id
      type value = (lens * id) list
      let compare_key = comparison_compare
      let compare_value =
        dictionary_order
          (pair_compare
             lens_compare
             comparison_compare)
      let key_to_string = ident
      let value_to_string =
        string_of_list
          (string_of_pair
             lens_to_string
             ident)
    end)

  module DS = Disjointset.Make(
    struct
      type elt = id
      let compare_elt = comparison_compare
      let elt_to_string = ident
    end)

  type t = { defs     : DefsD.dict     ;
             outgoing : OutgoingD.dict ;
             equivs   : DS.set         ; }

  let empty = { defs     = DefsD.empty     ;
                outgoing = OutgoingD.empty ;
                equivs   = DS.empty        ; }

	let fold f a t = DefsD.fold f a t.defs
	
	let lookup (lc:t) (name:id) : (lens*regex*regex) option=
    DefsD.lookup lc.defs name
		
  let lookup_exn (lc:t) (name:id) : lens*regex*regex =
    DefsD.lookup_exn lc.defs name

  let lookup_type_exn (lc:t) (name:id) : regex*regex =
    let (_,r1,r2) = lookup_exn lc name in
    (r1,r2)

  let lookup_impl_exn (lc:t) (name:id) : lens =
    let (l,_,_) = lookup_exn lc name in
    l

  let update_defs (defs:DefsD.dict)
      (name:id) (l:lens) (r1:regex) (r2:regex)
    : DefsD.dict =
    if not (DefsD.member defs name) then
      DefsD.insert defs name (l,r1,r2)
    else
      failwith "bad insert"

  let update_outgoing (outgoing:OutgoingD.dict)
      (id1:id) (id2:id) (l:lens)
    : OutgoingD.dict =
    let outgoing = begin match OutgoingD.lookup outgoing id1 with
      | None -> OutgoingD.insert outgoing id1 [(l,id2)]
      | Some ol -> OutgoingD.insert outgoing id1 ((l,id2)::ol)
    end in
    let outgoing = begin match OutgoingD.lookup outgoing id2 with
      | None -> OutgoingD.insert outgoing id2 [(LensInverse l,id1)]
      | Some ol -> OutgoingD.insert outgoing id2 ((LensInverse l,id1)::ol)
    end in
    outgoing

  let update_equivs (equivs:DS.set) (id1:id) (id2:id)
    : DS.set =
    DS.union_elements
      equivs
      id1
      id2

  (* TODO: is this the right thing, simpler if just between userdefs ? *)
  let insert_exn (lc:t) (name:id) (l:lens) (r1:regex) (r2:regex) : t =
    begin match (r1,r2) with
      | (RegExVariable id1, RegExVariable id2) ->
        { defs     = update_defs lc.defs name l r1 r2      ;
          outgoing = update_outgoing lc.outgoing id1 id2 (LensVariable name);
          equivs   = update_equivs lc.equivs id1 id2       ; }
      | _ -> 
        { defs     = update_defs lc.defs name l r1 r2 ;
          outgoing = lc.outgoing                      ;
          equivs   = lc.equivs                        ; }
    end

  let insert_list_exn (lc:t) (nirsl:(string * lens * regex * regex) list) : t =
    List.fold_left
      ~f:(fun acc (name,l,r1,r2) -> insert_exn acc name l r1 r2)
      ~init:lc
      nirsl

  let get_outgoing_edges (outgoing:OutgoingD.dict) (source:id)
    : (lens * id) list =
    begin match OutgoingD.lookup outgoing source with
      | None -> []
      | Some connections -> connections
    end

  let create_from_list_exn (nirsl:(string * lens * regex * regex) list) : t =
    insert_list_exn empty nirsl

  let shortest_path (lc:t) (regex1_name:id) (regex2_name:id)
    : lens option =
    let outgoing = lc.outgoing in
    let rec shortest_path_internal (accums:(lens * id) list) : lens =
      let satisfying_path_option =
        List.find
          ~f:(fun (_,n) -> n = regex2_name)
          accums
      in
      begin match satisfying_path_option with
        | None ->
          let accums =
            List.concat_map
              ~f:(fun (l,n) ->
                  let valid_outgoing_edges =
                    List.filter
                      ~f:(fun (l',_) -> not (has_common_sublens l' l))
                      (get_outgoing_edges outgoing n)
                  in
                  List.map
                    ~f:(fun (l',n') -> (LensCompose (l',l),n'))
                    valid_outgoing_edges)
              accums
          in
          shortest_path_internal accums
        | Some (l,_) -> l
      end
    in
    let regex1_rep = DS.find_representative lc.equivs regex1_name in
    let regex2_rep = DS.find_representative lc.equivs regex2_name in
    if regex1_rep <> regex2_rep then
      None
    else if regex1_name = regex2_name then
      Some (LensIdentity (RegExVariable regex1_name))
    else
      Some (shortest_path_internal (get_outgoing_edges outgoing regex1_name))

  let shortest_path_exn (lc:t) (regex1_name:id) (regex2_name:id)
    : lens =
    begin match shortest_path lc regex1_name regex2_name with
      | None -> 
        failwith "regexes not in same equivalence class"
      | Some l -> l
    end

  let shortest_path_to_rep_elt (lc:t) (regex_name:id) : id * lens =
    let rep_element = DS.find_representative lc.equivs regex_name in
    let shortest_path = shortest_path_exn lc regex_name rep_element in
    (rep_element,shortest_path)

  let autogen_id_from_base (lc:t) (base:string) : id =
    let rec fresh nopt =
      let (x,next) =
        begin match nopt with
          | None -> (base,Some 1)
          | Some n -> (Printf.sprintf "%s%d" base n, Some (n+1))
        end
      in
      if DefsD.member lc.defs x then
        fresh next
      else
        x
    in
    fresh None

  let autogen_id (lc:t) (l:lens) : id =
    let base = lens_to_string l in
    let rec fresh nopt =
      let (x,next) =
        begin match nopt with
          | None -> (base,Some 1)
          | Some n -> (Printf.sprintf "%s%d" base n, Some (n+1))
        end
      in
      begin match DefsD.lookup lc.defs x with
        | Some (l',_,_) ->
          if l = l' then
            x
          else
            fresh next
        | _ -> x
      end
    in
    fresh None
      
  let autogen_fresh_id (lc:t) : id =
    autogen_id_from_base lc "l"

  let compare (lc1:t) (lc2:t) : comparison =
    (* only need to compare defs as rest is just memoization *)
    DefsD.compare
      lc1.defs
      lc2.defs

  let to_string (lc:t) : string =
    DefsD.to_string lc.defs

  let hash (lc:t) : int =
    let kvp_list = DefsD.as_kvp_list lc.defs in
    List.foldi
      ~f:(fun i acc (id,(l,r1,r2)) ->
          (regex_hash r1)
          lxor (regex_hash r2)
          lxor (lens_hash l)
          lxor (String.hash id)
          lxor (Int.hash i)
          lxor acc)
      ~init:(-25389029)
      kvp_list
end

(***** }}} *****)
