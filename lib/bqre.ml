module L = Lang
module BL = Blenses
module BS = Bstring
module Perms = BL.Permutations
module Perm = Permutation.Permutation

let msg = Util.format

let rec permutations (l : 'a list) : 'a list list =
    List.map (fun m -> Perms.permute_list m l) (Perms.permutations (List.length l))

let rec even_odd
        (l : 'a list) (even : 'a list) (odd : 'a list) (p : int) : ('a list) * ('a list) =
    match l with
    | [] -> List.rev even, List.rev odd
    | x :: xs -> if p = 0 then even_odd xs (x :: even) odd ((p + 1) mod 2)
            else even_odd xs even (x :: odd) ((p + 1) mod 2)

let rec even_odd_inv (even : 'a list) (odd : 'a list) (temp : 'a list) (p : int) : 'a list =
    match even, odd with
    | [], [] -> List.rev temp
    | x :: xs, odd when p = 0 -> even_odd_inv xs odd (x :: temp) ((p + 1) mod 2)
    | even, y :: ys when p = 1 -> even_odd_inv even ys (y :: temp) ((p + 1) mod 2)
    | _ -> Berror.run_error (Info.I ("", (0, 0), (0, 0)))
                (fun () -> msg "Lists cannot be alternated!" )

let rec get_matches (l : Brx.t list) (s : BS.t) (t : BS.t list) : BS.t list =
    match l with
    | [] -> List.rev t
    | [x] -> List.rev (s :: t)
    | x :: xs -> let s1, s2 = BS.concat_split x (Brx.concat_list xs) s in
            get_matches xs s2 (s1 :: t)

let perm_canonizer (cs : BL.Canonizer.t list) (c : BL.Canonizer.t) : BL.Canonizer.t =
    let l = List.fold_left (fun l c -> (BL.Canonizer.uncanonized_type c) :: l) [] cs in
    let l = List.rev l in
    let sep = BL.Canonizer.uncanonized_type c in
    let whole = Brx.mk_perm l sep in
    let l' = List.fold_left (fun l c -> (BL.Canonizer.canonized_type c) :: l) [] cs in
    let l' = List.rev l' in
    let sep' = BL.Canonizer.canonized_type c in
    let kernel = Brx.concat_list (Brx.intersperse sep' l') in
    let f (s' : string) : string =
        let s = BS.of_string s' in
        let perm = match fst (Brx.which_perm l sep s') with
            | None -> []
            | Some l -> Perms.invert_permutation l in
        let lperm = Perms.permute_list perm l in
        let matches = get_matches (Brx.intersperse sep lperm) s [] in
        let real, seps = even_odd matches [] [] 0 in
        let real = Perms.permute_list (Perms.invert_permutation perm) real in
        let ss = List.map BS.to_string (even_odd_inv real seps [] 0) in
        let ss = List.map2
                (fun c s -> BL.Canonizer.canonize c (BS.of_string s)) (Brx.intersperse c cs) ss in
        String.concat "" ss in
    BL.Canonizer.normalize (Info.I ("", (0, 0), (0, 0))) whole kernel f
		