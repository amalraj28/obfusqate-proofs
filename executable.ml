module Verification_Framework : sig
  type nat
  type gate_id
  val nth_opt : 'a list -> nat -> 'a option
  val inverses_exec : (gate_id list) list
  val cloak_seq_exec : gate_id -> (gate_id list) list
  val insert_seq_exec : gate_id list -> nat -> gate_id list -> gate_id list
  val delayed_seq_exec : gate_id -> (gate_id list) list
  val replace_gate_exec : gate_id list -> nat -> gate_id list -> gate_id list
  val cloaked_gate_exec : gate_id list -> nat -> nat -> (gate_id list) option
  val delayed_gate_exec : gate_id list -> nat -> nat -> (gate_id list) option
  val inverse_gate_exec : nat -> gate_id list -> nat -> (gate_id list) option
end = struct

type nat = Zero_nat | Suc of nat;;

type gate_id = GX | GY | GZ | GH | GS | GT | GSdg | GTdg | GCNOT;;

let rec drop
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs -> (match n with Zero_nat -> x :: xs | Suc m -> drop m xs);;

let rec take
  n x1 = match n, x1 with n, [] -> []
    | n, x :: xs -> (match n with Zero_nat -> [] | Suc m -> x :: take m xs);;

let rec nth_opt x0 uu = match x0, uu with [], uu -> None
                  | x :: xs, Zero_nat -> Some x
                  | x :: xs, Suc n -> nth_opt xs n;;

let inverses_exec : (gate_id list) list
  = [[GX; GX]; [GY; GY]; [GZ; GZ]; [GH; GH]; [GT; GTdg]; [GTdg; GT]; [GS; GSdg];
      [GSdg; GS]; [GCNOT; GCNOT]];;

let rec cloak_seq_exec
  = function
    GX -> [[GH; GZ; GH]; [GS; GY; GS; GZ]; [GZ; GSdg; GY; GSdg];
            [GH; GY; GZ; GH; GY]; [GY; GH; GZ; GY; GH];
            [GH; GY; GH; GY; GSdg; GY; GS]; [GSdg; GY; GS; GH; GY; GH; GY];
            [GS; GY; GSdg]]
    | GY -> [[GSdg; GX; GS]; [GSdg; GX; GZ; GSdg]; [GS; GZ; GX; GS]]
    | GZ -> [[GH; GX; GH]; [GX; GS; GY; GS]; [GSdg; GY; GSdg; GX];
              [GY; GH; GX; GY; GH]; [GH; GY; GX; GH; GY]; [GS; GS];
              [GT; GT; GT; GT]]
    | GS -> [[GT; GT]; [GZ; GT; GZ; GT]; [GTdg; GTdg; GZ]]
    | GH -> []
    | GT -> []
    | GSdg -> []
    | GTdg -> []
    | GCNOT -> [];;

let rec insert_seq_exec qc pos seq = take pos qc @ seq @ drop pos qc;;

let rec delayed_seq_exec
  = function
    GX -> [[GH; GZ; GX; GH; GZ]; [GH; GY; GH; GY; GZ; GX; GZ];
            [GH; GY; GH; GX; GY]; [GY; GX; GH; GY; GH]; [GZ; GH; GX; GZ; GH];
            [GZ; GX; GZ; GY; GH; GY; GH]]
    | GY -> [[GX; GH; GY; GH; GX]]
    | GZ -> [[GH; GY; GH; GZ; GY]; [GY; GZ; GH; GY; GH];
              [GH; GY; GH; GY; GX; GZ; GX]; [GX; GZ; GX; GY; GH; GY; GH];
              [GX; GH; GZ; GX; GH]; [GH; GX; GZ; GH; GX]; [GSdg; GZ; GS];
              [GS; GZ; GSdg]]
    | GH -> [[GX; GZ; GH; GX; GZ]; [GZ; GX; GH; GZ; GX]]
    | GS -> [[GZ; GT; GS; GTdg; GZ]; [GZ; GTdg; GS; GT; GZ];
              [GH; GY; GH; GS; GX]]
    | GT -> [[GZ; GSdg; GT; GS; GZ]; [GZ; GS; GT; GSdg; GZ]]
    | GSdg -> []
    | GTdg -> []
    | GCNOT -> [];;

let rec replace_gate_exec qc pos seq = take pos qc @ seq @ drop (Suc pos) qc;;

let rec cloaked_gate_exec
  qc pos n =
    (match nth_opt qc pos with None -> None
      | Some g ->
        (match nth_opt (cloak_seq_exec g) n with None -> None
          | Some seq -> Some (replace_gate_exec qc pos seq)));;

let rec delayed_gate_exec
  qc pos n =
    (match nth_opt qc pos with None -> None
      | Some g ->
        (match nth_opt (delayed_seq_exec g) n with None -> None
          | Some seq -> Some (replace_gate_exec qc pos seq)));;

let rec inverse_gate_exec
  n qc pos =
    (match nth_opt inverses_exec n with None -> None
      | Some seq -> Some (insert_seq_exec qc pos seq));;

let () = print_endline "Running executable...";

end;; (*struct Verification_Framework*)
