module Verification_Framework : sig
  type nat
  type complex
  type 'a mat
  val compose : complex mat list -> nat -> complex mat
  val inverses_exec : (complex mat list) list
  val insert_seq_exec :
    complex mat list -> nat -> complex mat list -> complex mat list
  val replace_gate_exec :
    complex mat list -> nat -> complex mat list -> complex mat list
  val apply_inverse_exec : complex mat list -> nat -> nat -> complex mat list
end = struct

type num = One | Bit0 of num | Bit1 of num;;

type int = Zero_int | Pos of num | Neg of num;;

let one_inta : int = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_int = ({zero = Zero_int} : int zero);;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

type nat = Zero_nat | Suc of nat;;

let rec equal_nata x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                     | Suc x2, Zero_nat -> false
                     | Suc x2, Suc y2 -> equal_nata x2 y2
                     | Zero_nat, Zero_nat -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec plus_nata x0 n = match x0, n with Zero_nat, n -> n
                    | Suc m, n -> plus_nata m (Suc n);;

let rec times_nata x0 n = match x0, n with Zero_nat, n -> Zero_nat
                     | Suc m, n -> plus_nata n (times_nata m n);;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a dvd = {times_dvd : 'a times};;

let times_nat = ({times = times_nata} : nat times);;

let dvd_nat = ({times_dvd = times_nat} : nat dvd);;

let one_nata : nat = Suc Zero_nat;;

let one_nat = ({one = one_nata} : nat one);;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_nat = ({plus = plus_nata} : nat plus);;

let zero_nat = ({zero = Zero_nat} : nat zero);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let semigroup_add_nat = ({plus_semigroup_add = plus_nat} : nat semigroup_add);;

let numeral_nat =
  ({one_numeral = one_nat; semigroup_add_numeral = semigroup_add_nat} :
    nat numeral);;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let power_nat = ({one_power = one_nat; times_power = times_nat} : nat power);;

let rec minus_nata m n = match m, n with m, Zero_nat -> m
                     | Zero_nat, n -> Zero_nat
                     | Suc m, Suc n -> minus_nata m n;;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

let minus_nat = ({minus = minus_nata} : nat minus);;

let rec less_eq_nat x0 n = match x0, n with Zero_nat, n -> true
                      | Suc m, n -> less_nat m n
and less_nat n x1 = match n, x1 with n, Zero_nat -> false
               | m, Suc n -> less_eq_nat m n;;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add;
    semiring_0_semiring_0_cancel : 'a semiring_0};;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult;
    semiring_comm_semiring : 'a semiring};;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring;
    semiring_0_comm_semiring_0 : 'a semiring_0};;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0;
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel;
    semiring_1_semiring_1_cancel : 'a semiring_1};;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult;
    monoid_mult_comm_monoid_mult : 'a monoid_mult;
    dvd_comm_monoid_mult : 'a dvd};;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult;
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0;
    semiring_1_comm_semiring_1 : 'a semiring_1};;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel;
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1;
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

type 'a interval =
  {linorder_interval : 'a linorder;
    comm_semiring_1_cancel_interval : 'a comm_semiring_1_cancel};;

let cancel_semigroup_add_nat =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
    nat cancel_semigroup_add);;

let ab_semigroup_add_nat =
  ({semigroup_add_ab_semigroup_add = semigroup_add_nat} :
    nat ab_semigroup_add);;

let cancel_ab_semigroup_add_nat =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat;
     minus_cancel_ab_semigroup_add = minus_nat}
    : nat cancel_ab_semigroup_add);;

let monoid_add_nat =
  ({semigroup_add_monoid_add = semigroup_add_nat; zero_monoid_add = zero_nat} :
    nat monoid_add);;

let comm_monoid_add_nat =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat;
     monoid_add_comm_monoid_add = monoid_add_nat}
    : nat comm_monoid_add);;

let cancel_comm_monoid_add_nat =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_nat;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
    : nat cancel_comm_monoid_add);;

let mult_zero_nat =
  ({times_mult_zero = times_nat; zero_mult_zero = zero_nat} : nat mult_zero);;

let semigroup_mult_nat =
  ({times_semigroup_mult = times_nat} : nat semigroup_mult);;

let semiring_nat =
  ({ab_semigroup_add_semiring = ab_semigroup_add_nat;
     semigroup_mult_semiring = semigroup_mult_nat}
    : nat semiring);;

let semiring_0_nat =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_nat;
     mult_zero_semiring_0 = mult_zero_nat; semiring_semiring_0 = semiring_nat}
    : nat semiring_0);;

let semiring_0_cancel_nat =
  ({cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat;
     semiring_0_semiring_0_cancel = semiring_0_nat}
    : nat semiring_0_cancel);;

let ab_semigroup_mult_nat =
  ({semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
    nat ab_semigroup_mult);;

let comm_semiring_nat =
  ({ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat;
     semiring_comm_semiring = semiring_nat}
    : nat comm_semiring);;

let comm_semiring_0_nat =
  ({comm_semiring_comm_semiring_0 = comm_semiring_nat;
     semiring_0_comm_semiring_0 = semiring_0_nat}
    : nat comm_semiring_0);;

let comm_semiring_0_cancel_nat =
  ({comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat;
     semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
    : nat comm_semiring_0_cancel);;

let monoid_mult_nat =
  ({semigroup_mult_monoid_mult = semigroup_mult_nat;
     power_monoid_mult = power_nat}
    : nat monoid_mult);;

let semiring_numeral_nat =
  ({monoid_mult_semiring_numeral = monoid_mult_nat;
     numeral_semiring_numeral = numeral_nat;
     semiring_semiring_numeral = semiring_nat}
    : nat semiring_numeral);;

let zero_neq_one_nat =
  ({one_zero_neq_one = one_nat; zero_zero_neq_one = zero_nat} :
    nat zero_neq_one);;

let semiring_1_nat =
  ({semiring_numeral_semiring_1 = semiring_numeral_nat;
     semiring_0_semiring_1 = semiring_0_nat;
     zero_neq_one_semiring_1 = zero_neq_one_nat}
    : nat semiring_1);;

let semiring_1_cancel_nat =
  ({semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat;
     semiring_1_semiring_1_cancel = semiring_1_nat}
    : nat semiring_1_cancel);;

let comm_monoid_mult_nat =
  ({ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat;
     monoid_mult_comm_monoid_mult = monoid_mult_nat;
     dvd_comm_monoid_mult = dvd_nat}
    : nat comm_monoid_mult);;

let comm_semiring_1_nat =
  ({comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat;
     comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat;
     semiring_1_comm_semiring_1 = semiring_1_nat}
    : nat comm_semiring_1);;

let comm_semiring_1_cancel_nat =
  ({comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat;
     comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat;
     semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
    : nat comm_semiring_1_cancel);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

let interval_nat =
  ({linorder_interval = linorder_nat;
     comm_semiring_1_cancel_interval = comm_semiring_1_cancel_nat}
    : nat interval);;

type rat = Frct of (int * int);;

let zero_rat : rat = Frct (Zero_int, one_inta);;

type real = Ratreal of rat;;

let zero_real : real = Ratreal zero_rat;;

let one_rat : rat = Frct (one_inta, one_inta);;

let one_real : real = Ratreal one_rat;;

type complex = Complex of real * real;;

let one_complexa : complex = Complex (one_real, zero_real);;

let one_complex = ({one = one_complexa} : complex one);;

let rec plus_num x0 x1 = match x0, x1 with One, One -> Bit0 One
                   | One, Bit0 n -> Bit1 n
                   | One, Bit1 n -> Bit0 (plus_num n One)
                   | Bit0 m, One -> Bit1 m
                   | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
                   | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
                   | Bit1 m, One -> Bit0 (plus_num m One)
                   | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
                   | Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One);;

let rec times_num
  m n = match m, n with m, One -> m
    | One, n -> n
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));;

let rec times_int k l = match k, l with k, Zero_int -> Zero_int
                    | Zero_int, l -> Zero_int
                    | Pos m, Pos n -> Pos (times_num m n)
                    | Pos m, Neg n -> Neg (times_num m n)
                    | Neg m, Pos n -> Neg (times_num m n)
                    | Neg m, Neg n -> Pos (times_num m n);;

let rec uminus_int = function Zero_int -> Zero_int
                     | Pos m -> Neg m
                     | Neg m -> Pos m;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec dup = function Zero_int -> Zero_int
              | Pos n -> Pos (Bit0 n)
              | Neg n -> Neg (Bit0 n);;

let rec plus_int k l = match k, l with k, Zero_int -> k
                   | Zero_int, l -> l
                   | Pos m, Pos n -> Pos (plus_num m n)
                   | Pos m, Neg n -> sub m n
                   | Neg m, Pos n -> sub n m
                   | Neg m, Neg n -> Neg (plus_num m n)
and sub x0 x1 = match x0, x1 with One, One -> Zero_int
          | Bit0 m, One -> Pos (bitM m)
          | Bit1 m, One -> Pos (Bit0 m)
          | One, Bit0 n -> Neg (bitM n)
          | One, Bit1 n -> Neg (Bit0 n)
          | Bit0 m, Bit0 n -> dup (sub m n)
          | Bit1 m, Bit1 n -> dup (sub m n)
          | Bit1 m, Bit0 n -> plus_int (dup (sub m n)) one_inta
          | Bit0 m, Bit1 n -> minus_int (dup (sub m n)) one_inta
and minus_int k l = match k, l with k, Zero_int -> k
                | Zero_int, l -> uminus_int l
                | Pos m, Pos n -> sub m n
                | Pos m, Neg n -> Pos (plus_num m n)
                | Neg m, Pos n -> Neg (plus_num m n)
                | Neg m, Neg n -> sub n m;;

let rec quotient_of (Frct x) = x;;

let rec less_eq_num x0 n = match x0, n with One, n -> true
                      | Bit0 m, One -> false
                      | Bit1 m, One -> false
                      | Bit0 m, Bit0 n -> less_eq_num m n
                      | Bit0 m, Bit1 n -> less_eq_num m n
                      | Bit1 m, Bit1 n -> less_eq_num m n
                      | Bit1 m, Bit0 n -> less_num m n
and less_num m x1 = match m, x1 with m, One -> false
               | One, Bit0 n -> true
               | One, Bit1 n -> true
               | Bit0 m, Bit0 n -> less_num m n
               | Bit0 m, Bit1 n -> less_eq_num m n
               | Bit1 m, Bit1 n -> less_num m n
               | Bit1 m, Bit0 n -> less_num m n;;

let rec less_eq_int x0 x1 = match x0, x1 with Zero_int, Zero_int -> true
                      | Zero_int, Pos l -> true
                      | Zero_int, Neg l -> false
                      | Pos k, Zero_int -> false
                      | Pos k, Pos l -> less_eq_num k l
                      | Pos k, Neg l -> false
                      | Neg k, Zero_int -> true
                      | Neg k, Pos l -> true
                      | Neg k, Neg l -> less_eq_num l k;;

let rec less_int x0 x1 = match x0, x1 with Zero_int, Zero_int -> false
                   | Zero_int, Pos l -> true
                   | Zero_int, Neg l -> false
                   | Pos k, Zero_int -> false
                   | Pos k, Pos l -> less_num k l
                   | Pos k, Neg l -> false
                   | Neg k, Zero_int -> true
                   | Neg k, Pos l -> true
                   | Neg k, Neg l -> less_num l k;;

let rec abs_int i = (if less_int i Zero_int then uminus_int i else i);;

let rec divmod_step_int
  l qr =
    (let (q, r) = qr in
      (if less_eq_int (abs_int l) (abs_int r)
        then (plus_int (times_int (Pos (Bit0 One)) q) one_inta, minus_int r l)
        else (times_int (Pos (Bit0 One)) q, r)));;

let rec divmod_int
  m x1 = match m, x1 with m, One -> (Pos m, Zero_int)
    | One, Bit0 n -> (Zero_int, Pos One)
    | One, Bit1 n -> (Zero_int, Pos One)
    | Bit0 m, Bit0 n ->
        (let (q, r) = divmod_int m n in (q, times_int (Pos (Bit0 One)) r))
    | Bit1 m, Bit0 n ->
        (let (q, r) = divmod_int m n in
          (q, plus_int (times_int (Pos (Bit0 One)) r) one_inta))
    | Bit0 m, Bit1 n ->
        (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
          else divmod_step_int (Pos (Bit1 n))
                 (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
    | Bit1 m, Bit1 n ->
        (if less_num m n then (Zero_int, Pos (Bit1 m))
          else divmod_step_int (Pos (Bit1 n))
                 (divmod_int (Bit1 m) (Bit0 (Bit1 n))));;

let rec fst (x1, x2) = x1;;

let rec of_bool _A = function false -> zero _A.zero_zero_neq_one
                     | true -> one _A.one_zero_neq_one;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

let rec equal_int x0 x1 = match x0, x1 with Zero_int, Zero_int -> true
                    | Zero_int, Pos l -> false
                    | Zero_int, Neg l -> false
                    | Pos k, Zero_int -> false
                    | Pos k, Pos l -> equal_num k l
                    | Pos k, Neg l -> false
                    | Neg k, Zero_int -> false
                    | Neg k, Pos l -> false
                    | Neg k, Neg l -> equal_num k l;;

let rec adjust_div
  (q, r) = plus_int q (of_bool zero_neq_one_int (not (equal_int r Zero_int)));;

let rec divide_int
  k ka = match k, ka with k, Zero_int -> Zero_int
    | Zero_int, k -> Zero_int
    | k, Pos One -> k
    | k, Neg One -> uminus_int k
    | Pos m, Pos n -> fst (divmod_int m n)
    | Neg m, Pos n -> uminus_int (adjust_div (divmod_int m n))
    | Pos m, Neg n -> uminus_int (adjust_div (divmod_int m n))
    | Neg m, Neg n -> fst (divmod_int m n);;

let rec snd (x1, x2) = x2;;

let rec adjust_mod
  l r = (if equal_int r Zero_int then Zero_int else minus_int (Pos l) r);;

let rec modulo_int
  k ka = match k, ka with k, Zero_int -> k
    | Zero_int, k -> Zero_int
    | k, Pos One -> Zero_int
    | k, Neg One -> Zero_int
    | Pos m, Pos n -> snd (divmod_int m n)
    | Neg m, Pos n -> adjust_mod n (snd (divmod_int m n))
    | Pos m, Neg n -> uminus_int (adjust_mod n (snd (divmod_int m n)))
    | Neg m, Neg n -> uminus_int (snd (divmod_int m n));;

let rec gcd_int
  k l = abs_int
          (if equal_int l Zero_int then k
            else gcd_int l (modulo_int (abs_int k) (abs_int l)));;

let rec normalize
  p = (if less_int Zero_int (snd p)
        then (let a = gcd_int (fst p) (snd p) in
               (divide_int (fst p) a, divide_int (snd p) a))
        else (if equal_int (snd p) Zero_int then (Zero_int, one_inta)
               else (let a = uminus_int (gcd_int (fst p) (snd p)) in
                      (divide_int (fst p) a, divide_int (snd p) a))));;

let rec plus_rat
  p q = Frct (let (a, c) = quotient_of p in
              let (b, d) = quotient_of q in
               normalize
                 (plus_int (times_int a d) (times_int b c), times_int c d));;

let rec plus_real (Ratreal x) (Ratreal y) = Ratreal (plus_rat x y);;

let rec re (Complex (x1, x2)) = x1;;

let rec im (Complex (x1, x2)) = x2;;

let rec plus_complexa
  x y = Complex (plus_real (re x) (re y), plus_real (im x) (im y));;

let plus_complex = ({plus = plus_complexa} : complex plus);;

let zero_complexa : complex = Complex (zero_real, zero_real);;

let zero_complex = ({zero = zero_complexa} : complex zero);;

let rec times_rat
  p q = Frct (let (a, c) = quotient_of p in
              let (b, d) = quotient_of q in
               normalize (times_int a b, times_int c d));;

let rec times_real (Ratreal x) (Ratreal y) = Ratreal (times_rat x y);;

let rec minus_rat
  p q = Frct (let (a, c) = quotient_of p in
              let (b, d) = quotient_of q in
               normalize
                 (minus_int (times_int a d) (times_int b c), times_int c d));;

let rec minus_real (Ratreal x) (Ratreal y) = Ratreal (minus_rat x y);;

let rec times_complexa
  x y = Complex
          (minus_real (times_real (re x) (re y)) (times_real (im x) (im y)),
            plus_real (times_real (re x) (im y)) (times_real (im x) (re y)));;

let times_complex = ({times = times_complexa} : complex times);;

let semigroup_add_complex =
  ({plus_semigroup_add = plus_complex} : complex semigroup_add);;

let ab_semigroup_add_complex =
  ({semigroup_add_ab_semigroup_add = semigroup_add_complex} :
    complex ab_semigroup_add);;

let semigroup_mult_complex =
  ({times_semigroup_mult = times_complex} : complex semigroup_mult);;

let semiring_complex =
  ({ab_semigroup_add_semiring = ab_semigroup_add_complex;
     semigroup_mult_semiring = semigroup_mult_complex}
    : complex semiring);;

let mult_zero_complex =
  ({times_mult_zero = times_complex; zero_mult_zero = zero_complex} :
    complex mult_zero);;

let monoid_add_complex =
  ({semigroup_add_monoid_add = semigroup_add_complex;
     zero_monoid_add = zero_complex}
    : complex monoid_add);;

let comm_monoid_add_complex =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_complex;
     monoid_add_comm_monoid_add = monoid_add_complex}
    : complex comm_monoid_add);;

let semiring_0_complex =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_complex;
     mult_zero_semiring_0 = mult_zero_complex;
     semiring_semiring_0 = semiring_complex}
    : complex semiring_0);;

type 'a mat = Abs_mat of (nat * (nat * (nat * nat -> 'a)));;

type 'a vec = Abs_vec of (nat * (nat -> 'a));;

let rec id x = (fun xa -> xa) x;;

let rec eq _A a b = equal _A a b;;

let rec comp f g = (fun x -> f (g x));;

let rec nth x0 x1 = match x0, x1 with x :: xs, Zero_nat -> x
              | x :: xs, Suc n -> nth xs n;;

let rec upt i j = (if less_nat i j then i :: upt (Suc i) j else []);;

let rec nat_of_num = function One -> one_nata
                     | Bit0 n -> (let m = nat_of_num n in plus_nata m m)
                     | Bit1 n -> (let m = nat_of_num n in Suc (plus_nata m m));;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec undef_mat
  nr nc f =
    (fun (i, a) ->
      nth (nth (map (fun ia -> map (fun j -> f (ia, j)) (upt Zero_nat nc))
                 (upt Zero_nat nr))
            i)
        a);;

let rec mk_mat
  nr nc f =
    (fun (i, j) ->
      (if less_nat i nr && less_nat j nc then f (i, j)
        else undef_mat nr nc f (i, j)));;

let rec mat xc xd xe = Abs_mat (xc, (xd, mk_mat xc xd xe));;

let x : complex mat
  = mat (nat_of_num (Bit0 One)) (nat_of_num (Bit0 One))
      (fun (i, j) -> (if equal_nata i j then zero_complexa else one_complexa));;

let rec uminus_rat p = Frct (let (a, b) = quotient_of p in (uminus_int a, b));;

let rec uminus_real (Ratreal x) = Ratreal (uminus_rat x);;

let rec uminus_complex x = Complex (uminus_real (re x), uminus_real (im x));;

let imaginary_unit : complex = Complex (zero_real, one_real);;

let y : complex mat
  = mat (nat_of_num (Bit0 One)) (nat_of_num (Bit0 One))
      (fun (i, j) ->
        (if equal_nata i j then zero_complexa
          else (if equal_nata i Zero_nat then uminus_complex imaginary_unit
                 else imaginary_unit)));;

let z : complex mat
  = mat (nat_of_num (Bit0 One)) (nat_of_num (Bit0 One))
      (fun (i, j) ->
        (if not (equal_nata i j) then zero_complexa
          else (if equal_nata i Zero_nat then one_complexa
                 else uminus_complex one_complexa)));;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec rep_mat (Abs_mat x) = x;;

let rec index_mat x = snd (snd (rep_mat x));;

let rec dim_row x = fst (rep_mat x);;

let rec undef_vec i = nth [] i;;

let rec mk_vec
  n f = (fun i -> (if less_nat i n then f i else undef_vec (minus_nata i n)));;

let rec vec xb xc = Abs_vec (xb, mk_vec xb xc);;

let rec col a j = vec (dim_row a) (fun i -> index_mat a (i, j));;

let rec dim_col x = fst (snd (rep_mat x));;

let rec row a i = vec (dim_col a) (fun j -> index_mat a (i, j));;

let cnot : complex mat
  = mat (nat_of_num (Bit0 (Bit0 One))) (nat_of_num (Bit0 (Bit0 One)))
      (fun (i, j) ->
        (if equal_nata i Zero_nat && equal_nata j Zero_nat then one_complexa
          else (if equal_nata i one_nata && equal_nata j one_nata
                 then one_complexa
                 else (if equal_nata i (nat_of_num (Bit0 One)) &&
                            equal_nata j (nat_of_num (Bit1 One))
                        then one_complexa
                        else (if equal_nata i (nat_of_num (Bit1 One)) &&
                                   equal_nata j (nat_of_num (Bit0 One))
                               then one_complexa else zero_complexa)))));;

let rec rep_vec (Abs_vec x) = x;;

let rec dim_vec x = fst (rep_vec x);;

let rec one_mat (_A1, _A2)
  n = mat n n (fun (i, j) -> (if equal_nata i j then one _A1 else zero _A2));;

let rec vec_index x = snd (rep_vec x);;

let rec sum_list _A
  xs = foldr (plus _A.semigroup_add_monoid_add.plus_semigroup_add) xs
         (zero _A.zero_monoid_add);;

let rec interval (_A1, _A2)
  a b = (if less _A2.linorder_interval.order_linorder.preorder_order.ord_preorder
              a b
          then a :: interval (_A1, _A2)
                      (plus _A2.comm_semiring_1_cancel_interval.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
                        a (one _A2.comm_semiring_1_cancel_interval.comm_semiring_1_comm_semiring_1_cancel.semiring_1_comm_semiring_1.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral))
                      b
          else (if eq _A1 a b then [a] else []));;

let rec scalar_prod _A
  v w = (let d = minus_nata (dim_vec w) one_nata in
          (if less_nat d (dim_vec w)
            then sum_list
                   _A.comm_monoid_add_semiring_0.monoid_add_comm_monoid_add
                   (map (fun i ->
                          times _A.mult_zero_semiring_0.times_mult_zero
                            (vec_index v i) (vec_index w i))
                     (interval (equal_nat, interval_nat) Zero_nat d))
            else zero _A.mult_zero_semiring_0.zero_mult_zero));;

let rec times_mat _A
  a b = mat (dim_row a) (dim_col b)
          (fun (i, j) -> scalar_prod _A (row a i) (col b j));;

let rec compose
  x0 n = match x0, n with [], n -> one_mat (one_complex, zero_complex) n
    | g :: gs, n -> times_mat semiring_0_complex (compose gs n) g;;

let inverses_exec : (complex mat list) list
  = [[x; x]; [y; y]; [z; z]; [cnot; cnot]];;

let rec insert_seq_exec
  x0 pos seq = match x0, pos, seq with [], pos, seq -> seq
    | g :: gs, Zero_nat, seq -> seq @ g :: gs
    | g :: gs, Suc pos, seq -> g :: insert_seq_exec gs pos seq;;

let rec replace_gate_exec
  x0 pos seq = match x0, pos, seq with [], pos, seq -> seq
    | g :: gs, Zero_nat, seq -> seq @ gs
    | g :: gs, Suc pos, seq -> g :: replace_gate_exec gs pos seq;;

let rec apply_inverse_exec
  qc pos k = insert_seq_exec qc pos (nth inverses_exec k);;

end;; (*struct Verification_Framework*)
