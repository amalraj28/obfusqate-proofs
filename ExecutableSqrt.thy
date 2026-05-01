theory ExecutableSqrt
  imports Complex_Main
begin

text \<open>
  Executable symbolic complex numbers for H and T gates.

  We represent numbers of the form:

    a + b*i + c*k + d*(k*i)

  where k = 1 / sqrt 2.

  The point is that the executable layer never uses sqrt or exp directly.
  Instead, k is treated as a symbolic basis element with multiplication
  rules built in.
\<close>

datatype scomplex = SC rat rat rat rat
  \<comment> \<open>SC a b c d represents a + b*i + c*k + d*(k*i)\<close>


subsection \<open>Basic constants\<close>

definition sc_zero :: scomplex where
  "sc_zero = SC 0 0 0 0"

definition sc_one :: scomplex where
  "sc_one = SC 1 0 0 0"

definition sc_i :: scomplex where
  "sc_i = SC 0 1 0 0"

definition sc_k :: scomplex where
  "sc_k = SC 0 0 1 0"

definition sc_ki :: scomplex where
  "sc_ki = SC 0 0 0 1"

definition sc_minus_one :: scomplex where
  "sc_minus_one = SC (-1) 0 0 0"


subsection \<open>Arithmetic\<close>

fun add_sc :: "scomplex \<Rightarrow> scomplex \<Rightarrow> scomplex" where
  "add_sc (SC a b c d) (SC e f g h) =
     SC (a + e) (b + f) (c + g) (d + h)"

fun neg_sc :: "scomplex \<Rightarrow> scomplex" where
  "neg_sc (SC a b c d) = SC (-a) (-b) (-c) (-d)"

definition sub_sc :: "scomplex \<Rightarrow> scomplex \<Rightarrow> scomplex" where
  "sub_sc x y = add_sc x (neg_sc y)"

text \<open>
  Multiplication rules used:

    i^2      = -1
    k^2      = 1/2
    i*k      = k*i = ki
    i*ki     = -k
    ki*i     = -k
    k*ki     = (1/2)i
    ki*k     = (1/2)i
    ki^2     = -1/2
\<close>

fun mult_sc :: "scomplex \<Rightarrow> scomplex \<Rightarrow> scomplex" where
  "mult_sc (SC a b c d) (SC e f g h) =
     SC
       (a*e - b*f + (c*g - d*h) / 2)
       (a*f + b*e + (c*h + d*g) / 2)
       (a*g - b*h + c*e - d*f)
       (a*h + b*g + c*f + d*e)"

definition scale_sc :: "rat \<Rightarrow> scomplex \<Rightarrow> scomplex" where
  "scale_sc q z = mult_sc (SC q 0 0 0) z"


subsection \<open>Some useful derived constants\<close>

definition sc_half :: scomplex where
  "sc_half = SC (1/2) 0 0 0"

definition sc_minus_k :: scomplex where
  "sc_minus_k = neg_sc sc_k"

definition sc_phase_pi4 :: scomplex where
  "sc_phase_pi4 = add_sc sc_k sc_ki"
  \<comment> \<open>(1 + i) / sqrt 2 = k + k*i\<close>


subsection \<open>Small matrix layer\<close>

type_synonym smat = "scomplex list list"

definition mat2 :: "scomplex \<Rightarrow> scomplex \<Rightarrow> scomplex \<Rightarrow> scomplex \<Rightarrow> smat" where
  "mat2 a b c d = [[a, b], [c, d]]"

definition smat_id2 :: smat where
  "smat_id2 = mat2 sc_one sc_zero sc_zero sc_one"

fun dot_sc :: "scomplex list \<Rightarrow> scomplex list \<Rightarrow> scomplex" where
  "dot_sc [] [] = sc_zero"
| "dot_sc (x#xs) (y#ys) = add_sc (mult_sc x y) (dot_sc xs ys)"
| "dot_sc _ _ = sc_zero"

fun col2 :: "smat \<Rightarrow> nat \<Rightarrow> scomplex list" where
  "col2 [] j = []"
| "col2 (row#rows) j = row ! j # col2 rows j"

definition mmult2 :: "smat \<Rightarrow> smat \<Rightarrow> smat" where
  "mmult2 A B =
     mat2
       (dot_sc (A ! 0) (col2 B 0))
       (dot_sc (A ! 0) (col2 B 1))
       (dot_sc (A ! 1) (col2 B 0))
       (dot_sc (A ! 1) (col2 B 1))"

definition smat_scale :: "scomplex \<Rightarrow> smat \<Rightarrow> smat" where
  "smat_scale z A =
     map (map (\<lambda>x. mult_sc z x)) A"
                 

subsection \<open>Executable H and T gates\<close>

definition H_exec :: smat where
  "H_exec = mat2 sc_k sc_k sc_k sc_minus_k"

definition T_exec :: smat where
  "T_exec = mat2 sc_one sc_zero sc_zero sc_phase_pi4"


subsection \<open>Interpretation into Isabelle complex\<close>

definition ck :: complex where
  "ck = of_real (1 / sqrt 2)"

definition cki :: complex where
  "cki = \<i> * ck"

definition cminus_one :: complex where
  "cminus_one = -1"

definition chalf :: complex where
  "chalf = of_real (1/2)"

fun denote_sc :: "scomplex \<Rightarrow> complex" where
  "denote_sc (SC a b c d) =
      of_rat a
    + of_rat b * \<i>
    + of_rat c * ck
    + of_rat d * cki"

definition denote_mat :: "smat \<Rightarrow> complex list list" where
  "denote_mat A = map (map denote_sc) A"


subsection \<open>Algebra sanity lemmas\<close>

lemma add_sc_zero_left[simp]:
  "add_sc sc_zero z = z"
  by (cases z) (simp add: sc_zero_def)

lemma add_sc_zero_right[simp]:
  "add_sc z sc_zero = z"
  by (cases z) (simp add: sc_zero_def)

lemma neg_sc_neg[simp]:
  "neg_sc (neg_sc z) = z"
  by (cases z) simp

lemma sub_sc_self[simp]:
  "sub_sc z z = sc_zero"
  by (cases z) (simp add: sub_sc_def sc_zero_def)

lemma mult_sc_zero_left[simp]:
  "mult_sc sc_zero z = sc_zero"
  by (cases z) (simp add: sc_zero_def)

lemma mult_sc_zero_right[simp]:
  "mult_sc z sc_zero = sc_zero"
  by (cases z) (simp add: sc_zero_def)

lemma mult_sc_one_left[simp]:
  "mult_sc sc_one z = z"
  by (cases z) (simp add: sc_one_def)

lemma mult_sc_one_right[simp]:
  "mult_sc z sc_one = z"
  by (cases z) (simp add: sc_one_def)

lemma mult_sc_i_i[simp]:
  "mult_sc sc_i sc_i = sc_minus_one"
  by (simp add: sc_i_def sc_minus_one_def)

lemma mult_sc_k_k[simp]:
  "mult_sc sc_k sc_k = sc_half"
  by (simp add: sc_k_def sc_half_def)

lemma mult_sc_k_i[simp]:
  "mult_sc sc_k sc_i = sc_ki"
  by (simp add: sc_k_def sc_i_def sc_ki_def)

lemma mult_sc_i_k[simp]:
  "mult_sc sc_i sc_k = sc_ki"
  by (simp add: sc_k_def sc_i_def sc_ki_def)

lemma mult_sc_i_ki[simp]:
  "mult_sc sc_i sc_ki = sc_minus_k"
  by (simp add: sc_i_def sc_ki_def sc_minus_k_def sc_k_def)

lemma mult_sc_ki_i[simp]:
  "mult_sc sc_ki sc_i = sc_minus_k"
  by (simp add: sc_i_def sc_ki_def sc_minus_k_def sc_k_def)

lemma mult_sc_k_ki[simp]:
  "mult_sc sc_k sc_ki = SC 0 (1/2) 0 0"
  by (simp add: sc_k_def sc_ki_def)

lemma mult_sc_ki_k[simp]:
  "mult_sc sc_ki sc_k = SC 0 (1/2) 0 0"
  by (simp add: sc_k_def sc_ki_def)

lemma mult_sc_ki_ki[simp]:
  "mult_sc sc_ki sc_ki = SC (-1/2) 0 0 0"
  by (simp add: sc_ki_def)


subsection \<open>Gate shape sanity lemmas\<close>

lemma H_exec_entries:
  "H_exec = [[sc_k, sc_k], [sc_k, sc_minus_k]]"
  by (simp add: H_exec_def mat2_def)

lemma T_exec_entries:
  "T_exec = [[sc_one, sc_zero], [sc_zero, sc_phase_pi4]]"
  by (simp add: T_exec_def mat2_def)

lemma sc_phase_pi4_alt:
  "sc_phase_pi4 = SC 0 0 1 1"
  by (simp add: sc_phase_pi4_def sc_k_def sc_ki_def)

lemma neg_sc_zero[simp]:
  "neg_sc sc_zero = sc_zero"
  by (simp add: sc_zero_def)

lemma neg_sc_one[simp]:
  "neg_sc sc_one = SC (-1) 0 0 0"
  by (simp add: sc_one_def)

lemma neg_sc_k[simp]:
  "neg_sc sc_k = sc_minus_k"
  by (simp add: sc_k_def sc_minus_k_def)

lemma mult_sc_neg_left[simp]:
  "mult_sc (neg_sc x) y = neg_sc (mult_sc x y)"
  by (cases x; cases y; simp add: field_simps)

lemma mult_sc_neg_right[simp]:
  "mult_sc x (neg_sc y) = neg_sc (mult_sc x y)"
  by (cases x; cases y; simp add: field_simps)

lemma add_sc_neg_left[simp]:
  "add_sc (neg_sc x) x = sc_zero"
  by (cases x) (simp add: sc_zero_def)

lemma add_sc_neg_right[simp]:
  "add_sc x (neg_sc x) = sc_zero"
  by (cases x) (simp add: sc_zero_def)

lemma add_sc_half_half[simp]:
  "add_sc sc_half sc_half = sc_one"
  by (simp add: sc_half_def sc_one_def)

lemma mult_sc_k_minus_k[simp]:
  "mult_sc sc_k sc_minus_k = neg_sc sc_half"
  by (simp add: sc_k_def sc_minus_k_def sc_half_def)

lemma mult_sc_minus_k_k[simp]:
  "mult_sc sc_minus_k sc_k = neg_sc sc_half"
  by (simp add: sc_k_def sc_minus_k_def sc_half_def)

lemma mult_sc_minus_k_minus_k[simp]:
  "mult_sc sc_minus_k sc_minus_k = sc_half"
  by (simp add: sc_k_def sc_minus_k_def sc_half_def)

lemma add_sc_half_neg_half[simp]:
  "add_sc sc_half (neg_sc sc_half) = sc_zero"
  by (simp add: sc_half_def sc_zero_def)

lemma add_sc_neg_half_half[simp]:
  "add_sc (neg_sc sc_half) sc_half = sc_zero"
  by (simp add: sc_half_def sc_zero_def)

lemma dot_HH_00:
  "dot_sc [sc_k, sc_k] [sc_k, sc_k] = sc_one"
  unfolding sc_one_def
  by (simp add: sc_half_def)

lemma dot_HH_01:
  "dot_sc [sc_k, sc_k] [sc_k, sc_minus_k] = sc_zero"
  unfolding sc_zero_def sc_minus_k_def
  by (simp add: sc_half_def)

lemma dot_HH_10:
  "dot_sc [sc_k, sc_minus_k] [sc_k, sc_k] = sc_zero"
  unfolding sc_zero_def sc_minus_k_def
  by (simp add: sc_half_def)

lemma dot_HH_11:
  "dot_sc [sc_k, sc_minus_k] [sc_k, sc_minus_k] = sc_one"
  unfolding sc_one_def sc_minus_k_def
  by (simp add: sc_half_def)

lemma H_exec_squared:
  "mmult2 H_exec H_exec = smat_id2"
  unfolding mmult2_def H_exec_def smat_id2_def mat2_def
  by (simp add: dot_HH_00 dot_HH_01 dot_HH_10 dot_HH_11)


lemma denote_add:
  "denote_sc (add_sc x y) = denote_sc x + denote_sc y"
  by (cases x; cases y; simp add: complex_eq_iff algebra_simps add_divide_distrib of_rat_add)

lemma denote_neg:
  "denote_sc (neg_sc x) = - denote_sc x"
  by (cases x; simp add: complex_eq_iff algebra_simps of_rat_minus)

lemma inv_sqrt2_sq:
  "((1 / sqrt 2 :: real) * (1 / sqrt 2)) = 1/2"
  by (simp add: power2_eq_square)

lemma ck_sq[simp]:
  "ck * ck = chalf"
  by (simp add: ck_def chalf_def power2_eq_square of_real_def)

lemma ii_sq[simp]:
  "\<i> * \<i> = cminus_one"
  by (simp add: cminus_one_def)

lemma ck_ii[simp]:
  "ck * \<i> = cki"
  by (simp add: cki_def mult.commute)

lemma ii_ck[simp]:
  "\<i> * ck = cki"
  by (simp add: cki_def)

lemma cki_ii[simp]:
  "cki * \<i> = - ck"
  by (metis cki_def complex_i_mult_minus mult.commute)

lemma ii_cki[simp]:
  "\<i> * cki = - ck"
  by (metis cki_ii mult.commute)
  

lemma ck_cki[simp]:
  "ck * cki = chalf * \<i>"
  by (metis ck_ii ck_sq mult.assoc)


lemma cki_ck[simp]:
  "cki * ck = chalf * \<i>"
  by (simp add: mult.commute)
  

lemma cki_sq[simp]:
  "cki * cki = - chalf"
  by (metis ck_ii ck_sq ii_cki mult.assoc mult_minus_right)

lemma ck_ck_left[simp]:
  "ck * (ck * z) = chalf * z"
  by (simp add: mult.assoc)

lemma cki_cki_left[simp]:
  "cki * (cki * z) = (- chalf) * z"
  by (metis cki_sq mult.assoc)


lemma ck_cki_left[simp]:
  "ck * (cki * z) = (chalf * \<i>) * z"
  by (simp add: mult.assoc)

lemma cki_ck_left[simp]:
  "cki * (ck * z) = (chalf * \<i>) * z"
  by (simp add: mult.assoc)

lemma ii_ck_left[simp]:
  "\<i> * (ck * z) = cki * z"
  by (simp add: mult.assoc)

lemma ii_cki_left[simp]:
  "\<i> * (cki * z) = (- ck) * z"
  by (metis ab_semigroup_mult_class.mult_ac(1) ii_cki)
  

lemma ck_ii_left[simp]:
  "ck * (\<i> * z) = cki * z"
  by (simp add: mult.assoc mult.commute)

lemma cki_ii_left[simp]:
  "cki * (\<i> * z) = (- ck) * z"
  by (metis cki_ii mult.assoc)


lemma ii_ii_left[simp]:
  "\<i> * (\<i> * z) = cminus_one * z"
  by (simp add: cminus_one_def)

lemma cminus_one_times[simp]:
  "cminus_one * z = - z"
  by (simp add: cminus_one_def)

lemma chalf_times_of_rat[simp]:
  "chalf * of_rat q = of_rat (q / 2)"
  by (simp add: chalf_def of_rat_divide)

lemma of_rat_times_chalf[simp]:
  "of_rat q * chalf = of_rat (q / 2)"
  by (simp add: chalf_def of_rat_divide mult.commute)

lemma denote_mult:
  "denote_sc (mult_sc x y) = denote_sc x * denote_sc y"
  apply (cases x; cases y; simp add: algebra_simps ck_def cki_def chalf_def)

lemma denote_sub:
  "denote_sc (sub_sc x y) = denote_sc x - denote_sc y"
  by (simp add: sub_sc_def denote_add denote_neg)

lemma denote_H_exec:
  "denote_mat H_exec = [[ck, ck], [ck, - ck]]"
  sorry

lemma denote_T_exec:
  "denote_mat T_exec = [[1, 0], [0, ck + cki]]"
  sorry

lemma sc_phase_pi4_squared:
  "mult_sc sc_phase_pi4 sc_phase_pi4 = sc_i"
  sorry

lemma T_exec_squared:
  "mmult2 T_exec T_exec = mat2 sc_one sc_zero sc_zero sc_i"
  unfolding mmult2_def T_exec_def mat2_def
  by (simp add: sc_phase_pi4_squared)


subsection \<open>Quick sanity checks\<close>

value "H_exec"
value "T_exec"
value "mult_sc sc_k sc_k"
value "mult_sc sc_i sc_i"
value "mult_sc sc_k sc_i"
value "mult_sc sc_i sc_ki"

value "mmult2 H_exec H_exec"
value "mmult2 T_exec T_exec"

end