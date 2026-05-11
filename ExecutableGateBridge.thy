theory ExecutableGateBridge
  imports ExecutableSqrt1 ObfusQate
begin

lemma denote_H_exec_eq_H:
  "denote_mat H_exec = H"
proof (rule eq_matI)
  show "dim_row (denote_mat H_exec) = dim_row H"
    by (simp add: denote_mat_def H_exec_def mat2_def H_def)
next
  show "dim_col (denote_mat H_exec) = dim_col H"
    by (simp add: denote_mat_def H_exec_def mat2_def H_def)
next
  fix i j
  assume i: "i < dim_row H"
  assume j: "j < dim_col H"
  show "denote_mat H_exec $$ (i,j) = H $$ (i,j)"
    using i j
    by (simp add: denote_mat_def H_exec_def mat2_def H_def
                  sc_k_def sc_minus_k_def ck_def)
qed

lemma denote_T_exec_eq_T:
  "denote_mat T_exec = T"
proof (rule eq_matI)
  show "dim_row (denote_mat T_exec) = dim_row T"
    by (simp add: denote_mat_def T_exec_def mat2_def T_def)
next
  show "dim_col (denote_mat T_exec) = dim_col T"
    by (simp add: denote_mat_def T_exec_def mat2_def T_def)
next
  fix i j
  assume i: "i < dim_row T"
  assume j: "j < dim_col T"
    show "denote_mat T_exec $$ (i,j) = T $$ (i,j)"
  proof -
    have phase:
      "1 / complex_of_real (sqrt 2) + \<i> / complex_of_real (sqrt 2)
       = exp (\<i> * complex_of_real pi / 4)"
    proof -
      have "exp (\<i> * complex_of_real pi / 4) = cis (pi / 4)"
        using cis_conv_exp[of "pi / 4"]
        by simp
      also have "... =
        complex_of_real (cos (pi / 4)) + \<i> * complex_of_real (sin (pi / 4))"
        using Basics.exp_of_real cis_conv_exp by auto              
      also have "... =
        1 / complex_of_real (sqrt 2) + \<i> / complex_of_real (sqrt 2)"
        by (metis (no_types, lifting) add_divide_distrib ck_def cos_45
            divide_divide_eq_right mult_2 nonzero_mult_div_cancel_left
            of_real_1 of_real_add of_real_hom.hom_div one_add_one
            real_sqrt_divide real_sqrt_one sin_45 two_div_sqrt_two
            zero_neq_numeral)
      finally show ?thesis
        by simp
    qed

    show ?thesis
      using i j phase
      by (simp add: denote_mat_def T_exec_def mat2_def T_def
                    sc_one_def sc_zero_def sc_phase_pi4_def
                    sc_k_def sc_ki_def ck_def cki_def)
  qed
qed