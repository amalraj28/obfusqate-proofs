theory Sequences
  imports ObfusQate "HOL-Analysis.Complex_Transcendental"
begin

context gate
begin

abbreviation Sdg :: "complex mat" where
  "Sdg \<equiv> dagger S"


abbreviation Tdg :: "complex mat" where
  "Tdg \<equiv> dagger T"


definition cloak_seq :: "complex mat \<Rightarrow> complex mat list list" where
  "cloak_seq g = 
    (if g = X then [
      [H, Z, H],
      [S, Y, S, Z],
      [Z, Sdg, Y, Sdg],
      [H, Y, Z, H, Y],
      [Y, H, Z, Y, H],
      [H, Y, H, Y, Sdg, Y, S],
      [Sdg, Y, S, H, Y, H, Y],
      [S, Y, Sdg]
     ] else
     
     if g = Y then [
      [Sdg, X, S],
      [Sdg, X, Z, Sdg],
      [S, Z, X, S]
     ] else

     if g = Z then [
      [H, X, H],
      [X, S, Y, S],
      [Sdg, Y, Sdg, X],
      [Y, H, X, Y, H],
      [H, Y, X, H, Y],
      [S, S], [T, T, T, T]
     ] else
    
     if g = S then [
      [T, T], [Z, T, Z, T], [Tdg, Tdg, Z]
     ] else 
     
     [])"

(* A table of delayed gate sequences *)
definition delayed_seq :: "complex mat \<Rightarrow> complex mat list list" where
  "delayed_seq g = (
    if g = X then [
         [H, Z, X, H, Z],
         [H, Y, H, Y, Z, X, Z],
         [H, Y, H, X, Y],
         [Y, X, H, Y, H],
         [Z, H, X, Z, H],
         [Z, X, Z, Y, H, Y, H]
       ] else
     if g = Y then [
         [X, H, Y, H, X]
       ]else
     if g = Z then [
         [H, Y, H, Z, Y],
         [Y, Z, H, Y, H],
         [H, Y, H, Y, X, Z, X],
         [X, Z, X, Y, H, Y, H],
         [X, H, Z, X, H],
         [H, X, Z, H, X],
         [Sdg, Z, S],
         [S, Z, Sdg]
       ] else
     if g = H then [
         [X, Z, H, X, Z],
         [Z, X, H, Z, X]
       ] else
     if g = S then [
         [Z, T, S, Tdg, Z],
         [Z, Tdg, S, T, Z],
         [H, Y, H, S, X]
       ] else
     if g = T then [
         [Z, Sdg, T, S, Z],
         [Z, S, T, Sdg, Z]
       ] else
     [])"


definition inverses :: "complex mat list list" where
  "inverses = [
    [X, X],
    [Y, Y],
    [Z, Z],
    [H, H],
    [T, Tdg],
    [Tdg, T],
    [S, Sdg],
    [Sdg, S],
    [CNOT, CNOT]
  ]"


lemma dim_row_X[simp]: "dim_row X = 2"
  by (simp add: X_def)


lemma dim_col_X[simp]: "dim_col X = 2"
  by (simp add: X_def)


lemma dim_row_Y[simp]: "dim_row Y = 2"
  by (simp add: Y_def)


lemma dim_col_Y[simp]: "dim_col Y = 2"
  by (simp add: Y_def)


lemma dim_row_Z[simp]: "dim_row Z = 2"
  by (simp add: Z_def)


lemma dim_col_Z[simp]: "dim_col Z = 2"
  by (simp add: Z_def)


lemma dim_row_H[simp]: "dim_row H = 2"
  by (simp add: H_def)


lemma dim_col_H[simp]: "dim_col H = 2"
  by (simp add: H_def)


lemma dim_row_S[simp]: "dim_row S = 2"
  by (simp add: S_def)


lemma dim_col_S[simp]: "dim_col S = 2"
  by (simp add: S_def)


lemma dim_row_T[simp]: "dim_row T = 2"
  by (simp add: T_def)


lemma dim_col_T[simp]: "dim_col T = 2"
  by (simp add: T_def)


lemma dim_row_CNOT[simp]: "dim_row CNOT = 4"
  by (simp add: CNOT_def)


lemma dim_col_CNOT[simp]: "dim_col CNOT = 4"
  by (simp add: CNOT_def)


lemma Tdg_is_inv_T:
  "T * Tdg = 1\<^sub>m 2"
 apply(simp add: T_def times_mat_def one_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp: scalar_prod_def complex_mult_cnj Re_exp Im_exp of_real_def)  
  done


lemma T_is_inv_Tdg:
  "Tdg * T = 1\<^sub>m 2"
 apply(simp add: T_def times_mat_def one_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp add: mult.commute scalar_prod_def Re_exp Im_exp complex_mult_cnj of_real_def)  
  done


lemma Sdg_is_inv_S:
  "S * Sdg = 1\<^sub>m 2"
 apply(simp add: S_def times_mat_def one_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp: scalar_prod_def complex_mult_cnj Re_exp Im_exp of_real_def)  
  done


lemma S_is_inv_Sdg:
  "Sdg * S = 1\<^sub>m 2"
 apply(simp add: S_def times_mat_def one_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp add: mult.commute scalar_prod_def Re_exp Im_exp complex_mult_cnj of_real_def)  
  done


lemma inverse_pair_identity:
  assumes "seq \<in> set inverses"
  shows "compose seq (dim_row (seq ! 0)) = 1\<^sub>m (dim_row (seq ! 0))"
proof -
  from assms have                          
    "seq = [X, X] \<or>
     seq = [Y, Y] \<or>
     seq = [Z, Z] \<or>
     seq = [H, H] \<or>
     seq = [T, Tdg] \<or>
     seq = [Tdg, T] \<or>
     seq = [S, Sdg] \<or>
     seq = [Sdg, S] \<or>
     seq = [CNOT, CNOT]"
    by (simp add: inverses_def)

  then show ?thesis
    by (auto simp add: T_is_inv_Tdg Tdg_is_inv_T S_is_inv_Sdg Sdg_is_inv_S)
qed


lemma valid_inverse_pairs:
  fixes idx :: nat
  assumes "idx < length inverses"
  shows "compose (inverses ! idx) (dim_row ((inverses ! idx) ! 0)) = 1\<^sub>m (dim_row (inverses ! idx ! 0))"
proof -
  have "inverses ! idx \<in> set inverses"
    using assms by auto
  then show ?thesis
    using inverse_pair_identity by simp
qed

(* ---------- Inverse Pairs are totally proved to be correct above ---------- *)
(* ---- Cloaked Gates below ----------- *)
(*method solve_gate_eq uses defs =
  (simp add: defs times_mat_def one_mat_def complex_mult_cnj,
   rule cong_mat,
   auto simp add: scalar_prod_def Re_exp Im_exp of_real_def complex_mult_cnj mult.commute)
*)

lemma sqrt2_scale_identity[simp]:
  "(2 / sqrt 2) *\<^sub>R x = sqrt 2 *\<^sub>R x"
 by (simp add: real_div_sqrt)


lemma SYSZ_is_X[simp]: 
  "compose [S, Y, S, Z] 2 = X" 
  apply (auto simp add: S_def Y_def Z_def X_def times_mat_def)
  apply (rule cong_mat)
  by (auto simp add: scalar_prod_def)


lemma ZSdgYSdg_is_X[simp]:
  "compose [Z, Sdg, Y, Sdg] 2 = X"
  apply (auto simp: X_def Z_def S_def Y_def times_mat_def)
  apply (rule cong_mat)
  by (auto simp add: scalar_prod_def)


lemma HYZHY_is_X[simp]:
  "compose [H, Y, Z, H, Y] 2 = X"
    apply (auto simp: X_def Y_def H_def Z_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all

  apply (auto simp add: scalar_prod_def of_real_def)
  using sqrt2_scale_identity
  by (metis of_real_def of_real_divide of_real_numeral)+ 


lemma YHZYH_is_X[simp]:
  "compose [Y, H, Z, Y, H] 2 = X"
  apply (auto simp: X_def Y_def H_def Z_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  apply (simp add: scalar_prod_def of_real_def)
  by (simp add: scaleR_conv_of_real)

  
lemma HYHYSdgYS_is_X[simp]:
  "compose [H, Y, H, Y, Sdg, Y, S] 2 = X"
  apply (auto simp: X_def Y_def H_def Z_def S_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  apply (simp add: scalar_prod_def of_real_def complex_mult_cnj)
  using sqrt2_scale_identity
  by (metis of_real_def of_real_divide of_real_numeral) 


lemma SdgYSHYHY_is_X[simp]:
  "compose [Sdg, Y, S, H, Y, H, Y] 2 = X"
  apply (auto simp: X_def Y_def H_def S_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  apply (auto simp add: scalar_prod_def of_real_def mult.commute)
  using sqrt2_scale_identity
  by (simp add: scaleR_conv_of_real)+


lemma SYSdg_is_X[simp]:
  "compose [S, Y, Sdg] 2 = X"
  apply (auto simp: X_def Y_def S_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (simp add: scalar_prod_def)


lemma SdgXS_is_Y[simp]:
  "compose [Sdg, X, S] 2 = Y"
  apply (auto simp: X_def Y_def S_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (simp add: scalar_prod_def)


lemma SdgXZSdg_is_Y[simp]:
  "compose [Sdg, X, Z, Sdg] 2 = Y"
  apply (auto simp: X_def Z_def S_def Y_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (simp add: scalar_prod_def)


lemma SZXS_is_Y[simp]:
  "compose [S, Z, X, S] 2 = Y"
  apply (auto simp: X_def Z_def S_def Y_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (simp add: scalar_prod_def)


lemma XSYS_is_Z[simp]:
  "compose [X, S, Y, S] 2 = Z"
  apply (auto simp: X_def Z_def S_def Y_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (simp add: scalar_prod_def)


lemma SdgYSdgX_is_Z[simp]:
  "compose [Sdg, Y, Sdg, X] 2 = Z"
  apply (auto simp: X_def Z_def S_def Y_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (simp add: scalar_prod_def)


lemma YHXYH_is_Z[simp]:
  "compose [Y, H, X, Y, H] 2 = Z"
  apply (auto simp: X_def Z_def H_def Y_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  apply (simp add: scalar_prod_def of_real_def)
  by (simp add: scaleR_conv_of_real)


lemma HYXHY_is_Z[simp]:
  "compose [H, Y, X, H, Y] 2 = Z"
  apply (auto simp: X_def Z_def H_def Y_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  apply (simp add: scalar_prod_def of_real_def)
  using sqrt2_scale_identity
  by (metis of_real_def of_real_divide of_real_numeral)


lemma SS_is_Z[simp]:
  "compose [S, S] 2 = Z"
  apply (auto simp: X_def Z_def S_def Y_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (simp add: scalar_prod_def)


lemma TT_is_S[simp]:
  "compose [T, T] 2 = S"
  apply(simp add: T_def S_def times_mat_def one_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp: scalar_prod_def mult_exp_exp of_real_def)
  apply (auto simp: scaleR_conv_of_real)
  using cis_conv_exp cis_pi_half
  by auto


lemma TTTT_is_Z[simp]:
  "compose [T, T, T, T] 2 = Z"
  apply(simp add: T_def Z_def times_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp: scalar_prod_def mult_exp_exp of_real_def)
  by (simp add: scaleR_conv_of_real)  


lemma ZTZT_is_S[simp]:
  "compose [Z, T, Z, T] 2 = S"
  apply(simp add: T_def Z_def S_def times_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp: scalar_prod_def mult_exp_exp of_real_def)
  apply (simp add: scaleR_conv_of_real)
  using cis_conv_exp cis_pi_half
  by auto
  

lemma TdgTdgZ_is_S[simp]:
  "compose [Tdg, Tdg, Z] 2 = S"
  apply(simp add: T_def Z_def S_def times_mat_def complex_mult_cnj)
  apply(rule cong_mat)
    apply(auto simp: scalar_prod_def of_real_def)
  apply (simp add: scaleR_conv_of_real mult_exp_exp exp_cnj)
  using exp_of_minus_half_pi
  by fastforce


(* ---------- delayed_seq lemmas ---------- *)
lemma HZXHZ_is_X[simp]:
  "compose [H, Z, X, H, Z] 2 = X"
  apply (auto simp add: H_def Z_def X_def times_mat_def of_real_def)
  apply (rule cong_mat)
    apply (auto simp add: scalar_prod_def)
  by (simp add: scaleR_conv_of_real)+

lemma HYHYZXZ_is_X[simp]:
  "compose [H, Y, H, Y, Z, X, Z] 2 = X"
  apply (auto simp add: H_def Z_def X_def Y_def times_mat_def of_real_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: scalar_prod_def of_real_def)
  by (simp add: scaleR_conv_of_real)
  

lemma HYHXY_is_X[simp]:
  "compose [H, Y, H, X, Y] 2 = X"
  apply (auto simp add: H_def Y_def X_def times_mat_def)
  apply (rule cong_mat)
  apply auto
    apply (simp add: of_real_def)
   apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  using sqrt2_scale_identity
  by (metis of_real_def of_real_divide of_real_numeral)


lemma YXHYH_is_X[simp]:
  "compose [Y, X, H, Y, H] 2 = X"
  apply (auto simp add: H_def Y_def X_def times_mat_def)
  apply (rule cong_mat)
    apply (auto simp add: scalar_prod_def of_real_def)
  by (simp add: scaleR_conv_of_real)+


lemma ZHXZH_is_X[simp]:
  "compose [Z, H, X, Z, H] 2 = X"
  apply (auto simp add: H_def X_def Z_def times_mat_def)
  apply (rule cong_mat)
    apply (auto simp add: scalar_prod_def of_real_def)
  by (simp add: scaleR_conv_of_real)+
  

lemma ZXZYHYH_is_X[simp]:
  "compose [Z, X, Z, Y, H, Y, H] 2 = X"
  apply (auto simp add: H_def X_def Y_def Z_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  by (simp add: scaleR_conv_of_real)


lemma XHYHX_is_Y[simp]:
  "compose [X, H, Y, H, X] 2 = Y"
  apply (auto simp add: H_def X_def Y_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  by (simp add: scaleR_conv_of_real)


lemma HYHZY_is_Z[simp]:
  "compose [H, Y, H, Z, Y] 2 = Z"
  apply (auto simp add: H_def X_def Y_def Z_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)+
  using sqrt2_scale_identity
  by (metis (mono_tags, lifting) of_real_def of_real_divide
      of_real_numeral)
  

lemma YZHYH_is_Z[simp]:
  "compose [Y, Z, H, Y, H] 2 = Z"
  apply (auto simp add: H_def Z_def Y_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  by (simp add: scaleR_conv_of_real)


lemma HYHYXZX_is_Z[simp]:
  "compose [H, Y, H, Y, X, Z, X] 2 = Z"
  apply (auto simp add: H_def X_def Y_def Z_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  using sqrt2_scale_identity
  by (metis (mono_tags, lifting) of_real_def of_real_divide
      of_real_numeral)
  

lemma XZXYHYH_is_Z[simp]:
  "compose [X, Z, X, Y, H, Y, H] 2 = Z"
  apply (auto simp add: H_def X_def Y_def Z_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  by (simp add: scaleR_conv_of_real)


lemma XHZXH_is_Z[simp]:
  "compose [X, H, Z, X, H] 2 = Z"
  apply (auto simp add: H_def X_def Z_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  by (simp add: scaleR_conv_of_real)


lemma HXZHX_is_Z[simp]:
  "compose [H, X, Z, H, X] 2 = Z"
  apply (auto simp add: H_def X_def Z_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
    apply (simp add: of_real_def)
  apply (simp add: scalar_prod_def scaleR_conv_of_real)+
  apply (simp add: of_real_def)
  apply (auto simp add: scaleR_conv_of_real)
  apply (simp add: of_real_def)
  using sqrt2_scale_identity
  by (metis (no_types, opaque_lifting) of_real_def of_real_divide one_add_one
      scaleR_2)  
  

lemma SdgZS_is_Z[simp]:
  "compose [Sdg, Z, S] 2 = Z"
  apply (auto simp add: Z_def S_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
  by (simp add: scalar_prod_def scaleR_conv_of_real)

lemma SZSdg_is_Z[simp]:
  "compose [S, Z, Sdg] 2 = Z"
  apply (auto simp add: S_def Z_def times_mat_def)
  apply (rule cong_mat)
  apply simp_all
  by (simp add: scalar_prod_def scaleR_conv_of_real)


lemma XZHXZ_is_H[simp]:
  "compose [X, Z, H, X, Z] 2 = H"
  apply (auto simp add: X_def H_def Z_def times_mat_def)
  by (auto simp add: scalar_prod_def)


lemma ZXHZX_is_H[simp]:
  "compose [Z, X, H, Z, X] 2 = H"
  apply (auto simp add: X_def H_def Z_def times_mat_def)
  by (auto simp add: scalar_prod_def)


lemma ZTSTdgZ_is_S[simp]:
  "compose [Z, T, S, Tdg, Z] 2 = S"
  apply (auto simp add: T_def S_def Z_def times_mat_def)
  apply (rule cong_mat)
    apply simp_all
  by (auto simp add: scalar_prod_def exp_cnj mult_exp_exp)


lemma ZTdgSTZ_is_S[simp]:
  "compose [Z, Tdg, S, T, Z] 2 = S"
  apply (auto simp add: T_def Z_def S_def times_mat_def)
  apply (rule cong_mat)
  by (auto simp add: scalar_prod_def exp_cnj mult_exp_exp)


lemma HYHSX_is_S[simp]:
  "compose [H, Y, H, S, X] 2 = S"
  apply (simp add: H_def Y_def S_def X_def times_mat_def)
  apply (rule cong_mat)
  apply (auto simp add: scalar_prod_def mult.commute)
  by (simp add: of_real_def scaleR_2)


lemma ZSdgTSZ_is_T[simp]:
  "compose [Z, Sdg, T, S, Z] 2 = T"
  apply (simp add: Z_def S_def T_def times_mat_def)
  apply (rule cong_mat)
  by (auto simp add: scalar_prod_def mult.commute)


lemma ZSTSdgZ_is_T[simp]:
  "compose [Z, S, T, Sdg, Z] 2 = T"
  apply (simp add: Z_def S_def T_def times_mat_def)
  apply (rule cong_mat)
  by (auto simp add: scalar_prod_def mult.commute)


lemma X_neq_Y[simp]: "X \<noteq> Y"
proof
  assume "X = Y"
  then have "X $$ (0,1) = Y $$ (0,1)"
    by simp
  moreover have "X $$ (0,1) = 1"
    by (simp add: X_def)
  moreover have "Y $$ (0,1) = -\<i>"
    by (simp add: Y_def)
  ultimately show False
    by (metis complex_i_not_numeral complex_i_not_zero divide_i divide_self_if
        mult_1 numeral_One)  
qed


lemma X_neq_Z[simp]: "X \<noteq> Z"
proof
  assume "X = Z"
  then have "X $$ (0,1) = Z $$ (0,1)"
    by simp
  moreover have "X $$ (0,0) = 0"
    by (simp add: X_def)
  moreover have "Z $$ (0,0) = 1"
    by (simp add: Z_def)
  ultimately show False
    by (simp add: \<open>X = Z\<close>)
  
qed

lemma X_neq_S[simp]: "X \<noteq> S"
proof
  assume "X = S"
  then have "X $$ (0,0) = S $$ (0,0)"
    by simp
  moreover have "X $$ (0,0) = 0"
    by (simp add: X_def)
  moreover have "S $$ (0,0) = 1"
    by (simp add: S_def)
  ultimately show False
    by (simp add: \<open>X = S\<close>)
qed


lemma Y_neq_Z[simp]: "Y \<noteq> Z"
proof
  assume "Y = Z"
  then have "Y $$ (0,0) = Z $$ (0,0)"
    by simp
  moreover have "Y $$ (0,0) = 0"
    by (simp add: Y_def)
  moreover have "Z $$ (0,0) = 1"
    by (simp add: Z_def)
  ultimately show False
    by (simp add: \<open>Y = Z\<close>)
qed

lemma Y_neq_S[simp]: "Y \<noteq> S"
proof
  assume "Y = S"
  then have "Y $$ (0,0) = S $$ (0,0)"
    by simp
  moreover have "Y $$ (0,0) = 0"
    by (simp add: Y_def)
  moreover have "S $$ (0,0) = 1"
    by (simp add: S_def)
  ultimately show False
    by (simp add: \<open>Y = S\<close>)
qed

lemma Z_neq_S[simp]: "Z \<noteq> S"
proof
  assume "Z = S"
  then have "Z $$ (1,1) = S $$ (1,1)"
    by simp
  moreover have "Z $$ (1,1) = (-1::complex)"
    by (simp add: Z_def)
  moreover have "S $$ (1,1) = \<i>"
    by (simp add: S_def)
  ultimately show False
    by (metis i_squared mult_cancel_left1 one_neq_neg_one
        zero_neq_neg_one)
qed


lemma H_neq_X[simp]: "H \<noteq> X"
proof
  assume "H = X"
  then have "H $$ (0,0) = X $$ (0,0)"
    by simp
  moreover have "H $$ (0,0) = 1 / sqrt 2"
    by (simp add: H_def)
  moreover have "X $$ (0,0) = 0"
    by (simp add: X_def)
  ultimately show False
    by (simp add: \<open>H = X\<close>)
qed


lemma H_neq_Y[simp]: "H \<noteq> Y"
proof
  assume "H = Y"
  then have "H $$ (0,0) = Y $$ (0,0)"
    by simp
  moreover have "H $$ (0,0) = 1 / sqrt 2"
    by (simp add: H_def)
  moreover have "Y $$ (0,0) = 0"
    by (simp add: Y_def)
  ultimately show False
    by (simp add: \<open>H = Y\<close>)
qed


lemma H_neq_Z[simp]: "H \<noteq> Z"
proof
  assume "H = Z"
  then have "H $$ (0,0) = Z $$ (0,0)"
    by simp
  moreover have "H $$ (0,0) = 1 / sqrt 2"
    by (simp add: H_def)
  moreover have "Z $$ (0,0) = 1"
    by (simp add: Z_def)
  ultimately show False
    by (simp add: \<open>H = Z\<close>)
qed


lemma H_neq_S[simp]: "H \<noteq> S"
proof
  assume "H = S"
  then have "H $$ (0,0) = S $$ (0,0)"
    by simp
  moreover have "H $$ (0,0) = complex_of_real (1 / sqrt 2)"
    by (simp add: H_def)
  moreover have "S $$ (0,0) = 1"
    by (simp add: S_def)
  ultimately show False
    by (simp add: \<open>H = S\<close>)
qed


lemma H_neq_T[simp]: "H \<noteq> T"
proof
  assume "H = T"
  then have "H $$ (0,0) = T $$ (0,0)"
    by simp
  moreover have "H $$ (0,0) = 1 / sqrt 2"
    by (simp add: H_def)
  moreover have "T $$ (0,0) = 1"
    by (simp add: T_def)
  ultimately show False
    by (simp add: \<open>H = T\<close>)
qed


lemma T_neq_X[simp]: "T \<noteq> X"
proof
  assume "T = X"
  then have "T $$ (0,0) = X $$ (0,0)"
    by simp
  moreover have "T $$ (0,0) = 1"
    by (simp add: T_def)
  moreover have "X $$ (0,0) = 0"
    by (simp add: X_def)
  ultimately show False
    by (simp)
qed


lemma T_neq_Y[simp]: "T \<noteq> Y"
proof
  assume "T = Y"
  then have "T $$ (0,0) = Y $$ (0,0)"
    by simp
  moreover have "T $$ (0,0) = 1"
    by (simp add: T_def)
  moreover have "Y $$ (0,0) = 0"
    by (simp add: Y_def)
  ultimately show False
    by (simp)
qed

lemma T_neq_Z[simp]: "T \<noteq> Z"
proof
  assume "T = Z"
  then have "T $$ (1,1) = Z $$ (1,1)"
    by simp
  moreover have "T $$ (1,1) = exp (\<i> * pi / 4)"
    by (simp add: T_def)
  moreover have "Z $$ (1,1) = -1"
    by (simp add: Z_def)
  ultimately show False
    using TTTT_is_Z ZTZT_is_S \<open>T = Z\<close> by auto
qed


lemma T_neq_S[simp]: "T \<noteq> S"
proof
  assume "T = S"
  then have "T $$ (1,1) = S $$ (1,1)"
    by simp
  moreover have "T $$ (1,1) = exp (\<i> * pi / 4)"
    by (simp add: T_def)
  moreover have "S $$ (1,1) = \<i>"
    by (simp add: S_def)
  ultimately show False
    using SS_is_Z TT_is_S \<open>T = S\<close> by auto
qed


lemma cloak_seq_X_correct[simp]:
  assumes "seq \<in> set (cloak_seq X)"
  shows "compose seq 2 = X"
  using assms
  unfolding cloak_seq_def
  apply simp_all
  by (auto simp del:compose.simps) simp


lemma cloak_seq_Y_correct[simp]:
  assumes "seq \<in> set (cloak_seq Y)"
  shows "compose seq 2 = Y"
  using assms
  unfolding cloak_seq_def
  apply (simp add: not_sym)
  by (auto simp del: compose.simps)
  

lemma cloak_seq_Z_correct[simp]:
  assumes "seq \<in> set (cloak_seq Z)"
  shows "compose seq 2 = Z"
  using assms
  unfolding cloak_seq_def
  apply (simp add: not_sym)
  by (auto simp del: compose.simps) simp


lemma cloak_seq_S_correct[simp]:
  assumes "seq \<in> set (cloak_seq S)"
  shows "compose seq 2 = S"
  using assms
  unfolding cloak_seq_def
  apply (simp add: not_sym)
  by (auto simp del: compose.simps)


lemma cloak_seq_correct:
  assumes "seq \<in> set (cloak_seq g)"
  shows "compose seq (dim_row g) = g"
proof -
  have "g = X \<or> g = Y \<or> g = Z \<or> g = S"
    using assms
    unfolding cloak_seq_def
    by auto
  then show ?thesis
  proof
    assume "g = X"
    with assms show ?thesis
      by simp
  next
    assume "g = Y \<or> g = Z \<or> g = S"
    then show ?thesis
    proof
      assume "g = Y"
      with assms show ?thesis
        by simp
    next
      assume "g = Z \<or> g = S"
      then show ?thesis
      proof
        assume "g = Z"
        with assms show ?thesis
          by simp
      next
        assume "g = S"
        with assms show ?thesis
          by simp
      qed
    qed
  qed
qed
  

lemma cloak_seq_correct_idx:
  assumes "n < length (cloak_seq g)"
  shows "compose ((cloak_seq g) ! n) (dim_row g) = g"

proof -
  have "(cloak_seq g) ! n \<in> set (cloak_seq g)"
    using assms by auto
  then show ?thesis
    using cloak_seq_correct by simp
qed


lemma delayed_seq_X_correct[simp]:
  assumes "seq \<in> set (delayed_seq X)"
  shows "compose seq 2 = X"
  using assms
  unfolding delayed_seq_def
  apply simp_all
  by (auto simp del:compose.simps)


lemma delayed_seq_Y_correct[simp]:
  assumes "seq \<in> set (delayed_seq Y)"
  shows "compose seq 2 = Y"
  using assms
  unfolding delayed_seq_def
  by (simp add: not_sym del: compose.simps)


lemma delayed_seq_H_correct[simp]:
  assumes "seq \<in> set (delayed_seq H)"
  shows "compose seq 2 = H"
  using assms
  unfolding delayed_seq_def
  apply simp_all
  using XZHXZ_is_H ZXHZX_is_H by blast


lemma delayed_seq_Z_correct[simp]:
  assumes "seq \<in> set (delayed_seq Z)"
  shows "compose seq 2 = Z"
  using assms
  unfolding delayed_seq_def
  apply (simp add: not_sym)
  by (auto simp del: compose.simps) 


lemma delayed_seq_S_correct[simp]:
  assumes "seq \<in> set (delayed_seq S)"
  shows "compose seq 2 = S"
  using assms
  unfolding delayed_seq_def
  apply (simp add: not_sym)
  by (auto simp del: compose.simps)


lemma delayed_seq_T_correct[simp]:
  assumes "seq \<in> set (delayed_seq T)"
  shows "compose seq 2 = T"
  using assms
  unfolding delayed_seq_def
  apply (simp add: not_sym)
  by (auto simp del: compose.simps)
  

lemma delayed_seq_correct:
  assumes "seq \<in> set (delayed_seq g)"
  shows "compose seq (dim_row g) = g"
proof -
  have "g = X \<or> g = Y \<or> g = Z \<or> g = S \<or> g = H \<or> g = T"
    using assms
    unfolding delayed_seq_def
    by auto
  then show ?thesis
  proof
    assume "g = X"
    with assms show ?thesis
      by simp
  next
    assume "g = Y \<or> g = Z \<or> g = S \<or> g = H \<or> g = T"
    then show ?thesis
    proof
      assume "g = Y"
      with assms show ?thesis
        by simp
    next
      assume "g = Z \<or> g = S \<or> g = H \<or> g = T"
      then show ?thesis
      proof
        assume "g = Z"
        with assms show ?thesis
          by simp
      next
        assume "g = S \<or> g = H \<or> g = T"
        then show ?thesis
      proof
        assume "g = S"
        with assms show ?thesis
          by simp
      next
        assume "g = H \<or> g = T"
        then show ?thesis
      proof
        assume "g = H"
        with assms show ?thesis
          by simp
      next
        assume "g = T"
        with assms show ?thesis
          by simp
      qed
    qed
  qed
qed
qed
qed
  

lemma delayed_seq_correct_idx:
  assumes "n < length (delayed_seq g)"
  shows "compose ((delayed_seq g) ! n) (dim_row g) = g"

proof -
  have "(delayed_seq g) ! n \<in> set (delayed_seq g)"
    using assms by auto
  then show ?thesis
    using delayed_seq_correct by simp
qed

end
end