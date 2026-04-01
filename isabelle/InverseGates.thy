theory InverseGates
  imports Circuit
begin

context gate
begin

lemma inverse_insertion_preserves:
  assumes "seq \<in> set inverses"
  assumes qc_carrier: "\<forall>g \<in> set qc. g \<in> carrier_mat d d"
  assumes seq_carrier: "\<forall>g \<in> set seq. g \<in> carrier_mat d d"
  shows "compose (insert_seq qc pos seq) d = compose qc d"
proof -
  have "compose seq d = 1\<^sub>m d"
    using assms(1) inverse_pair_identity
    by (metis carrier_matD(1) compose.simps(1) length_greater_0_conv nth_mem
        seq_carrier)
  then show ?thesis
    using identity_insertion qc_carrier seq_carrier
    by blast
qed


lemma inverseGates:
  assumes n_lt: "n < length inverses"
  assumes qc_carrier: "\<forall>g \<in> set qc. g \<in> carrier_mat d d"
  assumes seq_carrier: "\<forall>g \<in> set (inverses ! n). g \<in> carrier_mat d d"
  shows "compose (insert_seq qc pos (inverses ! n)) d = compose qc d"
proof -
  have seq0_in: "((inverses ! n) ! 0) \<in> set (inverses ! n)"
    using inverses_def assms(1)
    by simp

  have dim_eq: "dim_row ((inverses ! n) ! 0) = d"
    using seq_carrier seq0_in
    by (metis carrier_matD(1))

  have seq_id: "compose (inverses ! n) d = 1\<^sub>m d"
    using valid_inverse_pairs[OF n_lt] dim_eq
    by simp

  show ?thesis
    using identity_insertion[OF seq_id qc_carrier seq_carrier]
    by simp
qed



end
end