theory CloakedGates
  imports Circuit
begin

context gate
begin

lemma cloak_replacement_preserves:
  assumes pos_lt: "pos < length qc"
  assumes gate: "qc ! pos = g"
  assumes seq_mem: "seq \<in> set (cloak_seq g)"
  assumes qc_carrier: "\<forall>g \<in> set qc. g \<in> carrier_mat d d"
  assumes seq_carrier: "\<forall>g \<in> set seq. g \<in> carrier_mat d d"
  shows "compose (replace_gate qc pos seq) d = compose qc d"
proof -
  have "compose seq d = g"
    using cloak_seq_correct seq_mem
    by (metis carrier_matD(1) gate nth_mem pos_lt qc_carrier)
  also have "... = qc ! pos"
    using gate by simp
  finally have "compose seq d = qc ! pos" .
  then show ?thesis
    using replacement_preservation pos_lt qc_carrier seq_carrier
    by blast
qed


lemma cloakedGates:
  assumes pos_lt: "pos < length qc"
  assumes n_lt: "n < length (cloak_seq (qc ! pos))"
  assumes qc_carrier: "\<forall>g \<in> set qc. g \<in> carrier_mat d d"
  assumes seq_carrier: "\<forall>g \<in> set ((cloak_seq (qc ! pos)) ! n). g \<in> carrier_mat d d"
  shows "compose (replace_gate qc pos ((cloak_seq (qc ! pos)) ! n)) d = compose qc d"

proof -
  have gate_in: "qc ! pos \<in> set qc"
    using pos_lt
    by simp

  have gate_carrier: "qc ! pos \<in> carrier_mat d d"
    using qc_carrier gate_in
    by blast

  have dim_eq: "dim_row (qc ! pos) = d"
    using gate_carrier
    by simp

  have seq_eq_dimrow:
    "compose ((cloak_seq (qc ! pos)) ! n) (dim_row (qc ! pos)) = qc ! pos"
    using cloak_seq_correct_idx[OF n_lt]
    by simp

  have seq_eq:
    "compose ((cloak_seq (qc ! pos)) ! n) d = qc ! pos"
    using seq_eq_dimrow dim_eq
    by simp

  show ?thesis
    using replacement_preservation[OF pos_lt seq_eq qc_carrier seq_carrier]
    by simp
qed

end
end