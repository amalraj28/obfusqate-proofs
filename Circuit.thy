theory Circuit
  imports Sequences
begin

context gate
begin
type_synonym circuit = "complex mat list"

definition insert_seq :: "circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> circuit" where
  "insert_seq qc pos seq = take pos qc @ seq @ drop pos qc"

definition replace_gate :: "circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> circuit" where
  "replace_gate qc pos seq = take pos qc @ seq @ drop (Suc pos) qc"


lemma compose_append:
  assumes "\<forall>g \<in> set (xs @ ys). g \<in> carrier_mat d d"
  shows "compose (xs @ ys) d = compose ys d * compose xs d"
  using assms
proof (induction xs)
  case Nil
  have "compose ys d \<in> carrier_mat d d"
    using Nil.prems compose_carrier by simp
  then show ?case
    by (simp add: left_mult_one_mat)
next
  case (Cons x xs)
  have x_carrier: "x \<in> carrier_mat d d"
    using Cons.prems by simp
  have rest_carrier: "\<forall>g \<in> set (xs @ ys). g \<in> carrier_mat d d"
    using Cons.prems by simp
  have comp_xs_carrier: "compose xs d \<in> carrier_mat d d"
    using rest_carrier compose_carrier by simp
  have comp_ys_carrier: "compose ys d \<in> carrier_mat d d"
    using rest_carrier compose_carrier by simp
  have IH: "compose (xs @ ys) d = compose ys d * compose xs d"
    using Cons.IH rest_carrier by blast
  show ?case
    using IH x_carrier comp_xs_carrier comp_ys_carrier
    by (simp)
qed


lemma identity_insertion:
  assumes seq_id: "compose seq d = 1\<^sub>m d"
  assumes qc_carrier: "\<forall>g \<in> set qc. g \<in> carrier_mat d d"
  assumes seq_carrier: "\<forall>g \<in> set seq. g \<in> carrier_mat d d"
  shows "compose (insert_seq qc pos seq) d = compose qc d"
proof -
  have take_carrier: "\<forall>g \<in> set (take pos qc). g \<in> carrier_mat d d"
    using qc_carrier
    by (meson in_set_takeD)

  have drop_carrier: "\<forall>g \<in> set (drop pos qc). g \<in> carrier_mat d d"
    using qc_carrier
    by (meson in_set_dropD)

  have insert_expand:
    "compose (insert_seq qc pos seq) d = compose (take pos qc @ seq @ drop pos qc) d"
    by (simp add: insert_seq_def)

  have c1_carrier:
  "\<forall>g \<in> set ((take pos qc @ seq) @ drop pos qc). g \<in> carrier_mat d d"
  using take_carrier drop_carrier seq_carrier
  by auto

  have c1:
    "compose (take pos qc @ seq @ drop pos qc) d
     = compose (drop pos qc) d * compose (take pos qc @ seq) d"
  using compose_append[OF c1_carrier]
  by simp

  have c2_carrier:
    "\<forall>g \<in> set (take pos qc @ seq). g \<in> carrier_mat d d"
    using take_carrier seq_carrier
    by auto

  have c2:
    "compose (take pos qc @ seq) d = compose seq d * compose (take pos qc) d"
    using compose_append[OF c2_carrier]
    by simp

  have take_comp_carrier: "compose (take pos qc) d \<in> carrier_mat d d"
    using take_carrier compose_carrier by blast

  have take_drop_carrier:
    "\<forall>g \<in> set (take pos qc @ drop pos qc). g \<in> carrier_mat d d"
    using qc_carrier
    by simp

  have "compose (insert_seq qc pos seq) d
      = compose (drop pos qc) d * compose (take pos qc @ seq) d"
    using insert_expand c1 by simp
  also have "... = compose (drop pos qc) d * (compose seq d * compose (take pos qc) d)"
    using c2 by simp
  also have "... = compose (drop pos qc) d * (1\<^sub>m d * compose (take pos qc) d)"
    using seq_id by simp
  also have "... = compose (drop pos qc) d * compose (take pos qc) d"
    using take_comp_carrier by simp
  also have "... = compose (take pos qc @ drop pos qc) d"
    using compose_append[OF take_drop_carrier]
    by simp
  also have "... = compose qc d"
    by simp
  finally show ?thesis .
qed

lemma replacement_preservation:
  assumes pos_lt: "pos < length qc"
  assumes seq_eq: "compose seq d = qc ! pos"
  assumes qc_carrier: "\<forall>g \<in> set qc. g \<in> carrier_mat d d"
  assumes seq_carrier: "\<forall>g \<in> set seq. g \<in> carrier_mat d d"
  shows "compose (replace_gate qc pos seq) d = compose qc d"

proof -
  have take_carrier: "\<forall>g \<in> set (take pos qc). g \<in> carrier_mat d d"
    using qc_carrier
    by (meson in_set_takeD)

  have drop_carrier: "\<forall>g \<in> set (drop (Suc pos) qc). g \<in> carrier_mat d d"
    using qc_carrier
    by (meson in_set_dropD)

  have nth_carrier: "qc ! pos \<in> carrier_mat d d"
    using pos_lt qc_carrier by auto

  have replace_expand:
    "compose (replace_gate qc pos seq) d = compose (take pos qc @ seq @ drop (Suc pos) qc) d"
    by (simp add: replace_gate_def)

  have c1_carrier:
    "\<forall>g \<in> set ((take pos qc @ seq) @ drop (Suc pos) qc). g \<in> carrier_mat d d"
    using take_carrier drop_carrier seq_carrier by auto

  have c1:
    "compose (take pos qc @ seq @ drop (Suc pos) qc) d
     = compose (drop (Suc pos) qc) d * compose (take pos qc @ seq) d"
    using compose_append[OF c1_carrier] by simp

  have c2_carrier:
    "\<forall>g \<in> set (take pos qc @ seq). g \<in> carrier_mat d d"
    using take_carrier seq_carrier by auto

  have c2:
    "compose (take pos qc @ seq) d = compose seq d * compose (take pos qc) d"
    using compose_append[OF c2_carrier]
    by simp

  have take_one_carrier:
    "\<forall>g \<in> set (take pos qc @ [qc ! pos]). g \<in> carrier_mat d d"
    using take_carrier nth_carrier by simp

  have decomp_qc:
    "qc = take pos qc @ [qc ! pos] @ drop (Suc pos) qc"
    using pos_lt
  proof (induction qc arbitrary: pos)
    case Nil
    then show ?case by simp
  next
    case (Cons a qc)
    then show ?case
    proof (cases pos)
      case 0
      then show ?thesis by simp
    next
      case (Suc n)
      then show ?thesis
        using Cons.IH Cons.prems
        by simp
    qed
  qed

  have one_gate_comp:
    "compose (take pos qc @ [qc ! pos]) d = qc ! pos * compose (take pos qc) d"
  proof -
    have "compose (take pos qc @ [qc ! pos]) d
        = compose [qc ! pos] d * compose (take pos qc) d"
      using compose_append[of "take pos qc" "[qc ! pos]" d, OF take_one_carrier]
      by simp
    also have "... = (1\<^sub>m d * qc ! pos) * compose (take pos qc) d"
      by simp
    also have "... = qc ! pos * compose (take pos qc) d"
      using nth_carrier
      by simp
    finally show ?thesis .
  qed

  have c3_carrier:
    "\<forall>g \<in> set ((take pos qc @ [qc ! pos]) @ drop (Suc pos) qc). g \<in> carrier_mat d d"
    using take_carrier drop_carrier nth_carrier
    by auto

  have "compose (replace_gate qc pos seq) d
      = compose (take pos qc @ seq @ drop (Suc pos) qc) d"
    using replace_expand by simp
  also have "... = compose (drop (Suc pos) qc) d * compose (take pos qc @ seq) d"
    using c1 by simp
  also have "... = compose (drop (Suc pos) qc) d * (compose seq d * compose (take pos qc) d)"
    using c2 by simp
  also have "... = compose (drop (Suc pos) qc) d * (qc ! pos * compose (take pos qc) d)"
    using seq_eq by simp
  also have "... = compose (drop (Suc pos) qc) d * compose (take pos qc @ [qc ! pos]) d"
    using one_gate_comp
    by simp
  also have "... = compose (take pos qc @ [qc ! pos] @ drop (Suc pos) qc) d"
    using compose_append[of "take pos qc @ [qc ! pos]" "drop (Suc pos) qc" d, OF c3_carrier]
    by simp
  also have "... = compose qc d"
    using decomp_qc by simp
  finally show ?thesis .
qed

end
end