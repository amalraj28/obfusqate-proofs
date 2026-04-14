theory Executable_From_Lemmas
  imports InverseGates CloakedGates DelayedGates
begin

context gate
begin

text \<open>
  Executable entry points corresponding directly to the functionality stated by:
    - inverseGates
    - cloakedGates
    - delayedGates

  These are thin wrappers around the existing matrix-based transformations.
  No new transformation logic is introduced here.
\<close>

definition inverse_obfuscate ::
  "circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> circuit" where
  "inverse_obfuscate =
     (\<lambda>qc pos n.
        if pos \<le> length qc \<and> n < length [[X,X],[Y,Y]]
        then insert_seq qc pos ([[X,X],[Y,Y]] ! n)
        else qc)"

definition cloak_obfuscate ::
  "circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> circuit" where
  "cloak_obfuscate =
     (\<lambda>qc pos n.
        if pos < length qc \<and> n < length (cloak_seq (qc ! pos))
        then replace_gate qc pos ((cloak_seq (qc ! pos)) ! n)
        else qc)"

definition delayed_obfuscate ::
  "circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> circuit" where
  "delayed_obfuscate =
     (\<lambda>qc pos n.
        if pos < length qc \<and> n < length (delayed_seq (qc ! pos))
        then replace_gate qc pos ((delayed_seq (qc ! pos)) ! n)
        else qc)"

lemma inverse_obfuscate_eq:
  assumes "pos \<le> length qc"
  assumes "n < length inverses"
  shows "inverse_obfuscate qc pos n = insert_seq qc pos (inverses ! n)"
  using assms unfolding inverse_obfuscate_def by simp

lemma cloak_obfuscate_eq:
  assumes "pos < length qc"
  assumes "n < length (cloak_seq (qc ! pos))"
  shows "cloak_obfuscate qc pos n = replace_gate qc pos ((cloak_seq (qc ! pos)) ! n)"
  using assms unfolding cloak_obfuscate_def by simp

lemma delayed_obfuscate_eq:
  assumes "pos < length qc"
  assumes "n < length (delayed_seq (qc ! pos))"
  shows "delayed_obfuscate qc pos n = replace_gate qc pos ((delayed_seq (qc ! pos)) ! n)"
  using assms unfolding delayed_obfuscate_def by simp

abbreviation qc_safe :: circuit where
  "qc_safe \<equiv> [X, Z]"

value "compose qc_safe 2"

export_code inverse_obfuscate cloak_obfuscate delayed_obfuscate
  in OCaml module_name Executable_From_Lemmas file_prefix executable_from_lemmas

end

end
