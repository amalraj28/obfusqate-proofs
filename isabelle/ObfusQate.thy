theory ObfusQate
  imports Main "Isabelle_Marries_Dirac.Quantum" "Jordan_Normal_Form.Matrix"
begin

(* Recursive composition of a circuit list to its resultant matrix *)
fun compose :: "complex mat list \<Rightarrow> nat \<Rightarrow> complex mat" where
  (* n is the dimension of the matrix, ie, (n \<times> n matrix) *)
  "compose [] n = 1\<^sub>m n" | 
  "compose (g # gs) n = (compose gs n) * g"

lemma compose_carrier:
  assumes "\<forall>M \<in> set gs. M \<in> carrier_mat d d"
  shows "compose gs d \<in> carrier_mat d d"
  using assms
  apply (induct gs)
  by simp_all
  
end                  