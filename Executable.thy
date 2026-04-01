theory Executable
  imports InverseGates CloakedGates DelayedGates
begin

datatype gate_id = GX | GY | GZ | GH | GS | GT | GSdg | GTdg | GCNOT
                       
type_synonym circuit_exec = "gate_id list"

fun nth_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_opt [] _ = None"
| "nth_opt (x # xs) 0 = Some x"
| "nth_opt (x # xs) (Suc n) = nth_opt xs n"

definition insert_seq_exec :: "circuit_exec \<Rightarrow> nat \<Rightarrow> circuit_exec \<Rightarrow> circuit_exec" where
  "insert_seq_exec qc pos seq = take pos qc @ seq @ drop pos qc"

definition replace_gate_exec :: "circuit_exec \<Rightarrow> nat \<Rightarrow> circuit_exec \<Rightarrow> circuit_exec" where
  "replace_gate_exec qc pos seq = take pos qc @ seq @ drop (Suc pos) qc"

definition inverses_exec :: "circuit_exec list" where
  "inverses_exec = [
    [GX, GX],
    [GY, GY],
    [GZ, GZ],
    [GH, GH],
    [GT, GTdg],
    [GTdg, GT],
    [GS, GSdg],
    [GSdg, GS],
    [GCNOT, GCNOT]
  ]"

fun cloak_seq_exec :: "gate_id \<Rightarrow> circuit_exec list" where
  "cloak_seq_exec GX = [
      [GH, GZ, GH],
      [GS, GY, GS, GZ],
      [GZ, GSdg, GY, GSdg],
      [GH, GY, GZ, GH, GY],
      [GY, GH, GZ, GY, GH],
      [GH, GY, GH, GY, GSdg, GY, GS],
      [GSdg, GY, GS, GH, GY, GH, GY],
      [GS, GY, GSdg]
    ]"
| "cloak_seq_exec GY = [
      [GSdg, GX, GS],
      [GSdg, GX, GZ, GSdg],
      [GS, GZ, GX, GS]
    ]"
| "cloak_seq_exec GZ = [
      [GH, GX, GH],
      [GX, GS, GY, GS],
      [GSdg, GY, GSdg, GX],
      [GY, GH, GX, GY, GH],
      [GH, GY, GX, GH, GY],
      [GS, GS],
      [GT, GT, GT, GT]
    ]"
| "cloak_seq_exec GS = [
      [GT, GT],
      [GZ, GT, GZ, GT],
      [GTdg, GTdg, GZ]
    ]"
| "cloak_seq_exec _ = []"

fun delayed_seq_exec :: "gate_id \<Rightarrow> circuit_exec list" where
  "delayed_seq_exec GX = [
      [GH, GZ, GX, GH, GZ],
      [GH, GY, GH, GY, GZ, GX, GZ],
      [GH, GY, GH, GX, GY],
      [GY, GX, GH, GY, GH],
      [GZ, GH, GX, GZ, GH],
      [GZ, GX, GZ, GY, GH, GY, GH]
    ]"
| "delayed_seq_exec GY = [
      [GX, GH, GY, GH, GX]
    ]"
| "delayed_seq_exec GZ = [
      [GH, GY, GH, GZ, GY],
      [GY, GZ, GH, GY, GH],
      [GH, GY, GH, GY, GX, GZ, GX],
      [GX, GZ, GX, GY, GH, GY, GH],
      [GX, GH, GZ, GX, GH],
      [GH, GX, GZ, GH, GX],
      [GSdg, GZ, GS],
      [GS, GZ, GSdg]
    ]"
| "delayed_seq_exec GH = [
      [GX, GZ, GH, GX, GZ],
      [GZ, GX, GH, GZ, GX]
    ]"
| "delayed_seq_exec GS = [
      [GZ, GT, GS, GTdg, GZ],
      [GZ, GTdg, GS, GT, GZ],
      [GH, GY, GH, GS, GX]
    ]"
| "delayed_seq_exec GT = [
      [GZ, GSdg, GT, GS, GZ],
      [GZ, GS, GT, GSdg, GZ]
    ]"
| "delayed_seq_exec _ = []"

definition inverse_gate_exec :: "nat \<Rightarrow> circuit_exec \<Rightarrow> nat \<Rightarrow> circuit_exec option" where
  "inverse_gate_exec n qc pos =
    (case nth_opt inverses_exec n of
       None \<Rightarrow> None
     | Some seq \<Rightarrow> Some (insert_seq_exec qc pos seq))"

definition cloaked_gate_exec :: "circuit_exec \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> circuit_exec option" where
  "cloaked_gate_exec qc pos n =
    (case nth_opt qc pos of
       None \<Rightarrow> None
     | Some g \<Rightarrow>
         (case nth_opt (cloak_seq_exec g) n of
            None \<Rightarrow> None
          | Some seq \<Rightarrow> Some (replace_gate_exec qc pos seq)))"

definition delayed_gate_exec :: "circuit_exec \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> circuit_exec option" where
  "delayed_gate_exec qc pos n =
    (case nth_opt qc pos of
       None \<Rightarrow> None
     | Some g \<Rightarrow>
         (case nth_opt (delayed_seq_exec g) n of
            None \<Rightarrow> None
          | Some seq \<Rightarrow> Some (replace_gate_exec qc pos seq)))"

export_code nth_opt insert_seq_exec replace_gate_exec
  inverses_exec cloak_seq_exec delayed_seq_exec
  inverse_gate_exec cloaked_gate_exec delayed_gate_exec
  in OCaml
  module_name Verification_Framework
  file "executable.ml"

value "inverse_gate_exec 0 [GX, GZ, GS] 1"
value "cloaked_gate_exec [GX, GZ, GS] 0 2"
value "delayed_gate_exec [GX, GZ, GS] 1 0"
(*
context gate
begin

fun gate_eval :: "gate_id \<Rightarrow> complex mat" where
  "gate_eval GX = X"
| "gate_eval GY = Y"
| "gate_eval GZ = Z"
| "gate_eval GH = H"
| "gate_eval GS = S"
| "gate_eval GT = T"
| "gate_eval GSdg = Sdg"
| "gate_eval GTdg = Tdg"
| "gate_eval GCNOT = CNOT"


definition circuit_eval :: "circuit_exec \<Rightarrow> complex mat list" where
  "circuit_eval qc = map gate_eval qc"

lemma inverses_exec_matches:
  "map circuit_eval inverses_exec = inverses"
  by (simp add: circuit_eval_def inverses_exec_def inverses_def)

lemma cloak_seq_exec_matches:
  assumes "g \<in> {GX, GY, GZ, GS}"
  shows "map circuit_eval (cloak_seq_exec g) = cloak_seq (gate_eval g)"
  using assms
  apply (cases g) 
  
  apply (simp_all add: circuit_eval_def cloak_seq_def)
  
 

lemma delayed_seq_exec_matches:
  "map circuit_eval (delayed_seq_exec g) = delayed_seq (gate_eval g)"
  by (cases g) (simp_all add: circuit_eval_def delayed_seq_def)

lemma insert_seq_exec_matches:
  "circuit_eval (insert_seq_exec qc pos seq) =
    insert_seq (circuit_eval qc) pos (circuit_eval seq)"
  by (simp add: circuit_eval_def insert_seq_exec_def insert_seq_def)

lemma replace_gate_exec_matches:
  "circuit_eval (replace_gate_exec qc pos seq) =
    replace_gate (circuit_eval qc) pos (circuit_eval seq)"
  by (simp add: circuit_eval_def replace_gate_exec_def replace_gate_def)

lemma inverse_gate_exec_sound:
  assumes "inverse_gate_exec n qc pos = Some qc'"
  shows "\<exists>seq.
    nth_opt inverses n = Some seq \<and>
    circuit_eval qc' = insert_seq (circuit_eval qc) pos seq"
  using assms
  by (auto simp: inverse_gate_exec_def insert_seq_exec_matches inverses_exec_matches
      split: option.splits)

lemma cloaked_gate_exec_sound:
  assumes "cloaked_gate_exec qc pos n = Some qc'"
  shows "\<exists> g seq.
    nth_opt qc pos = Some g \<and>
    nth_opt (cloak_seq (gate_eval g)) n = Some seq \<and>
    circuit_eval qc' = replace_gate (circuit_eval qc) pos seq"
  using assms
  by (auto simp: cloaked_gate_exec_def replace_gate_exec_matches cloak_seq_exec_matches
      split: option.splits)

lemma delayed_gate_exec_sound:
  assumes "delayed_gate_exec qc pos n = Some qc'"
  shows "\<exists>g seq.
    nth_opt qc pos = Some g \<and>
    nth_opt (delayed_seq (gate_eval g)) n = Some seq \<and>
    circuit_eval qc' = replace_gate (circuit_eval qc) pos seq"
  using assms
  by (auto simp: delayed_gate_exec_def replace_gate_exec_matches delayed_seq_exec_matches
      split: option.splits)

end
*)
end
