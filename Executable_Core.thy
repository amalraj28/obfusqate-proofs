theory Executable_Core
  imports Circuit
begin

text \<open>
  Matrix-only executable subset.
  This keeps the existing matrix representation and removes the problematic gates
  H, T, and Tdg from the executable layer for now.
\<close>

type_synonym exec_circuit = "complex mat list"

definition inverses_exec :: "complex mat list list" where
  "inverses_exec = [
      [X, X],
      [Y, Y],
      [Z, Z],
      [CNOT, CNOT]
    ]"

fun insert_seq_exec :: "exec_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> exec_circuit" where
  "insert_seq_exec [] pos seq = seq"
| "insert_seq_exec (g # gs) 0 seq = seq @ (g # gs)"
| "insert_seq_exec (g # gs) (Suc pos) seq = g # insert_seq_exec gs pos seq"

fun replace_gate_exec :: "exec_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> exec_circuit" where
  "replace_gate_exec [] pos seq = seq"
| "replace_gate_exec (g # gs) 0 seq = seq @ gs"
| "replace_gate_exec (g # gs) (Suc pos) seq = g # replace_gate_exec gs pos seq"

fun apply_inverse_exec :: "exec_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exec_circuit" where
  "apply_inverse_exec qc pos k = insert_seq_exec qc pos (inverses_exec ! k)"

abbreviation qc_xz :: exec_circuit where
  "qc_xz \<equiv> [X, Z]"

abbreviation qc_xyzs :: exec_circuit where
  "qc_xyzs \<equiv> [X, Y, Z, S]"

text \<open>Sanity checks on the executable-safe subset\<close>

value "compose [X, Z] 2"
value "insert_seq_exec [X, Z] 1 [X, X]"
value "replace_gate_exec [X, Z] 0 [Z, Z]"
value "apply_inverse_exec [X, Z] 1 0"
value "compose (insert_seq_exec [X, Z] 1 [X, X]) 2"
value "compose (replace_gate_exec [X, Z] 0 [Z, Z]) 2"

export_code compose insert_seq_exec replace_gate_exec inverses_exec apply_inverse_exec
  in OCaml
  module_name Verification_Framework
  file "executable3.ml"

end