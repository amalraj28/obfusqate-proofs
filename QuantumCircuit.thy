theory QuantumCircuit
  imports Sequences
begin


record instruction =
  gate_matrix :: "complex mat" (* The gate itself *)
  gate_params :: "nat list" (* Which qubit(s) is/are the gate acting on *)
  gate_arity :: nat (* Number of qubits the gate is acting on *)


record quantum_circuit =
  num_qubits   :: nat
  instructions :: "instruction list"


definition make_instruction :: "complex mat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> instruction" where
  "make_instruction Gate arity params =
     \<lparr> gate_matrix = Gate, gate_params = params, gate_arity = arity\<rparr>" (* Bracket of a record *)


definition make_quantum_circuit :: "nat \<Rightarrow> instruction list \<Rightarrow> quantum_circuit" where
  "make_quantum_circuit n instrs =
     \<lparr> num_qubits = n, instructions = instrs \<rparr>"


definition empty_circuit :: "nat \<Rightarrow> quantum_circuit" where
  "empty_circuit n = make_quantum_circuit n []"


definition append_instruction :: "quantum_circuit \<Rightarrow> instruction \<Rightarrow> quantum_circuit" where
  "append_instruction qc instr = qc \<lparr> instructions := instructions qc @ [instr] \<rparr>"


definition valid_qubits :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "valid_qubits n qs \<longleftrightarrow> list_all (\<lambda>q. q < n) qs"


definition valid_instruction :: "nat \<Rightarrow> instruction \<Rightarrow> bool" where
  "valid_instruction n instr \<longleftrightarrow>
     gate_params instr \<noteq> [] \<and>
     distinct (gate_params instr) \<and>
     length (gate_params instr) = gate_arity instr \<and>
     valid_qubits n (gate_params instr)"


definition valid_quantum_circuit :: "quantum_circuit \<Rightarrow> bool" where
  "valid_quantum_circuit qc \<longleftrightarrow>
     list_all (valid_instruction (num_qubits qc)) (instructions qc)"


(*----------------  Prove validity preservation for constructors ----------------------*)

lemma valid_empty_circuit:
  "valid_quantum_circuit (empty_circuit n)"
  by (simp add:
      valid_quantum_circuit_def
      empty_circuit_def
      make_quantum_circuit_def)


lemma num_qubits_append_instruction:
  "num_qubits (append_instruction qc instr) = num_qubits qc"
  by (simp add: append_instruction_def)


lemma instructions_append_instruction:
  "instructions (append_instruction qc instr) = instructions qc @ [instr]"
  by (simp add: append_instruction_def)


lemma valid_append_instruction:
  assumes "valid_quantum_circuit qc"
  assumes "valid_instruction (num_qubits qc) instr"
  shows "valid_quantum_circuit (append_instruction qc instr)"
  using assms
  by (simp add:
      valid_quantum_circuit_def
      append_instruction_def)


definition insert_instructions_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> instruction list \<Rightarrow> quantum_circuit"
where
  "insert_instructions_at qc pos new_instrs =
     qc\<lparr> instructions := take pos (instructions qc) @ new_instrs @ drop pos (instructions qc) \<rparr>"


definition replace_instruction_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> instruction list \<Rightarrow> quantum_circuit"
where
  "replace_instruction_at qc pos new_instrs =
     qc\<lparr> instructions := take pos (instructions qc) @ new_instrs @ drop (Suc pos) (instructions qc) \<rparr>"


lemma num_qubits_insert_instructions_at:
  "num_qubits (insert_instructions_at qc pos new_instrs) = num_qubits qc"
  by (simp add: insert_instructions_at_def)


lemma instructions_insert_instructions_at:
  "instructions (insert_instructions_at qc pos new_instrs) =
     take pos (instructions qc) @ new_instrs @ drop pos (instructions qc)"
  by (simp add: insert_instructions_at_def)


lemma num_qubits_replace_instruction_at:
  "num_qubits (replace_instruction_at qc pos new_instrs) = num_qubits qc"
  by (simp add: replace_instruction_at_def)


lemma instructions_replace_instruction_at:
  "instructions (replace_instruction_at qc pos new_instrs) =
     take pos (instructions qc) @ new_instrs @ drop (Suc pos) (instructions qc)"
  by (simp add: replace_instruction_at_def)


lemma valid_insert_instructions_at:
  assumes "valid_quantum_circuit qc"
  assumes "list_all (valid_instruction (num_qubits qc)) new_instrs"
  shows "valid_quantum_circuit (insert_instructions_at qc pos new_instrs)"
  using assms
  apply (simp add: valid_quantum_circuit_def insert_instructions_at_def valid_instruction_def list_all_def)
  by (metis UnE in_set_dropD in_set_takeD)


lemma valid_replace_instruction_at:
  assumes "valid_quantum_circuit qc"
  assumes "list_all (valid_instruction (num_qubits qc)) new_instrs"
  shows "valid_quantum_circuit (replace_instruction_at qc pos new_instrs)"
  using assms
  apply (simp add:
      valid_quantum_circuit_def
      replace_instruction_at_def
      list_all_def)
  by (metis Un_iff in_set_dropD in_set_takeD)


definition valid_insert_pos :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_insert_pos qc pos \<longleftrightarrow> pos \<le> length (instructions qc)"


definition valid_replace_pos :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_replace_pos qc pos \<longleftrightarrow> pos < length (instructions qc)"


definition instructions_from_mats ::
  "complex mat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> instruction list"
where
  "instructions_from_mats mats arity params =
     map (\<lambda>G. make_instruction G arity params) mats"

lemma length_instructions_from_mats:
  "length (instructions_from_mats mats arity params) = length mats"
  by (simp add: instructions_from_mats_def)


lemma instructions_from_mats_Nil:
  "instructions_from_mats [] arity params = []"
  by (simp add: instructions_from_mats_def)


lemma instructions_from_mats_Cons:
  "instructions_from_mats (G # Gs) arity params =
     make_instruction G arity params # instructions_from_mats Gs arity params"
  by (simp add: instructions_from_mats_def)


lemma valid_instructions_from_mats:
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "length params = arity"
  assumes "valid_qubits n params"
  shows "list_all (valid_instruction n)
           (instructions_from_mats mats arity params)"
  using assms
  by (simp add: 
      instructions_from_mats_def
      valid_instruction_def
      make_instruction_def
      valid_qubits_def list_all_length)


lemma valid_replace_instruction_at_from_mats:
  assumes "valid_quantum_circuit qc"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "length params = arity"
  assumes "valid_qubits (num_qubits qc) params"
  shows "valid_quantum_circuit
           (replace_instruction_at qc pos
             (instructions_from_mats mats arity params))"
  using assms
  by (simp add:
      valid_replace_instruction_at
      valid_instructions_from_mats)


lemma valid_insert_instructions_at_from_mats:
  assumes "valid_quantum_circuit qc"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "length params = arity"
  assumes "valid_qubits (num_qubits qc) params"
  shows "valid_quantum_circuit
           (insert_instructions_at qc pos
             (instructions_from_mats mats arity params))"
  using assms
  by (simp add:
      valid_insert_instructions_at
      valid_instructions_from_mats)


definition replace_gate_by_mats_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> quantum_circuit"
where
  "replace_gate_by_mats_at qc pos mats =
     (let instr = instructions qc ! pos;
          arity = gate_arity instr;
          params = gate_params instr;
          new_instrs = instructions_from_mats mats arity params
      in replace_instruction_at qc pos new_instrs)"


lemma num_qubits_replace_gate_by_mats_at:
  "num_qubits (replace_gate_by_mats_at qc pos mats) = num_qubits qc"
  apply (simp add:
      replace_gate_by_mats_at_def
      instructions_from_mats_def
      replace_instruction_at_def make_instruction_def)
  by (metis (lifting) quantum_circuit.select_convs(1) quantum_circuit.surjective
      quantum_circuit.update_convs(2))


lemma instructions_replace_gate_by_mats_at:
  assumes "pos < length (instructions qc)"
  shows "instructions (replace_gate_by_mats_at qc pos mats) =
     take pos (instructions qc) @
     instructions_from_mats mats
       (gate_arity ((instructions qc) ! pos))
       (gate_params ((instructions qc) ! pos)) @
     drop (Suc pos) (instructions qc)"
  using assms
  apply (simp add:
      replace_gate_by_mats_at_def
      replace_instruction_at_def
      instructions_from_mats_def
      make_instruction_def)
  by (metis instructions_replace_instruction_at replace_instruction_at_def)


lemma valid_replace_gate_by_mats_at:
  assumes "valid_quantum_circuit qc"
  assumes "pos < length (instructions qc)"
  shows "valid_quantum_circuit (replace_gate_by_mats_at qc pos mats)"
proof -
  let ?instr = "(instructions qc) ! pos"
  have instr_valid:
    "valid_instruction (num_qubits qc) ?instr"
    using assms
    by (simp add:
        valid_quantum_circuit_def
        list_all_iff)

  have params_nonempty:
    "gate_params ?instr \<noteq> []"
    using instr_valid
    by (simp add: valid_instruction_def)

  have params_distinct:
    "distinct (gate_params ?instr)"
    using instr_valid
    by (simp add: valid_instruction_def)

  have params_length:
    "length (gate_params ?instr) = gate_arity ?instr"
    using instr_valid
    by (simp add: valid_instruction_def)

  have params_valid:
    "valid_qubits (num_qubits qc) (gate_params ?instr)"
    using instr_valid
    by (simp add: valid_instruction_def)

  have new_instrs_valid:
    "list_all (valid_instruction (num_qubits qc))
       (instructions_from_mats mats (gate_arity ?instr) (gate_params ?instr))"
    using params_nonempty params_distinct params_length params_valid
    by (simp add: valid_instructions_from_mats)

  show ?thesis
    using assms new_instrs_valid
    apply (simp add:
        replace_gate_by_mats_at_def
        valid_replace_instruction_at
        instructions_from_mats_def
        make_instruction_def
        valid_instruction_def)
    by (metis valid_replace_instruction_at)
qed


definition replace_gate_by_seq_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "replace_gate_by_seq_choice qc pos seqs choice =
     replace_gate_by_mats_at qc pos (seqs ! choice)"


lemma num_qubits_replace_gate_by_seq_choice:
  "num_qubits (replace_gate_by_seq_choice qc pos seqs choice) =
     num_qubits qc"
  by (simp add:
      replace_gate_by_seq_choice_def
      num_qubits_replace_gate_by_mats_at)


lemma instructions_replace_gate_by_seq_choice:
  assumes "pos < length (instructions qc)"
  assumes "choice < length seqs"
  shows "instructions (replace_gate_by_seq_choice qc pos seqs choice) =
     take pos (instructions qc) @
     instructions_from_mats (seqs ! choice)
       (gate_arity ((instructions qc) ! pos))
       (gate_params ((instructions qc) ! pos)) @
     drop (Suc pos) (instructions qc)"
  using assms
  by (simp add:
      replace_gate_by_seq_choice_def
      instructions_replace_gate_by_mats_at)


lemma valid_replace_gate_by_seq_choice:
  assumes "valid_quantum_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length seqs"
  shows "valid_quantum_circuit
           (replace_gate_by_seq_choice qc pos seqs choice)"
  using assms
  by (simp add:
      replace_gate_by_seq_choice_def
      valid_replace_gate_by_mats_at)


definition valid_seq_choice :: "complex mat list list \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_seq_choice seqs choice \<longleftrightarrow> choice < length seqs"


lemma valid_replace_gate_by_seq_choice': (* Rename later  *)
  assumes "valid_quantum_circuit qc"
  assumes "valid_replace_pos qc pos"
  assumes "valid_seq_choice seqs choice"
  shows "valid_quantum_circuit
           (replace_gate_by_seq_choice qc pos seqs choice)"
  using assms
  by (simp add:
      valid_replace_pos_def
      valid_seq_choice_def
      valid_replace_gate_by_seq_choice)


definition generated_sequences_at ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list"
where
  "generated_sequences_at seq_fun qc pos =
     seq_fun (gate_matrix ((instructions qc) ! pos))"


definition replace_gate_by_generated_seq_choice ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "replace_gate_by_generated_seq_choice seq_fun qc pos choice =
     replace_gate_by_seq_choice qc pos
       (generated_sequences_at seq_fun qc pos)
       choice"


lemma num_qubits_replace_gate_by_generated_seq_choice:
  "num_qubits (replace_gate_by_generated_seq_choice seq_fun qc pos choice) =
     num_qubits qc"
  by (simp add:
      replace_gate_by_generated_seq_choice_def
      num_qubits_replace_gate_by_seq_choice)


lemma instructions_replace_gate_by_generated_seq_choice:
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generated_sequences_at seq_fun qc pos)"
  shows "instructions (replace_gate_by_generated_seq_choice seq_fun qc pos choice) =
     take pos (instructions qc) @
     instructions_from_mats ((generated_sequences_at seq_fun qc pos) ! choice)
       (gate_arity ((instructions qc) ! pos))
       (gate_params ((instructions qc) ! pos)) @
     drop (Suc pos) (instructions qc)"
  using assms
  by (simp add:
      replace_gate_by_generated_seq_choice_def
      instructions_replace_gate_by_seq_choice)


definition valid_generated_seq_choice ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_generated_seq_choice seq_fun qc pos choice \<longleftrightarrow>
     valid_replace_pos qc pos \<and>
     valid_seq_choice (generated_sequences_at seq_fun qc pos) choice"


lemma valid_replace_gate_by_generated_seq_choice:
  assumes "valid_quantum_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generated_sequences_at seq_fun qc pos)"
  shows "valid_quantum_circuit
           (replace_gate_by_generated_seq_choice seq_fun qc pos choice)"
  using assms
  by (simp add:
      replace_gate_by_generated_seq_choice_def
      valid_replace_gate_by_seq_choice)


lemma valid_replace_gate_by_generated_seq_choice':
  assumes "valid_quantum_circuit qc"
  assumes "valid_generated_seq_choice seq_fun qc pos choice"
  shows "valid_quantum_circuit
           (replace_gate_by_generated_seq_choice seq_fun qc pos choice)"
  using assms
  by (simp add:
      valid_generated_seq_choice_def
      valid_replace_pos_def
      valid_seq_choice_def
      valid_replace_gate_by_generated_seq_choice)


definition insert_mats_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_mats_at qc pos mats params =
     insert_instructions_at qc pos
       (instructions_from_mats mats (length params) params)"


lemma num_qubits_insert_mats_at:
  "num_qubits (insert_mats_at qc pos mats params) = num_qubits qc"
  by (simp add:
      insert_mats_at_def
      num_qubits_insert_instructions_at)


lemma instructions_insert_mats_at:
  "instructions (insert_mats_at qc pos mats params) =
     take pos (instructions qc) @
     instructions_from_mats mats (length params) params @
     drop pos (instructions qc)"
  by (simp add:
      insert_mats_at_def
      instructions_insert_instructions_at)


lemma valid_insert_mats_at:
  assumes "valid_quantum_circuit qc"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "valid_qubits (num_qubits qc) params"
  shows "valid_quantum_circuit (insert_mats_at qc pos mats params)"
  using assms
  by (simp add:
      insert_mats_at_def
      valid_insert_instructions_at_from_mats)


definition insert_seq_choice_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_seq_choice_at qc pos seqs choice params =
     insert_mats_at qc pos (seqs ! choice) params"


definition valid_params_for_circuit ::
  "quantum_circuit \<Rightarrow> nat list \<Rightarrow> bool"
where
  "valid_params_for_circuit qc params \<longleftrightarrow>
     params \<noteq> [] \<and>
     distinct params \<and>
     valid_qubits (num_qubits qc) params"


definition valid_insert_seq_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "valid_insert_seq_choice qc pos seqs choice params \<longleftrightarrow>
     valid_insert_pos qc pos \<and>
     valid_seq_choice seqs choice \<and>
     valid_params_for_circuit qc params"


lemma valid_insert_seq_choice_at:
  assumes "valid_quantum_circuit qc"
  assumes "valid_insert_seq_choice qc pos seqs choice params"
  shows "valid_quantum_circuit
           (insert_seq_choice_at qc pos seqs choice params)"
  using assms
  by (simp add:
      insert_seq_choice_at_def
      valid_insert_seq_choice_def
      valid_insert_pos_def
      valid_seq_choice_def
      valid_params_for_circuit_def
      valid_insert_mats_at)


lemma valid_insert_seq_choice_at_direct:
  assumes "valid_quantum_circuit qc"
  assumes "pos \<le> length (instructions qc)"
  assumes "choice < length seqs"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "valid_qubits (num_qubits qc) params"
  shows "valid_quantum_circuit
           (insert_seq_choice_at qc pos seqs choice params)"
  using assms
  by (simp add:
      insert_seq_choice_at_def
      valid_insert_mats_at)


datatype obfuscation_step =
    CloakStep nat nat
  | DelayedStep nat nat
  | InversePairStep nat nat "nat list"


(*
CloakStep pos choice
DelayedStep pos choice
InversePairStep pos choice params

For inverse pairs,
  pos    = insert before this position
  choice = which inverse-pair sequence
  params = qubit(s) to act on

*)


text \<open>
  TODO:
  The current validity predicate checks structural placement validity:
    - nonempty parameters
    - distinct parameters
    - parameter count agrees with stored arity
    - parameter indices are within circuit bounds

  It does not yet check that the matrix dimension agrees with the arity,
  e.g. dim_row gate_matrix = 2 ^ gate_arity and dim_col gate_matrix = 2 ^ gate_arity.

  This will be added later as a stronger well-formedness predicate, once the
  structural circuit transformation layer is complete.
\<close>


context gate
begin


definition h :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "h qc q = append_instruction qc (make_instruction H 1 [q])"


definition x :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "x qc q = append_instruction qc (make_instruction X 1 [q])"


definition y :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "y qc q = append_instruction qc (make_instruction Y 1 [q])"


definition z :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "z qc q = append_instruction qc (make_instruction Z 1 [q])"


definition s :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "s qc q = append_instruction qc (make_instruction S 1 [q])"


definition t :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "t qc q = append_instruction qc (make_instruction T 1 [q])"


definition cnot :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  quantum_circuit" where
  "cnot qc control target = append_instruction qc (make_instruction CNOT 2 [control, target])"


lemma valid_h:
  assumes "valid_quantum_circuit qc"
  assumes "q < num_qubits qc"
  shows "valid_quantum_circuit (h qc q)"
  using assms
  by (simp add:
      h_def
      valid_append_instruction
      valid_instruction_def
      valid_qubits_def
      make_instruction_def)


lemma valid_x:
  assumes "valid_quantum_circuit qc"
  assumes "q < num_qubits qc"
  shows "valid_quantum_circuit (x qc q)"
  using assms
  by (simp add:
      x_def
      valid_append_instruction
      valid_instruction_def
      valid_qubits_def
      make_instruction_def)


lemma valid_y:
  assumes "valid_quantum_circuit qc"
  assumes "q < num_qubits qc"
  shows "valid_quantum_circuit (y qc q)"
  using assms
  by (simp add:
      y_def
      valid_append_instruction
      valid_instruction_def
      valid_qubits_def
      make_instruction_def)


lemma valid_z:
  assumes "valid_quantum_circuit qc"
  assumes "q < num_qubits qc"
  shows "valid_quantum_circuit (z qc q)"
  using assms
  by (simp add:
      z_def
      valid_append_instruction
      valid_instruction_def
      valid_qubits_def
      make_instruction_def)


lemma valid_s:
  assumes "valid_quantum_circuit qc"
  assumes "q < num_qubits qc"
  shows "valid_quantum_circuit (s qc q)"
  using assms
  by (simp add:
      s_def
      valid_append_instruction
      valid_instruction_def
      valid_qubits_def
      make_instruction_def)


lemma valid_t:
  assumes "valid_quantum_circuit qc"
  assumes "q < num_qubits qc"
  shows "valid_quantum_circuit (t qc q)"
  using assms
  by (simp add:
      t_def
      valid_append_instruction
      valid_instruction_def
      valid_qubits_def
      make_instruction_def)


lemma valid_cnot:
  assumes "valid_quantum_circuit qc"
  assumes "control < num_qubits qc"
  assumes "target < num_qubits qc"
  assumes "control \<noteq> target"
  shows "valid_quantum_circuit (cnot qc control target)"
  using assms
  by (simp add:
      cnot_def
      valid_append_instruction
      valid_instruction_def
      valid_qubits_def
      make_instruction_def)


definition cloak_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "cloak_at qc pos choice =
     replace_gate_by_generated_seq_choice cloak_seq qc pos choice"


definition valid_cloak_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_cloak_choice qc pos choice \<longleftrightarrow>
     valid_generated_seq_choice cloak_seq qc pos choice"


lemma valid_cloak_at:
  assumes "valid_quantum_circuit qc"
  assumes "valid_cloak_choice qc pos choice"
  shows "valid_quantum_circuit (cloak_at qc pos choice)"
  using assms
  by (simp add:
      cloak_at_def
      valid_cloak_choice_def
      valid_replace_gate_by_generated_seq_choice')


lemma valid_cloak_at_direct:
  assumes "valid_quantum_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generated_sequences_at cloak_seq qc pos)"
  shows "valid_quantum_circuit (cloak_at qc pos choice)"
  using assms
  by (simp add:
      cloak_at_def
      valid_replace_gate_by_generated_seq_choice)


definition delayed_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "delayed_at qc pos choice =
     replace_gate_by_generated_seq_choice delayed_seq qc pos choice"


definition valid_delayed_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_delayed_choice qc pos choice \<longleftrightarrow>
     valid_generated_seq_choice delayed_seq qc pos choice"


lemma valid_delayed_at:
  assumes "valid_quantum_circuit qc"
  assumes "valid_delayed_choice qc pos choice"
  shows "valid_quantum_circuit (delayed_at qc pos choice)"
  using assms
  by (simp add:
      delayed_at_def
      valid_delayed_choice_def
      valid_replace_gate_by_generated_seq_choice')


lemma valid_delayed_at_direct:
  assumes "valid_quantum_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generated_sequences_at delayed_seq qc pos)"
  shows "valid_quantum_circuit (delayed_at qc pos choice)"
  using assms
  by (simp add:
      delayed_at_def
      valid_replace_gate_by_generated_seq_choice)


definition insert_inverse_pair_at ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_inverse_pair_at qc pos choice params =
     insert_seq_choice_at qc pos inverses choice params"


definition valid_inverse_pair_insert_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "valid_inverse_pair_insert_choice qc pos choice params \<longleftrightarrow>
     valid_insert_seq_choice qc pos inverses choice params"


lemma valid_insert_inverse_pair_at:
  assumes "valid_quantum_circuit qc"
  assumes "valid_inverse_pair_insert_choice qc pos choice params"
  shows "valid_quantum_circuit
           (insert_inverse_pair_at qc pos choice params)"
  using assms
  by (simp add:
      insert_inverse_pair_at_def
      valid_inverse_pair_insert_choice_def
      valid_insert_seq_choice_at)


fun apply_obfuscation_step ::
  "quantum_circuit \<Rightarrow> obfuscation_step \<Rightarrow> quantum_circuit"
where
  "apply_obfuscation_step qc (CloakStep pos choice) =
     cloak_at qc pos choice"
| "apply_obfuscation_step qc (DelayedStep pos choice) =
     delayed_at qc pos choice"
| "apply_obfuscation_step qc (InversePairStep pos choice params) =
     insert_inverse_pair_at qc pos choice params"


fun valid_obfuscation_step ::
  "quantum_circuit \<Rightarrow> obfuscation_step \<Rightarrow> bool"
where
  "valid_obfuscation_step qc (CloakStep pos choice) =
     valid_cloak_choice qc pos choice"
| "valid_obfuscation_step qc (DelayedStep pos choice) =
     valid_delayed_choice qc pos choice"
| "valid_obfuscation_step qc (InversePairStep pos choice params) =
     valid_inverse_pair_insert_choice qc pos choice params"


fun apply_obfuscation_plan ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> quantum_circuit"
where
  "apply_obfuscation_plan qc [] = qc"
| "apply_obfuscation_plan qc (step # steps) =
     apply_obfuscation_plan (apply_obfuscation_step qc step) steps"


fun valid_obfuscation_plan ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> bool"
where
  "valid_obfuscation_plan qc [] = True"
| "valid_obfuscation_plan qc (step # steps) =
     (valid_obfuscation_step qc step \<and>
      valid_obfuscation_plan (apply_obfuscation_step qc step) steps)"


lemma valid_apply_obfuscation_step:
  assumes "valid_quantum_circuit qc"
  assumes "valid_obfuscation_step qc step"
  shows "valid_quantum_circuit (apply_obfuscation_step qc step)"
  using assms
  by (cases step)
     (simp_all add:
        valid_cloak_at
        valid_delayed_at
        valid_insert_inverse_pair_at)


lemma valid_apply_obfuscation_plan:
  assumes "valid_quantum_circuit qc"
  assumes "valid_obfuscation_plan qc steps"
  shows "valid_quantum_circuit (apply_obfuscation_plan qc steps)"
  using assms
proof (induction steps arbitrary: qc)
  case Nil
  then show ?case
    by simp
next
  case (Cons step steps)
  have step_valid:
    "valid_obfuscation_step qc step"
    using Cons.prems
    by simp

  have rest_valid:
    "valid_obfuscation_plan (apply_obfuscation_step qc step) steps"
    using Cons.prems
    by simp

  have after_step_valid:
    "valid_quantum_circuit (apply_obfuscation_step qc step)"
    using Cons.prems(1) step_valid
    by (rule valid_apply_obfuscation_step)

  show ?case
    using Cons.IH[OF after_step_valid rest_valid]
    by simp
qed


definition obfuscate_circuit ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> quantum_circuit"
where
  "obfuscate_circuit qc steps = apply_obfuscation_plan qc steps"


lemma valid_obfuscate_circuit:
  assumes "valid_quantum_circuit qc"
  assumes "valid_obfuscation_plan qc steps"
  shows "valid_quantum_circuit (obfuscate_circuit qc steps)"
  using assms
  by (simp add:
      obfuscate_circuit_def
      valid_apply_obfuscation_plan)

text \<open>
  Example 1:
  Qiskit equivalent:

    qc = QuantumCircuit(1)
    qc.h(0)

  Isabelle circuit:
    one qubit, one H gate acting on qubit 0.
\<close>

definition example_h_circuit :: quantum_circuit where
  "example_h_circuit = h (empty_circuit 1) 0"

text \<open>                
  Example 2:
  Qiskit equivalent:

    qc = QuantumCircuit(2)
    qc.h(0)
    qc.cx(0, 1)

  Isabelle circuit:
    H acts on qubit 0.
    CNOT acts on [0, 1], where 0 is control and 1 is target.
\<close>

definition example_bell_circuit :: quantum_circuit where
  "example_bell_circuit = 
      (let qc0 = empty_circuit 2;
          qc1 = h qc0 0;
          qc2 = cnot qc1 0 1
      in qc2)"

text \<open>
  Example 3:
  Qiskit equivalent:

    qc = QuantumCircuit(3)
    qc.h(0)
    qc.cx(0, 1)
    qc.x(2)
    qc.z(1)

  Isabelle circuit:
    A 3-qubit circuit with four placed gate instructions.
\<close>

definition example_three_qubit_circuit :: quantum_circuit where
  "example_three_qubit_circuit = 
      (let qc0 = empty_circuit 3;
          qc1 = h qc0 0;
          qc2 = cnot qc1 0 1;
          qc3 = x qc2 2;
          qc4 = z qc3 1
      in qc4)"

text \<open>
  Important note:
  We do not evaluate gate_matrix directly using value yet.
  Some built-in gates, especially H and T, may involve non-executable constants
  such as sqrt or exp depending on their definitions.

  For now, value commands are used only to inspect the circuit structure:
    num_qubits
    length of instructions
    gate_params
\<close>


lemma valid_example_h_circuit:
  "valid_quantum_circuit example_h_circuit"
  by (simp add:
      example_h_circuit_def
      h_def
      valid_quantum_circuit_def
      valid_instruction_def
      valid_qubits_def
      append_instruction_def
      empty_circuit_def
      make_quantum_circuit_def
      make_instruction_def)


lemma valid_example_bell_circuit:
  "valid_quantum_circuit example_bell_circuit"
  by (simp add:
      example_bell_circuit_def
      h_def
      cnot_def
      valid_quantum_circuit_def
      valid_instruction_def
      valid_qubits_def
      append_instruction_def
      empty_circuit_def
      make_quantum_circuit_def
      make_instruction_def)


lemma valid_example_three_qubit_circuit:
  "valid_quantum_circuit example_three_qubit_circuit"
  by (simp add:
      example_three_qubit_circuit_def
      h_def
      cnot_def
      x_def
      z_def
      valid_quantum_circuit_def
      valid_instruction_def
      valid_qubits_def
      append_instruction_def
      empty_circuit_def
      make_quantum_circuit_def
      make_instruction_def)


lemma valid_replace_example_by_choice:
  "valid_quantum_circuit
     (replace_gate_by_seq_choice
        example_three_qubit_circuit
        2
        [[S, Y, S, Z], [Z, S, Y, S]]
        0)"
proof (rule valid_replace_gate_by_seq_choice)
  show "valid_quantum_circuit example_three_qubit_circuit"
    by (rule valid_example_three_qubit_circuit)

  show "length (instructions example_three_qubit_circuit) > 2"
    by (simp add:
        example_three_qubit_circuit_def
        h_def cnot_def x_def z_def
        append_instruction_def
        empty_circuit_def
        make_quantum_circuit_def
        make_instruction_def)

  show "length [[S, Y, S, Z], [Z, S, Y, S]] > 0"
    by simp
qed


(* 
value "valid_quantum_circuit (x (empty_circuit 3) 2)"
value "valid_quantum_circuit (x (empty_circuit 3) 3)"
value "valid_quantum_circuit (cnot (empty_circuit 3) 0 1)"
value "valid_quantum_circuit (cnot (empty_circuit 3) 0 3)"

value "valid_quantum_circuit example_h_circuit"
value "valid_quantum_circuit example_bell_circuit"
value "valid_quantum_circuit example_three_qubit_circuit"
*)
end

value "num_qubits example_h_circuit"
value "length (instructions example_h_circuit)"
value "gate_params (hd (instructions example_h_circuit))"
value "gate_arity (hd (instructions example_h_circuit))"

value "num_qubits example_bell_circuit"
value "length (instructions example_bell_circuit)"
value "gate_params ((instructions example_bell_circuit) ! 0)"
value "gate_arity ((instructions example_bell_circuit) ! 0)"
value "gate_params ((instructions example_bell_circuit) ! 1)"
value "gate_arity ((instructions example_bell_circuit) ! 1)"

value "num_qubits example_three_qubit_circuit"
value "length (instructions example_three_qubit_circuit)"
value "gate_params ((instructions example_three_qubit_circuit) ! 0)"
value "gate_params ((instructions example_three_qubit_circuit) ! 1)"
value "gate_params ((instructions example_three_qubit_circuit) ! 2)"
value "gate_params ((instructions example_three_qubit_circuit) ! 3)"


value "valid_qubits 3 [0, 1, 2]"
value "valid_qubits 3 [0, 3]"

value "valid_instruction 3 (make_instruction X 1 [2])"
value "valid_instruction 3 (make_instruction X 1 [3])"
value "valid_instruction 3 (make_instruction X 1 [0, 1])"
value "valid_instruction 3 (make_instruction CNOT 2 [0, 1])"
value "valid_instruction 3 (make_instruction CNOT 2 [0])"
value "valid_instruction 3 (make_instruction CNOT 2 [0, 0])"
end