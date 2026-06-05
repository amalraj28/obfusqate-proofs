theory ExecutableQuantumCircuitBridge
  imports ExecutableQuantumCircuit QuantumCircuitSemantics
begin

context executable_u3_basis_gate
begin

definition denote_instruction_id :: "instruction_id \<Rightarrow> instruction" where
  (*
    """
      Converts an executable symbolic instruction into the existing matrix-based
      instruction representation.

      The executable instruction stores a symbolic gate name and qubit
      parameters. This function converts the symbolic gate name into its matrix
      meaning, uses the executable gate arity as the instruction arity, and keeps
      the same qubit parameters.

      args:
        instr:
          The executable symbolic instruction.

      returns:
        The corresponding matrix-based instruction in the proof-layer circuit
        representation.
    """
  *)
  "denote_instruction_id instr =
     create_instruction
       (denote_gate_id (gate_name_id instr))
       (gate_id_arity (gate_name_id instr))
       (gate_params_id instr)"


definition denote_circuit_id :: "quantum_circuit_id \<Rightarrow> quantum_circuit" where
  (*
    """
      Converts an executable symbolic quantum circuit into the existing
      matrix-based quantum circuit representation.

      The executable circuit stores symbolic gate instructions. This function
      converts every executable instruction into a matrix-based instruction and
      keeps the same circuit qubit count.

      args:
        qc:
          The executable symbolic quantum circuit.

      returns:
        The corresponding matrix-based quantum circuit in the proof-layer
        representation.
    """
  *)
  "denote_circuit_id qc =
     create_circuit
       (num_qubits_id qc)
       (map denote_instruction_id (instructions_id qc))"


lemma num_qubits_denote_circuit_id[simp]:
  (*
    """
      Shows that denoting an executable circuit preserves the circuit qubit
      count.

      args:
        qc:
          The executable symbolic quantum circuit.

      conclusion:
        The matrix-based circuit obtained by denotation has the same number of
        qubits as the executable symbolic circuit.
    """
  *)
  "num_qubits (denote_circuit_id qc) = num_qubits_id qc"
  by (simp add:
      denote_circuit_id_def
      create_circuit_def)


lemma instructions_denote_circuit_id[simp]:
  (*
    """
      Shows that the instructions of a denoted executable circuit are obtained
      by denoting every executable instruction.

      args:
        qc:
          The executable symbolic quantum circuit.

      conclusion:
        The matrix-based instruction list of the denoted circuit is the mapped
        denotation of the executable instruction list.
    """
  *)
  "instructions (denote_circuit_id qc) =
     map denote_instruction_id (instructions_id qc)"
  by (simp add:
      denote_circuit_id_def
      create_circuit_def)


lemma gate_params_denote_instruction_id[simp]:
  (*
    """
      Shows that denoting an executable instruction preserves its qubit
      parameters.

      args:
        instr:
          The executable symbolic instruction.

      conclusion:
        The matrix-based instruction obtained by denotation uses the same qubit
        parameters as the executable instruction.
    """
  *)
  "gate_params (denote_instruction_id instr) = gate_params_id instr"
  by (simp add:
      denote_instruction_id_def
      create_instruction_def)


lemma gate_arity_denote_instruction_id[simp]:
  (*
    """
      Shows that the arity of a denoted executable instruction is the executable
      arity of its symbolic gate name.

      args:
        instr:
          The executable symbolic instruction.

      conclusion:
        The matrix-based instruction obtained by denotation has the arity
        associated with the executable symbolic gate.
    """
  *)
  "gate_arity (denote_instruction_id instr) =
     gate_id_arity (gate_name_id instr)"
  by (simp add:
      denote_instruction_id_def
      create_instruction_def)


lemma gate_matrix_denote_instruction_id[simp]:
  (*
    """
      Shows that the matrix of a denoted executable instruction is the matrix
      represented by its symbolic gate name.

      args:
        instr:
          The executable symbolic instruction.

      conclusion:
        The matrix-based instruction obtained by denotation stores the matrix
        denoted by the executable symbolic gate.
    """
  *)
  "gate_matrix (denote_instruction_id instr) =
     denote_gate_id (gate_name_id instr)"
  by (simp add:
      denote_instruction_id_def
      create_instruction_def)


lemma valid_qubits_id_imp_are_valid_qubits:
  (*
    """
      Connects executable qubit-validity checking to the existing matrix-circuit
      qubit-validity predicate.

      Both predicates check that every qubit index is within the circuit range.
      This lemma allows proofs about executable circuit validity to be reused
      when proving validity of the denoted matrix-based circuit.

      args:
        n:
          The number of qubits in the circuit.

        qs:
          The qubit indices being checked.

      assumptions:
        The executable qubit-validity check succeeds.

      conclusion:
        The matrix-circuit qubit-validity predicate also holds.
    """
  *)
  assumes "valid_qubits_id n qs"
  shows "are_valid_qubits n qs"
  using assms
  by (simp add:
      valid_qubits_id_def
      are_valid_qubits_def)


lemma valid_denote_instruction_id:
  (*
    """
      Proves that denoting a valid executable instruction gives a valid
      matrix-based instruction.

      The executable instruction validity check ensures that the parameters are
      nonempty, distinct, within range, and match the symbolic gate arity. Since
      denotation preserves the parameters and uses the same arity, the resulting
      matrix-based instruction satisfies the existing instruction-validity
      predicate.

      args:
        n:
          The number of qubits in the circuit.

        instr:
          The executable symbolic instruction.

      assumptions:
        The executable instruction is structurally valid for the given number of
        qubits.

      conclusion:
        The denoted matrix-based instruction is structurally valid.
    """
  *)
  assumes "valid_instruction_id n instr"
  shows "is_valid_instruction n (denote_instruction_id instr)"
  using assms
  by (simp add:
      valid_instruction_id_def
      is_valid_instruction_def
      valid_qubits_id_def
      are_valid_qubits_def)


lemma valid_denote_circuit_id:
  (*
    """
      Proves that denoting a valid executable quantum circuit gives a valid
      matrix-based quantum circuit.

      The executable circuit validity check ensures that every symbolic
      instruction is valid. Each valid executable instruction denotes a valid
      matrix-based instruction, so the entire denoted circuit satisfies the
      existing matrix-circuit validity predicate.

      args:
        qc:
          The executable symbolic quantum circuit.

      assumptions:
        The executable quantum circuit is structurally valid.

      conclusion:
        The denoted matrix-based quantum circuit is structurally valid.
    """
  *)
  assumes "valid_quantum_circuit_id qc"
  shows "is_valid_circuit (denote_circuit_id qc)"
  using assms
  by (auto simp add:
      valid_quantum_circuit_id_def
      is_valid_circuit_def
      list_all_iff
      valid_denote_instruction_id
      are_valid_qubits_def
      is_valid_instruction_def
      valid_instruction_id_def
      valid_qubits_id_def)

lemma can_replace_at_denote_circuit_id:
  (*
    """
      Shows that executable replacement-position checking agrees with the
      matrix-circuit replacement-position checking after denotation.

      Denotation preserves the instruction list length. Therefore, a position is
      replaceable in the executable symbolic circuit exactly when the same
      position is replaceable in the denoted matrix-based circuit.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being checked.

      conclusion:
        Replacement-position validity is preserved by circuit denotation.
    """
  *)
  "can_replace_at (denote_circuit_id qc) pos =
   can_replace_at_id qc pos"
  by (simp add:
      can_replace_at_def
      can_replace_at_id_def
      denote_circuit_id_def
      create_circuit_def)


lemma can_insert_at_denote_circuit_id:
  (*
    """
      Shows that executable insertion-position checking agrees with the
      matrix-circuit insertion-position checking after denotation.

      Denotation preserves the instruction list length. Therefore, a position is
      insertable in the executable symbolic circuit exactly when the same
      position is insertable in the denoted matrix-based circuit.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being checked.

      conclusion:
        Insertion-position validity is preserved by circuit denotation.
    """
  *)
  "can_insert_at (denote_circuit_id qc) pos =
   can_insert_at_id qc pos"
  by (simp add:
      can_insert_at_def
      can_insert_at_id_def
      denote_circuit_id_def
      create_circuit_def)


lemma denote_insert_instructions_at_id:
  (*
    """
      Shows that executable instruction insertion commutes with denotation.

      Inserting executable symbolic instructions into an executable circuit and
      then denoting the resulting circuit gives the same matrix-based circuit as
      first denoting the original circuit and then inserting the denoted
      instructions.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The insertion position.

        new_instrs:
          The executable symbolic instructions to insert.

      conclusion:
        Denotation commutes with executable instruction insertion.
    """
  *)
  "denote_circuit_id
     (insert_instructions_at_id qc pos new_instrs)
   =
   insert_instructions
     (denote_circuit_id qc)
     pos
     (map denote_instruction_id new_instrs)"
  by (simp add:
      denote_circuit_id_def
      insert_instructions_at_id_def
      insert_instructions_def
      create_circuit_def
      take_map
      drop_map)


lemma denote_replace_instruction_at_id:
  (*
    """
      Shows that executable instruction replacement commutes with denotation.

      Replacing one executable symbolic instruction by a list of executable
      symbolic instructions and then denoting the resulting circuit gives the
      same matrix-based circuit as first denoting the original circuit and then
      replacing the corresponding matrix instruction by the denoted replacement
      instructions.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being replaced.

        new_instrs:
          The executable symbolic replacement instructions.

      conclusion:
        Denotation commutes with executable instruction replacement.
    """
  *)
  "denote_circuit_id
     (replace_instruction_at_id qc pos new_instrs)
   =
   replace_instruction
     (denote_circuit_id qc)
     pos
     (map denote_instruction_id new_instrs)"
  by (simp add:
      denote_circuit_id_def
      replace_instruction_at_id_def
      replace_instruction_def
      create_circuit_def
      take_map
      drop_map)


lemma denote_instructions_from_gate_ids:
  (*
    """
      Shows how generated executable instructions denote matrix-level
      instructions.

      A symbolic gate sequence can be converted into executable instructions by
      attaching the same qubit parameters to every gate. If every symbolic gate
      in the sequence has arity matching the parameter list length, then
      denoting those executable instructions gives the same instruction list as
      converting the denoted matrix gate sequence into proof-layer instructions.

      args:
        gs:
          The symbolic gate sequence.

        params:
          The qubit parameters attached to every generated instruction.

      assumptions:
        Every symbolic gate in the sequence has arity matching the parameter
        list length.

      conclusion:
        Denoting the generated executable instructions agrees with generating
        matrix-level instructions from the denoted gate sequence.
    """
  *)
  assumes fits: "list_all (\<lambda>g. gate_id_arity g = length params) gs"
  shows
    "map denote_instruction_id
       (instructions_from_gate_ids gs params)
     =
     to_instructions
       (denote_gate_seq gs)
       (length params)
       params"
  using fits
  by (induction gs)
     (auto simp add:
        instructions_from_gate_ids_def
        make_instruction_id_def
        denote_instruction_id_def
        denote_gate_seq_def
        to_instructions_def
        create_instruction_def)


lemma denote_replace_with_gate_ids_id:
  (*
    """
      Shows that executable replacement by a symbolic gate sequence agrees with
      matrix-level replacement after denotation.

      The executable circuit replaces one symbolic instruction by a sequence of
      symbolic gate names. When the original circuit is valid, the replacement
      position exists, and the replacement sequence fits the original
      instruction's qubit parameters, denoting the transformed executable circuit
      gives the same result as replacing the corresponding matrix instruction by
      the denoted matrix sequence.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being replaced.

        gs:
          The symbolic gate sequence used as replacement.

      assumptions:
        The executable circuit is structurally valid.

        The selected instruction position exists.

        The symbolic replacement sequence fits the qubit parameters of the
        selected instruction.

      conclusion:
        Denotation commutes with executable replacement by a symbolic gate
        sequence.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  assumes can_replace: "can_replace_at_id qc pos"
  assumes fits:
    "gate_seq_fits_params_id
       gs
       (gate_params_id ((instructions_id qc) ! pos))"
  shows
    "denote_circuit_id
       (replace_with_gate_ids_id qc pos gs)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq gs)"
proof -
  have pos_lt:
    "pos < length (instructions_id qc)"
    using can_replace
    by (simp add: can_replace_at_id_def)

  let ?instr = "(instructions_id qc) ! pos"

  have valid_instr:
    "valid_instruction_id (num_qubits_id qc) ?instr"
    using valid_qc pos_lt
    by (rule valid_instruction_nth_id)

  have arity_eq:
    "length (gate_params_id ?instr) =
     gate_id_arity (gate_name_id ?instr)"
    using valid_instr
    by (simp add: valid_instruction_id_def)

  have fits_list:
    "list_all
       (\<lambda>g. gate_id_arity g = length (gate_params_id ?instr))
       gs"
    using fits
    by (auto simp add:
        gate_seq_fits_params_id_def
        list_all_iff)

  have map_eq:
    "map denote_instruction_id
       (instructions_from_gate_ids gs (gate_params_id ?instr))
     =
     to_instructions
       (denote_gate_seq gs)
       (length (gate_params_id ?instr))
       (gate_params_id ?instr)"
    using fits_list
    by (rule denote_instructions_from_gate_ids)

  show ?thesis
    using can_replace arity_eq map_eq
    by (simp add:
        replace_with_gate_ids_id_def
        replace_with_mats_def
        denote_replace_instruction_at_id
        can_replace_at_id_def
        Let_def)
qed


lemma denote_replace_by_cloak_circuit_id:
  (*
    """
      Shows that circuit-level executable cloak replacement agrees with
      matrix-level replacement after denotation.

      When the executable cloak request is valid, the selected symbolic cloak
      sequence is used to replace the chosen executable instruction. This lemma
      states that denoting the resulting executable circuit gives the same
      matrix circuit as replacing the corresponding matrix instruction by the
      denoted cloak sequence.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being replaced.

        idx:
          The selected cloak alternative.

      assumptions:
        The executable circuit is structurally valid.

        The circuit-level cloak replacement request is valid.

      conclusion:
        Denotation commutes with valid circuit-level executable cloak
        replacement.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  assumes can_cloak: "can_replace_by_cloak_circuit_id qc pos idx"
  shows
    "denote_circuit_id
       (replace_by_cloak_circuit_id qc pos idx)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq
          ((cloak_seq_id
              (gate_name_id ((instructions_id qc) ! pos))) ! idx))"
proof -
  have can_replace:
    "can_replace_at_id qc pos"
    using can_cloak
    by (simp add:
        can_replace_by_cloak_circuit_id_def
        split: if_splits)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "(cloak_seq_id (gate_name_id ?instr)) ! idx"

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using can_cloak
    by (simp add:
        can_replace_by_cloak_circuit_id_def
        can_replace_at_id_def
        Let_def
        split: if_splits)

  have bridge:
    "denote_circuit_id
       (replace_with_gate_ids_id qc pos ?seq)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq ?seq)"
    using valid_qc can_replace fits
    by (rule denote_replace_with_gate_ids_id)

  show ?thesis
    using can_cloak bridge
    by (simp add:
        replace_by_cloak_circuit_id_def
        Let_def)
qed


lemma denote_replace_by_delayed_circuit_id:
  (*
    """
      Shows that circuit-level executable delayed replacement agrees with
      matrix-level replacement after denotation.

      When the executable delayed request is valid, the selected symbolic
      delayed sequence is used to replace the chosen executable instruction.
      This lemma states that denoting the resulting executable circuit gives the
      same matrix circuit as replacing the corresponding matrix instruction by
      the denoted delayed sequence.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being replaced.

        idx:
          The selected delayed alternative.

      assumptions:
        The executable circuit is structurally valid.

        The circuit-level delayed replacement request is valid.

      conclusion:
        Denotation commutes with valid circuit-level executable delayed
        replacement.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  assumes can_delay: "can_replace_by_delayed_circuit_id qc pos idx"
  shows
    "denote_circuit_id
       (replace_by_delayed_circuit_id qc pos idx)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq
          ((delayed_seq_id
              (gate_name_id ((instructions_id qc) ! pos))) ! idx))"
proof -
  have can_replace:
    "can_replace_at_id qc pos"
    using can_delay
    by (simp add:
        can_replace_by_delayed_circuit_id_def
        split: if_splits)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "(delayed_seq_id (gate_name_id ?instr)) ! idx"

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using can_delay
    by (simp add:
        can_replace_by_delayed_circuit_id_def
        can_replace_at_id_def
        Let_def
        split: if_splits)

  have bridge:
    "denote_circuit_id
       (replace_with_gate_ids_id qc pos ?seq)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq ?seq)"
    using valid_qc can_replace fits
    by (rule denote_replace_with_gate_ids_id)

  show ?thesis
    using can_delay bridge
    by (simp add:
        replace_by_delayed_circuit_id_def
        Let_def)
qed


lemma denote_replace_by_basis_circuit_id:
  (*
    """
      Shows that circuit-level executable basis replacement agrees with
      matrix-level replacement after denotation.

      When the executable basis request is valid, the selected symbolic basis
      sequence is used to replace the chosen executable instruction. This lemma
      states that denoting the resulting executable circuit gives the same
      matrix circuit as replacing the corresponding matrix instruction by the
      denoted basis sequence.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being replaced.

        idx:
          The selected basis-transformation alternative.

      assumptions:
        The executable circuit is structurally valid.

        The circuit-level basis replacement request is valid.

      conclusion:
        Denotation commutes with valid circuit-level executable basis
        replacement.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  assumes can_basis: "can_replace_by_basis_circuit_id qc pos idx"
  shows
    "denote_circuit_id
       (replace_by_basis_circuit_id qc pos idx)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq
          ((basis_transform_seq_id
              (gate_name_id ((instructions_id qc) ! pos))) ! idx))"
proof -
  have can_replace:
    "can_replace_at_id qc pos"
    using can_basis
    by (simp add:
        can_replace_by_basis_circuit_id_def
        split: if_splits)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "(basis_transform_seq_id (gate_name_id ?instr)) ! idx"

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using can_basis
    by (simp add:
        can_replace_by_basis_circuit_id_def
        can_replace_at_id_def
        Let_def
        split: if_splits)

  have bridge:
    "denote_circuit_id
       (replace_with_gate_ids_id qc pos ?seq)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq ?seq)"
    using valid_qc can_replace fits
    by (rule denote_replace_with_gate_ids_id)

  show ?thesis
    using can_basis bridge
    by (simp add:
        replace_by_basis_circuit_id_def
        Let_def)
qed


lemma denote_replace_by_u3_basis_circuit_id:
  (*
    """
      Shows that circuit-level symbolic U3 basis replacement agrees with matrix-level replacement after denotation.

      When the executable U3 request is valid, the generated selective symbolic
      U3 sequence replaces the chosen executable instruction. Denoting the
      resulting executable circuit gives the same matrix circuit as replacing
      the corresponding denoted instruction by the denoted U3 sequence.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The instruction position being replaced.

        b:
          The symbolic U3 basis identifier.

      assumptions:
        The executable circuit is structurally valid.

        The circuit-level symbolic U3 basis replacement request is valid.

      conclusion:
        Denotation commutes with valid circuit-level symbolic U3 basis
        replacement.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  assumes can_u3: "can_replace_by_u3_basis_circuit_id qc pos b"
  shows
    "denote_circuit_id
       (replace_by_u3_basis_circuit_id qc pos b)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq
          (u3_selective_basis_seq_id b
            (gate_name_id ((instructions_id qc) ! pos))))"
proof -
  have can_replace:
    "can_replace_at_id qc pos"
    using can_u3
    by (simp add:
        can_replace_by_u3_basis_circuit_id_def
        split: if_splits)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "u3_selective_basis_seq_id b (gate_name_id ?instr)"

  have pos_lt:
    "pos < length (instructions_id qc)"
    using can_replace
    by (simp add: can_replace_at_id_def)

  have valid_instr:
    "valid_instruction_id (num_qubits_id qc) ?instr"
    using valid_qc pos_lt
    by (simp add: valid_instruction_nth_id)

  have arity_params:
    "gate_id_arity (gate_name_id ?instr) = length (gate_params_id ?instr)"
    using valid_instr
    by (simp add: valid_instruction_id_def)

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using arity_params
    by (rule u3_selective_basis_seq_id_fits)

  have bridge:
    "denote_circuit_id
       (replace_with_gate_ids_id qc pos ?seq)
     =
     replace_with_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq ?seq)"
    using valid_qc can_replace fits
    by (rule denote_replace_with_gate_ids_id)

  show ?thesis
    using can_u3 bridge
    by (simp add:
        replace_by_u3_basis_circuit_id_def
        Let_def)
qed


lemma denote_insert_inverse_circuit_id:
  (*
    """
      Shows that circuit-level executable inverse insertion agrees with
      matrix-level insertion after denotation.

      When the executable inverse-insertion request is valid, the selected
      symbolic inverse-pair sequence is converted into executable instructions
      and inserted into the executable circuit. This lemma states that denoting
      the resulting executable circuit gives the same matrix circuit as inserting
      the denoted inverse-pair sequence into the denoted matrix circuit.

      args:
        qc:
          The executable symbolic quantum circuit.

        pos:
          The insertion position.

        idx:
          The selected inverse-pair alternative.

        params:
          The qubit parameters for the inserted inverse-pair sequence.

      assumptions:
        The circuit-level inverse insertion request is valid.

      conclusion:
        Denotation commutes with valid circuit-level executable inverse-pair
        insertion.
    """
  *)
  assumes can_insert:
    "can_insert_inverse_circuit_id qc pos idx params"
  shows
    "denote_circuit_id
       (insert_inverse_circuit_id qc pos idx params)
     =
     insert_mats
       (denote_circuit_id qc)
       pos
       (denote_gate_seq (inverses_id ! idx))
       params"
proof -
  have valid_params:
    "valid_params_for_gate_seq_id
       (num_qubits_id qc)
       (inverses_id ! idx)
       params"
    using can_insert
    by (simp add:
        can_insert_inverse_circuit_id_def
        can_insert_at_id_def
        split: if_splits)

  have fits_list:
    "list_all
       (\<lambda>g. gate_id_arity g = length params)
       (inverses_id ! idx)"
    using valid_params
    by (auto simp add:
        valid_params_for_gate_seq_id_def
        list_all_iff)

  have map_eq:
    "map denote_instruction_id
       (instructions_from_gate_ids (inverses_id ! idx) params)
     =
     to_instructions
       (denote_gate_seq (inverses_id ! idx))
       (length params)
       params"
    using fits_list
    by (rule denote_instructions_from_gate_ids)

  show ?thesis
    using can_insert map_eq
    by (simp add:
        insert_inverse_circuit_id_def
        insert_mats_def
        denote_insert_instructions_at_id)
qed

fun apply_denoted_step_id ::
  "quantum_circuit_id \<Rightarrow> obfuscation_step_id \<Rightarrow> quantum_circuit"
where
  (*
    """
      Applies the matrix-level effect of one executable obfuscation step.

      This function is a proof bridge. It does not define executable behavior.
      It describes what the symbolic executable step becomes after the executable
      circuit is converted into the matrix-based circuit model.

      For valid cloak, delayed, and basis replacement requests, the selected
      symbolic sequence is converted into matrix gates and used as a
      matrix-level replacement. For valid inverse-pair insertion requests, the
      selected symbolic inverse-pair sequence is converted into matrix gates and
      inserted into the matrix circuit.

      If the executable request is invalid, the matrix circuit is left unchanged,
      matching the safe behavior of the executable circuit functions.

      args:
        qc:
          The executable symbolic quantum circuit.

        step:
          The executable obfuscation step.

      returns:
        The matrix-based circuit that corresponds to applying the executable
        step after denotation.
    """
  *)
  "apply_denoted_step_id qc (CloakId pos idx) =
     (if can_replace_by_cloak_circuit_id qc pos idx then
        let instr = instructions_id qc ! pos;
            seq = cloak_seq_id (gate_name_id instr) ! idx
        in replace_with_mats
             (denote_circuit_id qc)
             pos
             (denote_gate_seq seq)
      else denote_circuit_id qc)"
| "apply_denoted_step_id qc (DelayId pos idx) =
     (if can_replace_by_delayed_circuit_id qc pos idx then
        let instr = instructions_id qc ! pos;
            seq = delayed_seq_id (gate_name_id instr) ! idx
        in replace_with_mats
             (denote_circuit_id qc)
             pos
             (denote_gate_seq seq)
      else denote_circuit_id qc)"
| "apply_denoted_step_id qc (BasisId pos idx) =
     (if can_replace_by_basis_circuit_id qc pos idx then
        let instr = instructions_id qc ! pos;
            seq = basis_transform_seq_id (gate_name_id instr) ! idx
        in replace_with_mats
             (denote_circuit_id qc)
             pos
             (denote_gate_seq seq)
      else denote_circuit_id qc)"
| "apply_denoted_step_id qc (U3BasisId pos b) =
     (if can_replace_by_u3_basis_circuit_id qc pos b then
        let instr = instructions_id qc ! pos;
            seq = u3_selective_basis_seq_id b (gate_name_id instr)
        in replace_with_mats
             (denote_circuit_id qc)
             pos
             (denote_gate_seq seq)
      else denote_circuit_id qc)"
| "apply_denoted_step_id qc (InsertInverseId pos idx params) =
     (if can_insert_inverse_circuit_id qc pos idx params then
        insert_mats
          (denote_circuit_id qc)
          pos
          (denote_gate_seq (inverses_id ! idx))
          params
      else denote_circuit_id qc)"


lemma denote_apply_step_id:
  (*
    """
      Shows that applying one executable obfuscation step and then denoting the
      resulting circuit agrees with applying the corresponding matrix-level
      effect of that step.

      The executable step is safe: invalid requests leave the executable circuit
      unchanged. The matrix-level bridge mirrors this behavior by leaving the
      denoted circuit unchanged for invalid requests.

      args:
        qc:
          The executable symbolic quantum circuit.

        step:
          The executable obfuscation step.

      assumptions:
        The executable circuit is structurally valid.

      conclusion:
        Denotation commutes with one safe executable obfuscation step.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows
    "denote_circuit_id (apply_step_id qc step) =
     apply_denoted_step_id qc step"
proof (cases step)
  case (CloakId pos idx)

  show ?thesis
  proof (cases "can_replace_by_cloak_circuit_id qc pos idx")
    case True

    have bridge:
      "denote_circuit_id
         (replace_by_cloak_circuit_id qc pos idx)
       =
       replace_with_mats
         (denote_circuit_id qc)
         pos
         (denote_gate_seq
            ((cloak_seq_id
                (gate_name_id ((instructions_id qc) ! pos))) ! idx))"
      using valid_qc True
      by (rule denote_replace_by_cloak_circuit_id)

    show ?thesis
      using CloakId True bridge
      by (simp add: Let_def)

  next
    case False

    show ?thesis
      using CloakId False
      by (simp add: replace_by_cloak_circuit_id_def)
  qed

next
  case (DelayId pos idx)

  show ?thesis
  proof (cases "can_replace_by_delayed_circuit_id qc pos idx")
    case True

    have bridge:
      "denote_circuit_id
         (replace_by_delayed_circuit_id qc pos idx)
       =
       replace_with_mats
         (denote_circuit_id qc)
         pos
         (denote_gate_seq
            ((delayed_seq_id
                (gate_name_id ((instructions_id qc) ! pos))) ! idx))"
      using valid_qc True
      by (rule denote_replace_by_delayed_circuit_id)

    show ?thesis
      using DelayId True bridge
      by (simp add: Let_def)

  next
    case False

    show ?thesis
      using DelayId False
      by (simp add: replace_by_delayed_circuit_id_def)
  qed

next
  case (BasisId pos idx)

  show ?thesis
  proof (cases "can_replace_by_basis_circuit_id qc pos idx")
    case True

    have bridge:
      "denote_circuit_id
         (replace_by_basis_circuit_id qc pos idx)
       =
       replace_with_mats
         (denote_circuit_id qc)
         pos
         (denote_gate_seq
            ((basis_transform_seq_id
                (gate_name_id ((instructions_id qc) ! pos))) ! idx))"
      using valid_qc True
      by (rule denote_replace_by_basis_circuit_id)

    show ?thesis
      using BasisId True bridge
      by (simp add: Let_def)

  next
    case False

    show ?thesis
      using BasisId False
      by (simp add: replace_by_basis_circuit_id_def)
  qed

next
  case (U3BasisId pos b)

  show ?thesis
  proof (cases "can_replace_by_u3_basis_circuit_id qc pos b")
    case True

    have bridge:
      "denote_circuit_id
         (replace_by_u3_basis_circuit_id qc pos b)
       =
       replace_with_mats
         (denote_circuit_id qc)
         pos
         (denote_gate_seq
            (u3_selective_basis_seq_id b
              (gate_name_id ((instructions_id qc) ! pos))))"
      using valid_qc True
      by (rule denote_replace_by_u3_basis_circuit_id)

    show ?thesis
      using U3BasisId True bridge
      by (simp add: Let_def)

  next
    case False

    show ?thesis
      using U3BasisId False
      by (simp add: replace_by_u3_basis_circuit_id_def)
  qed

next
  case (InsertInverseId pos idx params)

  show ?thesis
  proof (cases "can_insert_inverse_circuit_id qc pos idx params")
    case True

    have bridge:
      "denote_circuit_id
         (insert_inverse_circuit_id qc pos idx params)
       =
       insert_mats
         (denote_circuit_id qc)
         pos
         (denote_gate_seq (inverses_id ! idx))
         params"
      using True
      by (rule denote_insert_inverse_circuit_id)

    show ?thesis
      using InsertInverseId True bridge
      by simp

  next
    case False

    show ?thesis
      using InsertInverseId False
      by (simp add: insert_inverse_circuit_id_def)
  qed
qed


fun apply_denoted_plan_id ::
  "quantum_circuit_id \<Rightarrow> obfuscation_step_id list \<Rightarrow> quantum_circuit"
where
  (*
    """
      Applies the matrix-level effect of an executable obfuscation plan.

      This function is a proof bridge. It follows the executable plan step by
      step, but returns the matrix-based circuit obtained after denoting the
      final executable symbolic circuit.

      The executable circuit is updated after each step, because later steps are
      interpreted relative to the transformed executable circuit.

      args:
        qc:
          The executable symbolic quantum circuit.

        steps:
          The executable obfuscation plan.

      returns:
        The matrix-based circuit corresponding to the executable circuit after
        all steps have been applied.
    """
  *)
  "apply_denoted_plan_id qc [] = denote_circuit_id qc"
| "apply_denoted_plan_id qc (step # steps) =
     apply_denoted_plan_id (apply_step_id qc step) steps"


lemma denote_apply_plan_id:
  (*
    """
      Shows that applying an executable obfuscation plan and then denoting the
      resulting circuit agrees with applying the denoted plan bridge.

      The proof proceeds by induction over the list of executable obfuscation
      steps. After each step, executable circuit validity is preserved, allowing
      the induction hypothesis to be applied to the transformed circuit.

      args:
        qc:
          The executable symbolic quantum circuit.

        steps:
          The executable obfuscation plan.

      assumptions:
        The executable circuit is structurally valid.

      conclusion:
        Denotation commutes with applying the full executable obfuscation plan.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows
    "denote_circuit_id (apply_plan_id qc steps) =
     apply_denoted_plan_id qc steps"
  using valid_qc
proof (induction steps arbitrary: qc)
  case Nil
  then show ?case
    by simp
next
  case (Cons step steps)

  have valid_after_step:
    "valid_quantum_circuit_id (apply_step_id qc step)"
    using Cons.prems
    by (rule valid_apply_step_id)

  have ih:
    "denote_circuit_id
       (apply_plan_id (apply_step_id qc step) steps)
     =
     apply_denoted_plan_id (apply_step_id qc step) steps"
    using Cons.IH[OF valid_after_step]
    by simp

  show ?case
    using ih
    by simp
qed


lemma denote_obfuscate_id:
  (*
    """
      Shows that top-level executable obfuscation commutes with denotation.

      The top-level executable obfuscator applies an executable obfuscation plan
      to a symbolic executable circuit. This lemma states that denoting the
      result is the same as applying the corresponding denoted plan bridge.

      args:
        qc:
          The executable symbolic quantum circuit.

        steps:
          The executable obfuscation plan.

      assumptions:
        The executable circuit is structurally valid.

      conclusion:
        Denotation commutes with top-level executable obfuscation.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows
    "denote_circuit_id (obfuscate_id qc steps) =
     apply_denoted_plan_id qc steps"
  using valid_qc
  by (simp add:
      obfuscate_id_def
      denote_apply_plan_id)


end

locale obfuscation_semantics_u3 =
  (*
    """
      Combines executable symbolic U3 basis denotation with circuit semantics.

      This locale is the bridge setting for semantic preservation of executable
      symbolic U3 basis steps. It keeps the abstract matrix-placement semantics
      from the proof world and adds the executable basis-denotation assumptions
      needed to interpret symbolic U3 basis artifacts.

      assumptions:
        The matrix circuit semantics locale assumptions hold.

        Symbolic executable U3 basis identifiers denote carrier-correct mutual
        inverse matrices.

      conclusion:
        Executable circuits containing symbolic U3 basis artifacts can be
        related to the matrix semantic preservation theorems.
    """
  *)
  obfuscation_semantics + executable_u3_basis_gate
begin


lemma has_circuit_carrier_denote_circuit_id:
  (*
    """
      Proves that a valid executable circuit denotes a matrix circuit whose
      instructions have the required matrix carrier dimensions.

      The executable circuit validity predicate ensures that every executable
      instruction is valid. From each valid executable instruction, we obtain
      that the number of qubit parameters matches the arity of its symbolic
      gate. The symbolic gate carrier theorem then gives the matrix dimensions
      required by the semantic preservation layer.

      args:
        qc:
          The executable symbolic quantum circuit.

      assumptions:
        The executable quantum circuit is structurally valid.

      conclusion:
        The denoted matrix circuit satisfies the circuit carrier condition.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "has_circuit_carrier (denote_circuit_id qc)"
proof -
  have all_valid:
    "\<forall>instr \<in> set (instructions_id qc).
       valid_instruction_id (num_qubits_id qc) instr"
    using valid_qc
    by (simp add:
        valid_quantum_circuit_id_def
        list_all_iff)

  show ?thesis
    unfolding has_circuit_carrier_def
  proof
    fix instr
    assume instr_in:
      "instr \<in> set (instructions (denote_circuit_id qc))"

    then obtain instr_id where instr_id_in:
      "instr_id \<in> set (instructions_id qc)"
      and instr_eq:
      "instr = denote_instruction_id instr_id"
      by (auto simp add:
          denote_circuit_id_def
          create_circuit_def)

    have valid_instr:
      "valid_instruction_id (num_qubits_id qc) instr_id"
      using all_valid instr_id_in
      by blast

    have arity_eq:
      "length (gate_params_id instr_id) =
       gate_id_arity (gate_name_id instr_id)"
      using valid_instr
      by (simp add: valid_instruction_id_def)

    have carrier:
      "denote_gate_id (gate_name_id instr_id)
         \<in> carrier_mat
             (2 ^ gate_id_arity (gate_name_id instr_id))
             (2 ^ gate_id_arity (gate_name_id instr_id))"
      by (rule denote_gate_id_carrier)

    show
      "gate_matrix instr
         \<in> carrier_mat
             (2 ^ length (gate_params instr))
             (2 ^ length (gate_params instr))"
      using instr_eq arity_eq carrier
      by (simp add:
          denote_instruction_id_def
          create_instruction_def)
  qed
qed

lemma denote_gate_seq_carrier:
  (*
    """
      Shows that a symbolic gate sequence denotes a matrix sequence with the
      carrier dimensions determined by a shared parameter list.

      The assumption says that every symbolic gate in the sequence has arity
      matching the length of the parameter list. Since each symbolic gate
      denotes a matrix with dimensions determined by its arity, the whole
      denoted sequence has the carrier dimensions required for placement on the
      parameter list.

      args:
        gs:
          The symbolic gate sequence.

        params:
          The qubit parameter list used by the sequence.

      assumptions:
        Every gate in the symbolic sequence has arity matching the length of the
        parameter list.

      conclusion:
        Every matrix in the denoted sequence has dimensions matching the length
        of the parameter list.
    """
  *)
  assumes fits:
    "list_all (\<lambda>g. gate_id_arity g = length params) gs"
  shows
    "\<forall>G \<in> set (denote_gate_seq gs).
       G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
  using fits
  by (auto simp add:
      denote_gate_seq_def
      list_all_iff
      denote_gate_id_carrier)


lemma dim_row_first_denoted_gate_seq:
  (*
    """
      Shows that the first matrix in a nonempty denoted gate sequence has the
      row dimension determined by the shared parameter list.

      The symbolic sequence must be nonempty, and every symbolic gate in the
      sequence must have arity matching the length of the parameter list.

      args:
        gs:
          The symbolic gate sequence.

        params:
          The qubit parameter list used by the sequence.

      assumptions:
        The symbolic gate sequence is nonempty.

        Every gate in the symbolic sequence has arity matching the length of the
        parameter list.

      conclusion:
        The first denoted matrix has row dimension matching the length of the
        parameter list.
    """
  *)
  assumes nonempty: "gs \<noteq> []"
  assumes fits:
    "list_all (\<lambda>g. gate_id_arity g = length params) gs"
  shows "dim_row ((denote_gate_seq gs) ! 0) = 2 ^ length params"
  using nonempty fits
  by (cases gs)
     (simp_all add:
        denote_gate_seq_def
        list_all_iff)


lemma preserve_apply_denoted_step_id:
  (*
    """
      Proves that the matrix-level effect of one executable obfuscation step
      preserves circuit semantics.

      The executable step may be a cloak replacement, delayed replacement, basis
      replacement, or inverse-pair insertion. If the executable request is
      invalid, the denoted matrix circuit is left unchanged. If the request is
      valid, the proof uses the corresponding matrix-level replacement or
      insertion preservation theorem.

      args:
        qc:
          The executable symbolic quantum circuit.

        step:
          The executable obfuscation step.

      assumptions:
        The executable quantum circuit is structurally valid.

      conclusion:
        Applying the denoted effect of the executable step does not change the
        semantics of the denoted matrix circuit.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows
    "eval_circuit (apply_denoted_step_id qc step) =
     eval_circuit (denote_circuit_id qc)"
proof (cases step)
  case (CloakId pos idx)

  show ?thesis
  proof (cases "can_replace_by_cloak_circuit_id qc pos idx")
    case True

    have can_replace:
      "can_replace_at_id qc pos"
      using True
      by (simp add:
          can_replace_by_cloak_circuit_id_def
          split: if_splits)

    have pos_lt_id:
      "pos < length (instructions_id qc)"
      using can_replace
      by (simp add: can_replace_at_id_def)

    have pos_lt:
      "pos < length (instructions (denote_circuit_id qc))"
      using pos_lt_id
      by simp

    let ?instr_id = "(instructions_id qc) ! pos"
    let ?seq = "(cloak_seq_id (gate_name_id ?instr_id)) ! idx"
    let ?params = "gate_params_id ?instr_id"

    have valid_instr:
      "valid_instruction_id (num_qubits_id qc) ?instr_id"
      using valid_qc pos_lt_id
      by (rule valid_instruction_nth_id)

    have arity_old:
      "length ?params = gate_id_arity (gate_name_id ?instr_id)"
      using valid_instr
      by (simp add: valid_instruction_id_def)

    have idx_lt:
      "idx < length (cloak_seq_id (gate_name_id ?instr_id))"
      using True
      by (simp add:
          can_replace_by_cloak_circuit_id_def
          can_replace_at_id_def
          Let_def
          split: if_splits)

    have fits:
      "gate_seq_fits_params_id ?seq ?params"
      using True
      by (simp add:
          can_replace_by_cloak_circuit_id_def
          can_replace_at_id_def
          Let_def
          split: if_splits)

    have fits_list:
      "list_all (\<lambda>g. gate_id_arity g = length ?params) ?seq"
      using fits
      by (auto simp add:
          gate_seq_fits_params_id_def
          list_all_iff)

    have qc_carrier:
      "\<forall>instr \<in> set (instructions (denote_circuit_id qc)).
         gate_matrix instr \<in> carrier_mat
           (2 ^ length (gate_params instr))
           (2 ^ length (gate_params instr))"
      using has_circuit_carrier_denote_circuit_id[OF valid_qc]
      by (simp add: has_circuit_carrier_def)

    have mats_carrier:
      "\<forall>G \<in> set (denote_gate_seq ?seq).
         G \<in> carrier_mat
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))"
      using denote_gate_seq_carrier[OF fits_list] pos_lt_id
      by simp

    have local_eq:
      "compose (denote_gate_seq ?seq)
         (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos))) =
       gate_matrix ((instructions (denote_circuit_id qc)) ! pos)"
      using cloak_seq_id_correct[OF idx_lt] arity_old pos_lt_id
      by simp

    have preserve:
      "eval_circuit
         (replace_with_mats
           (denote_circuit_id qc)
           pos
           (denote_gate_seq ?seq)) =
       eval_circuit (denote_circuit_id qc)"
      using pos_lt qc_carrier mats_carrier local_eq
      by (rule preserve_replace_mats)

    show ?thesis
      using CloakId True preserve
      by (simp add: Let_def)

  next
    case False

    then show ?thesis
      using CloakId
      by simp
  qed

next
  case (DelayId pos idx)

  show ?thesis
  proof (cases "can_replace_by_delayed_circuit_id qc pos idx")
    case True

    have can_replace:
      "can_replace_at_id qc pos"
      using True
      by (simp add:
          can_replace_by_delayed_circuit_id_def
          split: if_splits)

    have pos_lt_id:
      "pos < length (instructions_id qc)"
      using can_replace
      by (simp add: can_replace_at_id_def)

    have pos_lt:
      "pos < length (instructions (denote_circuit_id qc))"
      using pos_lt_id
      by simp

    let ?instr_id = "(instructions_id qc) ! pos"
    let ?seq = "(delayed_seq_id (gate_name_id ?instr_id)) ! idx"
    let ?params = "gate_params_id ?instr_id"

    have valid_instr:
      "valid_instruction_id (num_qubits_id qc) ?instr_id"
      using valid_qc pos_lt_id
      by (rule valid_instruction_nth_id)

    have arity_old:
      "length ?params = gate_id_arity (gate_name_id ?instr_id)"
      using valid_instr
      by (simp add: valid_instruction_id_def)

    have idx_lt:
      "idx < length (delayed_seq_id (gate_name_id ?instr_id))"
      using True
      by (simp add:
          can_replace_by_delayed_circuit_id_def
          can_replace_at_id_def
          Let_def
          split: if_splits)

    have fits:
      "gate_seq_fits_params_id ?seq ?params"
      using True
      by (simp add:
          can_replace_by_delayed_circuit_id_def
          can_replace_at_id_def
          Let_def
          split: if_splits)

    have fits_list:
      "list_all (\<lambda>g. gate_id_arity g = length ?params) ?seq"
      using fits
      by (auto simp add:
          gate_seq_fits_params_id_def
          list_all_iff)

    have qc_carrier:
      "\<forall>instr \<in> set (instructions (denote_circuit_id qc)).
         gate_matrix instr \<in> carrier_mat
           (2 ^ length (gate_params instr))
           (2 ^ length (gate_params instr))"
      using has_circuit_carrier_denote_circuit_id[OF valid_qc]
      by (simp add: has_circuit_carrier_def)

    have mats_carrier:
      "\<forall>G \<in> set (denote_gate_seq ?seq).
         G \<in> carrier_mat
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))"
      using denote_gate_seq_carrier[OF fits_list] pos_lt_id
      by simp

    have local_eq:
      "compose (denote_gate_seq ?seq)
         (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos))) =
       gate_matrix ((instructions (denote_circuit_id qc)) ! pos)"
      using delayed_seq_id_correct[OF idx_lt] arity_old pos_lt_id
      by simp

    have preserve:
      "eval_circuit
         (replace_with_mats
           (denote_circuit_id qc)
           pos
           (denote_gate_seq ?seq)) =
       eval_circuit (denote_circuit_id qc)"
      using pos_lt qc_carrier mats_carrier local_eq
      by (rule preserve_replace_mats)

    show ?thesis
      using DelayId True preserve
      by (simp add: Let_def)

  next
    case False

    then show ?thesis
      using DelayId
      by simp
  qed

next
  case (BasisId pos idx)

  show ?thesis
  proof (cases "can_replace_by_basis_circuit_id qc pos idx")
    case True

    have can_replace:
      "can_replace_at_id qc pos"
      using True
      by (simp add:
          can_replace_by_basis_circuit_id_def
          split: if_splits)

    have pos_lt_id:
      "pos < length (instructions_id qc)"
      using can_replace
      by (simp add: can_replace_at_id_def)

    have pos_lt:
      "pos < length (instructions (denote_circuit_id qc))"
      using pos_lt_id
      by simp

    let ?instr_id = "(instructions_id qc) ! pos"
    let ?seq = "(basis_transform_seq_id (gate_name_id ?instr_id)) ! idx"
    let ?params = "gate_params_id ?instr_id"

    have valid_instr:
      "valid_instruction_id (num_qubits_id qc) ?instr_id"
      using valid_qc pos_lt_id
      by (rule valid_instruction_nth_id)

    have arity_old:
      "length ?params = gate_id_arity (gate_name_id ?instr_id)"
      using valid_instr
      by (simp add: valid_instruction_id_def)

    have idx_lt:
      "idx < length (basis_transform_seq_id (gate_name_id ?instr_id))"
      using True
      by (simp add:
          can_replace_by_basis_circuit_id_def
          can_replace_at_id_def
          Let_def
          split: if_splits)

    have fits:
      "gate_seq_fits_params_id ?seq ?params"
      using True
      by (simp add:
          can_replace_by_basis_circuit_id_def
          can_replace_at_id_def
          Let_def
          split: if_splits)

    have fits_list:
      "list_all (\<lambda>g. gate_id_arity g = length ?params) ?seq"
      using fits
      by (auto simp add:
          gate_seq_fits_params_id_def
          list_all_iff)

    have qc_carrier:
      "\<forall>instr \<in> set (instructions (denote_circuit_id qc)).
         gate_matrix instr \<in> carrier_mat
           (2 ^ length (gate_params instr))
           (2 ^ length (gate_params instr))"
      using has_circuit_carrier_denote_circuit_id[OF valid_qc]
      by (simp add: has_circuit_carrier_def)

    have mats_carrier:
      "\<forall>G \<in> set (denote_gate_seq ?seq).
         G \<in> carrier_mat
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))"
      using denote_gate_seq_carrier[OF fits_list] pos_lt_id
      by simp

    have local_eq:
      "compose (denote_gate_seq ?seq)
         (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos))) =
       gate_matrix ((instructions (denote_circuit_id qc)) ! pos)"
      using basis_transform_seq_id_correct[OF idx_lt] arity_old pos_lt_id
      by simp

    have preserve:
      "eval_circuit
         (replace_with_mats
           (denote_circuit_id qc)
           pos
           (denote_gate_seq ?seq)) =
       eval_circuit (denote_circuit_id qc)"
      using pos_lt qc_carrier mats_carrier local_eq
      by (rule preserve_replace_mats)

    show ?thesis
      using BasisId True preserve
      by (simp add: Let_def)

  next
    case False

    then show ?thesis
      using BasisId
      by simp
  qed

next
  case (U3BasisId pos b)

  show ?thesis
  proof (cases "can_replace_by_u3_basis_circuit_id qc pos b")
    case True

    have can_replace:
      "can_replace_at_id qc pos"
      using True
      by (simp add:
          can_replace_by_u3_basis_circuit_id_def
          split: if_splits)

    have pos_lt_id:
      "pos < length (instructions_id qc)"
      using can_replace
      by (simp add: can_replace_at_id_def)

    have pos_lt:
      "pos < length (instructions (denote_circuit_id qc))"
      using pos_lt_id
      by simp

    let ?instr_id = "(instructions_id qc) ! pos"
    let ?seq = "u3_selective_basis_seq_id b (gate_name_id ?instr_id)"
    let ?params = "gate_params_id ?instr_id"

    have valid_instr:
      "valid_instruction_id (num_qubits_id qc) ?instr_id"
      using valid_qc pos_lt_id
      by (rule valid_instruction_nth_id)

    have arity_old:
      "length ?params = gate_id_arity (gate_name_id ?instr_id)"
      using valid_instr
      by (simp add: valid_instruction_id_def)

    have arity_one:
      "gate_id_arity (gate_name_id ?instr_id) = 1"
      using True
      by (simp add:
          can_replace_by_u3_basis_circuit_id_def
          can_u3_basis_gate_id_def
          Let_def
          split: if_splits)

    have fits:
      "gate_seq_fits_params_id ?seq ?params"
      using arity_old
      by (simp add: u3_selective_basis_seq_id_fits)

    have fits_list:
      "list_all (\<lambda>g. gate_id_arity g = length ?params) ?seq"
      using fits
      by (auto simp add:
          gate_seq_fits_params_id_def
          list_all_iff)

    have qc_carrier:
      "\<forall>instr \<in> set (instructions (denote_circuit_id qc)).
         gate_matrix instr \<in> carrier_mat
           (2 ^ length (gate_params instr))
           (2 ^ length (gate_params instr))"
      using has_circuit_carrier_denote_circuit_id[OF valid_qc]
      by (simp add: has_circuit_carrier_def)

    have mats_carrier:
      "\<forall>G \<in> set (denote_gate_seq ?seq).
         G \<in> carrier_mat
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))
           (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos)))"
      using denote_gate_seq_carrier[OF fits_list] pos_lt_id
      by simp

    have local_eq:
      "compose (denote_gate_seq ?seq)
         (2 ^ length (gate_params ((instructions (denote_circuit_id qc)) ! pos))) =
       gate_matrix ((instructions (denote_circuit_id qc)) ! pos)"
      using u3_selective_basis_seq_id_correct[OF arity_one] arity_old pos_lt_id
      by simp

    have preserve:
      "eval_circuit
         (replace_with_mats
           (denote_circuit_id qc)
           pos
           (denote_gate_seq ?seq)) =
       eval_circuit (denote_circuit_id qc)"
      using pos_lt qc_carrier mats_carrier local_eq
      by (rule preserve_replace_mats)

    show ?thesis
      using U3BasisId True preserve
      by (simp add: Let_def)

  next
    case False

    then show ?thesis
      using U3BasisId
      by simp
  qed

next
  case (InsertInverseId pos idx params)

  show ?thesis
  proof (cases "can_insert_inverse_circuit_id qc pos idx params")
    case True

    have valid_params:
      "valid_params_for_gate_seq_id
         (num_qubits_id qc)
         (inverses_id ! idx)
         params"
      using True
      by (simp add:
          can_insert_inverse_circuit_id_def
          can_insert_at_id_def
          split: if_splits)

    have idx_lt:
      "idx < length inverses_id"
      using True
      by (simp add:
          can_insert_inverse_circuit_id_def
          can_insert_at_id_def
          split: if_splits)

    have seq_nonempty:
      "inverses_id ! idx \<noteq> []"
      using valid_params
      by (simp add: valid_params_for_gate_seq_id_def)

    have fits_list:
      "list_all (\<lambda>g. gate_id_arity g = length params) (inverses_id ! idx)"
      using valid_params
      by (auto simp add:
          valid_params_for_gate_seq_id_def
          list_all_iff)

    have qc_carrier:
      "\<forall>instr \<in> set (instructions (denote_circuit_id qc)).
         gate_matrix instr \<in> carrier_mat
           (2 ^ length (gate_params instr))
           (2 ^ length (gate_params instr))"
      using has_circuit_carrier_denote_circuit_id[OF valid_qc]
      by (simp add: has_circuit_carrier_def)

    have mats_carrier:
      "\<forall>G \<in> set (denote_gate_seq (inverses_id ! idx)).
         G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
      using denote_gate_seq_carrier[OF fits_list]
      by simp

    have first_dim:
      "dim_row ((denote_gate_seq (inverses_id ! idx)) ! 0) =
       2 ^ length params"
      using seq_nonempty fits_list
      by (rule dim_row_first_denoted_gate_seq)

    have local_id:
      "compose (denote_gate_seq (inverses_id ! idx))
         (2 ^ length params) =
       1\<^sub>m (2 ^ length params)"
      using inverse_seq_id_selected_correct[OF idx_lt] first_dim
      by simp

    have preserve:
      "eval_circuit
         (insert_mats
           (denote_circuit_id qc)
           pos
           (denote_gate_seq (inverses_id ! idx))
           params) =
       eval_circuit (denote_circuit_id qc)"
      using qc_carrier mats_carrier local_id
      by (rule preserve_insert_mats)

    show ?thesis
      using InsertInverseId True preserve
      by simp

  next
    case False

    then show ?thesis
      using InsertInverseId
      by simp
  qed
qed


lemma preserve_apply_denoted_plan_id:
  (*
    """
      Proves that applying the matrix-level effect of an executable obfuscation
      plan preserves circuit semantics.

      The proof proceeds one executable step at a time. Each step preserves
      semantics after denotation, and each executable step also preserves
      executable circuit validity. This allows the induction to continue over
      the remaining steps.

      args:
        qc:
          The executable symbolic quantum circuit.

        steps:
          The executable obfuscation plan.

      assumptions:
        The executable quantum circuit is structurally valid.

      conclusion:
        Applying the denoted effect of the full executable obfuscation plan does
        not change the semantics of the denoted matrix circuit.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows
    "eval_circuit (apply_denoted_plan_id qc steps) =
     eval_circuit (denote_circuit_id qc)"
  using valid_qc
proof (induction steps arbitrary: qc)
  case Nil
  then show ?case
    by simp

next
  case (Cons step steps)

  have valid_after_step:
    "valid_quantum_circuit_id (apply_step_id qc step)"
    using Cons.prems
    by (rule valid_apply_step_id)

  have ih:
    "eval_circuit
       (apply_denoted_plan_id (apply_step_id qc step) steps) =
     eval_circuit
       (denote_circuit_id (apply_step_id qc step))"
    using Cons.IH[OF valid_after_step]
    by simp

  have step_bridge:
    "denote_circuit_id (apply_step_id qc step) =
     apply_denoted_step_id qc step"
    using Cons.prems
    by (rule denote_apply_step_id)

  have step_preserve:
    "eval_circuit (apply_denoted_step_id qc step) =
     eval_circuit (denote_circuit_id qc)"
    using Cons.prems
    by (rule preserve_apply_denoted_step_id)

  show ?case
    using ih step_bridge step_preserve
    by simp
qed


theorem preserve_obfuscate_id:
  (*
    """
      Proves the main semantic correctness theorem for the executable symbolic
      obfuscator.

      The executable obfuscator transforms a symbolic executable circuit using
      a list of executable obfuscation steps. This theorem states that after the
      resulting executable circuit is denoted into the matrix proof layer, its
      circuit semantics is equal to the semantics of the original denoted
      circuit.

      This is the main correctness connection between the exported executable
      obfuscator and the existing matrix-level semantics.

      args:
        qc:
          The executable symbolic quantum circuit.

        steps:
          The executable obfuscation plan.

      assumptions:
        The executable quantum circuit is structurally valid.

      conclusion:
        The denoted obfuscated circuit has the same semantics as the denoted
        original circuit.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows
    "eval_circuit (denote_circuit_id (obfuscate_id qc steps)) =
     eval_circuit (denote_circuit_id qc)"
proof -
  have bridge:
    "denote_circuit_id (obfuscate_id qc steps) =
     apply_denoted_plan_id qc steps"
    using valid_qc
    by (rule denote_obfuscate_id)

  have preserve:
    "eval_circuit (apply_denoted_plan_id qc steps) =
     eval_circuit (denote_circuit_id qc)"
    using valid_qc
    by (rule preserve_apply_denoted_plan_id)

  show ?thesis
    using bridge preserve
    by simp
qed


theorem obfuscate_id_valid_and_semantics:
  (*
    """
      Proves the combined correctness result for the executable symbolic
      obfuscator.

      The theorem states that if the input executable circuit is structurally
      valid, then running the executable obfuscator produces another structurally
      valid executable circuit. It also states that after both circuits are
      converted into the matrix proof layer, the obfuscated circuit has the same
      semantics as the original circuit.

      This is the most user-facing correctness theorem for the current
      executable pipeline.

      args:
        qc:
          The executable symbolic quantum circuit.

        steps:
          The executable obfuscation plan.

      assumptions:
        The input executable quantum circuit is structurally valid.

      conclusion:
        The executable obfuscator preserves structural validity, and its denoted
        output preserves the semantics of the denoted input circuit.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows
    "valid_quantum_circuit_id (obfuscate_id qc steps) \<and>
     eval_circuit (denote_circuit_id (obfuscate_id qc steps)) =
     eval_circuit (denote_circuit_id qc)"
  using valid_qc
  by (simp add:
      valid_obfuscate_id
      preserve_obfuscate_id)


end
end
