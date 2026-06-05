theory ExecutableQuantumCircuit
  imports ExecutableGateNames
begin

(*
  """
    Defines an executable quantum instruction.

    This instruction stores the gate as an executable symbolic gate name instead
    of storing the gate as a complex matrix. The qubit parameters specify which
    qubits the gate acts on.

    fields:
      gate_name_id:
        The executable symbolic gate name.

      gate_params_id:
        The list of qubit indices used by the gate.
  """
*)
record instruction_id =
  gate_name_id :: gate_id
  gate_params_id :: "nat list"


(*
  """
    Defines an executable quantum circuit.

    This circuit stores the number of qubits and a list of executable
    instructions. Unlike the proof-layer circuit, this representation does not
    store complex matrices directly.

    fields:
      num_qubits_id:
        The number of qubits in the circuit.

      instructions_id:
        The executable instructions in the circuit.
  """
*)
record quantum_circuit_id =
  num_qubits_id :: nat
  instructions_id :: "instruction_id list"


definition make_instruction_id :: "gate_id \<Rightarrow> nat list \<Rightarrow> instruction_id" where
  (*
    """
      Creates an executable instruction from a symbolic gate name and qubit
      parameters.

      args:
        g:
          The executable symbolic gate name.

        params:
          The qubits acted on by the gate.

      returns:
        An executable instruction containing the gate name and qubit parameters.
    """
  *)
  "make_instruction_id g params =
     \<lparr> gate_name_id = g, gate_params_id = params \<rparr>"


definition make_quantum_circuit_id ::
  "nat \<Rightarrow> instruction_id list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Creates an executable quantum circuit from a qubit count and instruction
      list.

      args:
        n:
          The number of qubits in the circuit.

        instrs:
          The executable instructions in the circuit.

      returns:
        An executable quantum circuit with the given number of qubits and
        instructions.
    """
  *)
  "make_quantum_circuit_id n instrs =
     \<lparr> num_qubits_id = n, instructions_id = instrs \<rparr>"


definition empty_circuit_id :: "nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Creates an empty executable quantum circuit.

      args:
        n:
          The number of qubits in the circuit.

      returns:
        An executable quantum circuit with no instructions.
    """
  *)
  "empty_circuit_id n = make_quantum_circuit_id n []"


definition valid_qubits_id :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  (*
    """
      Checks whether all qubit indices are within the circuit range.

      args:
        n:
          The number of qubits in the circuit.

        qs:
          The list of qubit indices to check.

      returns:
        True when every qubit index is smaller than the number of qubits, and
        False otherwise.
    """
  *)
  "valid_qubits_id n qs \<longleftrightarrow> list_all (\<lambda>q. q < n) qs"


definition valid_instruction_id :: "nat \<Rightarrow> instruction_id \<Rightarrow> bool" where
  (*
    """
      Checks whether an executable instruction is structurally valid for a
      circuit with the given number of qubits.

      The check ensures that the instruction has at least one qubit parameter,
      that the parameters are distinct, that the number of parameters matches
      the executable arity of the gate, and that all qubit indices are within
      the circuit range.

      args:
        n:
          The number of qubits in the circuit.

        instr:
          The executable instruction to check.

      returns:
        True when the instruction is structurally valid, and False otherwise.
    """
  *)
  "valid_instruction_id n instr \<longleftrightarrow>
     gate_params_id instr \<noteq> [] \<and>
     distinct (gate_params_id instr) \<and>
     length (gate_params_id instr) = gate_id_arity (gate_name_id instr) \<and>
     valid_qubits_id n (gate_params_id instr)"


definition valid_quantum_circuit_id :: "quantum_circuit_id \<Rightarrow> bool" where
  (*
    """
      Checks whether every instruction in an executable quantum circuit is
      structurally valid.

      args:
        qc:
          The executable quantum circuit to check.

      returns:
        True when every instruction is valid for the circuit's qubit count, and
        False otherwise.
    """
  *)
  "valid_quantum_circuit_id qc \<longleftrightarrow>
     list_all (valid_instruction_id (num_qubits_id qc)) (instructions_id qc)"


definition append_instruction_id ::
  "quantum_circuit_id \<Rightarrow> instruction_id \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Appends an executable instruction to the end of an executable quantum
      circuit.

      args:
        qc:
          The executable quantum circuit.

        instr:
          The executable instruction to append.

      returns:
        A circuit with the instruction appended at the end.
    """
  *)
  "append_instruction_id qc instr =
     qc\<lparr> instructions_id := instructions_id qc @ [instr] \<rparr>"


definition append_gate_id ::
  "quantum_circuit_id \<Rightarrow> gate_id \<Rightarrow> nat list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Appends a symbolic gate application to an executable quantum circuit.

      The function creates an executable instruction from the gate name and qubit
      parameters, then appends it to the circuit.

      args:
        qc:
          The executable quantum circuit.

        g:
          The executable symbolic gate name.

        params:
          The qubit parameters used by the gate.

      returns:
        A circuit with the corresponding executable instruction appended.
    """
  *)
  "append_gate_id qc g params =
     append_instruction_id qc (make_instruction_id g params)"


definition x_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable X gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with an X gate appended on the target qubit.
    """
  *)
  "x_id qc q = append_gate_id qc GX [q]"


definition y_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable Y gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with a Y gate appended on the target qubit.
    """
  *)
  "y_id qc q = append_gate_id qc GY [q]"


definition z_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable Z gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with a Z gate appended on the target qubit.
    """
  *)
  "z_id qc q = append_gate_id qc GZ [q]"


definition h_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable H gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with an H gate appended on the target qubit.
    """
  *)
  "h_id qc q = append_gate_id qc GH [q]"


definition s_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable S gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with an S gate appended on the target qubit.
    """
  *)
  "s_id qc q = append_gate_id qc GS [q]"


definition sdg_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable inverse S gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with an inverse S gate appended on the target qubit.
    """
  *)
  "sdg_id qc q = append_gate_id qc GSdg [q]"


definition t_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable T gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with a T gate appended on the target qubit.
    """
  *)
  "t_id qc q = append_gate_id qc GT [q]"


definition tdg_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> quantum_circuit_id" where
  (*
    """
      Appends an executable inverse T gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        q:
          The target qubit.

      returns:
        A circuit with an inverse T gate appended on the target qubit.
    """
  *)
  "tdg_id qc q = append_gate_id qc GTdg [q]"


definition cnot_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Appends an executable CNOT gate to a circuit.

      args:
        qc:
          The executable quantum circuit.

        control:
          The control qubit.

        target:
          The target qubit.

      returns:
        A circuit with a CNOT gate appended on the given control and target
        qubits.
    """
  *)
  "cnot_id qc control target =
     append_gate_id qc GCNOT [control, target]"


definition can_replace_at_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> bool" where
  (*
    """
      Checks whether an instruction position can be replaced in an executable
      quantum circuit.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position.

      returns:
        True when the position identifies an existing instruction, and False
        otherwise.
    """
  *)
  "can_replace_at_id qc pos \<longleftrightarrow> pos < length (instructions_id qc)"


definition can_insert_at_id :: "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> bool" where
  (*
    """
      Checks whether an instruction position can be used for insertion in an
      executable quantum circuit.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The insertion position.

      returns:
        True when the position is a valid insertion point, including the end of
        the instruction list, and False otherwise.
    """
  *)
  "can_insert_at_id qc pos \<longleftrightarrow> pos \<le> length (instructions_id qc)"


definition insert_instructions_at_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> instruction_id list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Inserts executable instructions at a given position in an executable
      quantum circuit.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The insertion position.

        new_instrs:
          The executable instructions to insert.

      returns:
        A circuit with the new instructions inserted at the requested position.
    """
  *)
  "insert_instructions_at_id qc pos new_instrs =
     qc\<lparr> instructions_id :=
          take pos (instructions_id qc) @
          new_instrs @
          drop pos (instructions_id qc) \<rparr>"


definition replace_instruction_at_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> instruction_id list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Replaces one executable instruction with a list of executable instructions.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        new_instrs:
          The replacement executable instructions.

      returns:
        A circuit where the instruction at the requested position has been
        replaced by the given instruction list.
    """
  *)
  "replace_instruction_at_id qc pos new_instrs =
     qc\<lparr> instructions_id :=
          take pos (instructions_id qc) @
          new_instrs @
          drop (Suc pos) (instructions_id qc) \<rparr>"


definition instructions_from_gate_ids ::
  "gate_id list \<Rightarrow> nat list \<Rightarrow> instruction_id list"
where
  (*
    """
      Converts a symbolic gate sequence into executable instructions using the
      same qubit parameters for every gate.

      args:
        gs:
          The symbolic gate sequence.

        params:
          The qubit parameters to attach to every generated instruction.

      returns:
        A list of executable instructions using the given gate names and qubit
        parameters.
    """
  *)
  "instructions_from_gate_ids gs params =
     map (\<lambda>g. make_instruction_id g params) gs"


definition gate_seq_fits_params_id :: "gate_id list \<Rightarrow> nat list \<Rightarrow> bool" where
  (*
    """
      Checks whether every gate in a symbolic gate sequence can use the given
      qubit parameters.

      The check ensures that the sequence is nonempty and that every gate in the
      sequence has arity matching the number of provided qubit parameters.

      args:
        gs:
          The symbolic gate sequence.

        params:
          The qubit parameters to check.

      returns:
        True when the sequence is nonempty and every gate has arity matching the
        number of qubit parameters, and False otherwise.
    """
  *)
  "gate_seq_fits_params_id gs params \<longleftrightarrow>
     gs \<noteq> [] \<and>
     list_all (\<lambda>g. gate_id_arity g = length params) gs"


definition valid_params_for_gate_seq_id ::
  "nat \<Rightarrow> gate_id list \<Rightarrow> nat list \<Rightarrow> bool"
where
  (*
    """
      Checks whether a symbolic gate sequence can be placed on a given list of
      qubit parameters inside a circuit with the given number of qubits.

      The check ensures that the sequence is nonempty, that the qubit parameters
      are nonempty and distinct, that every qubit index is within range, and
      that every gate in the sequence has arity matching the number of qubit
      parameters.

      args:
        n:
          The number of qubits in the circuit.

        gs:
          The symbolic gate sequence.

        params:
          The qubit parameters to check.

      returns:
        True when the gate sequence can be safely converted into executable
        instructions using the given qubit parameters, and False otherwise.
    """
  *)
  "valid_params_for_gate_seq_id n gs params \<longleftrightarrow>
     gs \<noteq> [] \<and>
     params \<noteq> [] \<and>
     distinct params \<and>
     valid_qubits_id n params \<and>
     list_all (\<lambda>g. length params = gate_id_arity g) gs"


definition replace_with_gate_ids_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> gate_id list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Replaces an executable instruction by a symbolic gate sequence.

      The replacement sequence is converted into executable instructions using
      the same qubit parameters as the instruction being replaced. If the
      requested position is invalid, the original circuit is returned unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        gs:
          The symbolic gate sequence used as replacement.

      returns:
        The transformed circuit when the position is valid, and the original
        circuit otherwise.
    """
  *)
  "replace_with_gate_ids_id qc pos gs =
     (if can_replace_at_id qc pos then
        let instr = instructions_id qc ! pos in
        replace_instruction_at_id qc pos
          (instructions_from_gate_ids gs (gate_params_id instr))
      else qc)"


definition can_replace_by_cloak_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  (*
    """
      Checks whether a circuit-level executable cloak replacement is safe.

      The check ensures that the selected instruction exists, that the selected
      cloak alternative exists for the gate at that instruction, and that the
      selected symbolic sequence can use the original instruction's qubit
      parameters.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected cloak alternative.

      returns:
        True when the circuit-level cloak replacement can be applied safely, and
        False otherwise.
    """
  *)
  "can_replace_by_cloak_circuit_id qc pos idx =
     (if can_replace_at_id qc pos then
        let instr = instructions_id qc ! pos in
        let seqs = cloak_seq_id (gate_name_id instr) in
        if idx < length seqs then
          gate_seq_fits_params_id (seqs ! idx) (gate_params_id instr)
        else False
      else False)"


definition replace_by_cloak_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Applies circuit-level executable cloak replacement when the request is
      valid, and otherwise returns the original circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected cloak alternative.

      returns:
        The cloak-transformed circuit when the request is valid, and the
        original circuit otherwise.
    """
  *)
  "replace_by_cloak_circuit_id qc pos idx =
     (if can_replace_by_cloak_circuit_id qc pos idx then
        let instr = instructions_id qc ! pos in
        let seq = cloak_seq_id (gate_name_id instr) ! idx in
        replace_with_gate_ids_id qc pos seq
      else qc)"


definition can_replace_by_delayed_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  (*
    """
      Checks whether a circuit-level executable delayed replacement is safe.

      The check ensures that the selected instruction exists, that the selected
      delayed alternative exists for the gate at that instruction, and that the
      selected symbolic sequence can use the original instruction's qubit
      parameters.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected delayed alternative.

      returns:
        True when the circuit-level delayed replacement can be applied safely,
        and False otherwise.
    """
  *)
  "can_replace_by_delayed_circuit_id qc pos idx =
     (if can_replace_at_id qc pos then
        let instr = instructions_id qc ! pos in
        let seqs = delayed_seq_id (gate_name_id instr) in
        if idx < length seqs then
          gate_seq_fits_params_id (seqs ! idx) (gate_params_id instr)
        else False
      else False)"


definition replace_by_delayed_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Applies circuit-level executable delayed replacement when the request is
      valid, and otherwise returns the original circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected delayed alternative.

      returns:
        The delayed-transformed circuit when the request is valid, and the
        original circuit otherwise.
    """
  *)
  "replace_by_delayed_circuit_id qc pos idx =
     (if can_replace_by_delayed_circuit_id qc pos idx then
        let instr = instructions_id qc ! pos in
        let seq = delayed_seq_id (gate_name_id instr) ! idx in
        replace_with_gate_ids_id qc pos seq
      else qc)"


definition can_replace_by_basis_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  (*
    """
      Checks whether a circuit-level executable basis replacement is safe.

      The check ensures that the selected instruction exists, that the selected
      symbolic basis-transformation alternative exists for the gate at that
      instruction, and that the selected symbolic sequence can use the original
      instruction's qubit parameters.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected basis-transformation alternative.

      returns:
        True when the circuit-level basis replacement can be applied safely, and
        False otherwise.
    """
  *)
  "can_replace_by_basis_circuit_id qc pos idx =
     (if can_replace_at_id qc pos then
        let instr = instructions_id qc ! pos in
        let seqs = basis_transform_seq_id (gate_name_id instr) in
        if idx < length seqs then
          gate_seq_fits_params_id (seqs ! idx) (gate_params_id instr)
        else False
      else False)"


definition replace_by_basis_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Applies circuit-level executable basis replacement when the request is
      valid, and otherwise returns the original circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected basis-transformation alternative.

      returns:
        The basis-transformed circuit when the request is valid, and the
        original circuit otherwise.
    """
  *)
  "replace_by_basis_circuit_id qc pos idx =
     (if can_replace_by_basis_circuit_id qc pos idx then
        let instr = instructions_id qc ! pos in
        let seq = basis_transform_seq_id (gate_name_id instr) ! idx in
        replace_with_gate_ids_id qc pos seq
      else qc)"

fun is_basis_artifact_id ::
  (*
    """
      Checks whether a symbolic gate is an artifact produced by basis transformation.

      U3 basis transformation should not recursively transform generated basis
      markers or generated opaque conjugation markers. This predicate identifies
      those generated symbolic gates.

      args:
        g:
          The symbolic gate being checked.

      returns:
        True for symbolic basis artifacts and False for ordinary gates.
    """
  *)
  "gate_id \<Rightarrow> bool"
where
  "is_basis_artifact_id (GBasis b k) = True"
| "is_basis_artifact_id (GInvBasis b k) = True"
| "is_basis_artifact_id (GConj b g) = True"
| "is_basis_artifact_id g = False"


definition can_u3_basis_gate_id ::
  (*
    """
      Checks whether a symbolic gate may be transformed by the U3 basis family.

      The first executable U3 implementation is intentionally single-qubit only
      and avoids transforming basis artifacts that were already generated by a
      previous U3 basis step.

      args:
        g:
          The symbolic gate being checked.

      returns:
        True when the gate is a non-artifact single-qubit gate, and False
        otherwise.
    """
  *)
  "gate_id \<Rightarrow> bool"
where
  "can_u3_basis_gate_id g \<longleftrightarrow>
     gate_id_arity g = 1 \<and> \<not> is_basis_artifact_id g"


definition can_replace_by_u3_basis_circuit_id ::
  (*
    """
      Checks whether circuit-level symbolic U3 basis replacement is safe.

      The selected instruction must exist and its gate must be eligible for the
      first U3 implementation: a non-artifact single-qubit gate. The basis
      identifier is carried symbolically and does not affect structural safety.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        b:
          The symbolic U3 basis identifier.

      returns:
        True when the U3 basis replacement can be applied safely, and False
        otherwise.
    """
  *)
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> basis_id \<Rightarrow> bool"
where
  "can_replace_by_u3_basis_circuit_id qc pos b =
     (if can_replace_at_id qc pos then
        let instr = instructions_id qc ! pos in
        can_u3_basis_gate_id (gate_name_id instr)
      else False)"


definition replace_by_u3_basis_circuit_id ::
  (*
    """
      Applies circuit-level symbolic U3 basis replacement when it is safe.

      A valid request replaces the selected single-qubit gate by the selective
      symbolic U3 sequence. An invalid request leaves the circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        b:
          The symbolic U3 basis identifier.

      returns:
        The U3-basis-transformed circuit when safe, and the original circuit
        otherwise.
    """
  *)
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> basis_id \<Rightarrow> quantum_circuit_id"
where
  "replace_by_u3_basis_circuit_id qc pos b =
     (if can_replace_by_u3_basis_circuit_id qc pos b then
        let instr = instructions_id qc ! pos in
        let seq = u3_selective_basis_seq_id b (gate_name_id instr) in
        replace_with_gate_ids_id qc pos seq
      else qc)"


definition can_insert_inverse_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  (*
    """
      Checks whether a circuit-level executable inverse-pair insertion is safe.

      The check ensures that the insertion position is valid, that the selected
      inverse-pair alternative exists, and that the provided qubit parameters are
      valid for the selected inverse-pair sequence.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The insertion position.

        idx:
          The selected inverse-pair alternative.

        params:
          The qubit parameters for the inserted inverse-pair sequence.

      returns:
        True when the inverse-pair insertion can be applied safely, and False
        otherwise.
    """
  *)
  "can_insert_inverse_circuit_id qc pos idx params =
     (if can_insert_at_id qc pos then
        if idx < length inverses_id then
          valid_params_for_gate_seq_id
            (num_qubits_id qc)
            (inverses_id ! idx)
            params
        else False
      else False)"


definition insert_inverse_circuit_id ::
  "quantum_circuit_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Applies circuit-level executable inverse-pair insertion when the request is
      valid, and otherwise returns the original circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The insertion position.

        idx:
          The selected inverse-pair alternative.

        params:
          The qubit parameters for the inserted inverse-pair sequence.

      returns:
        The circuit with the inverse-pair sequence inserted when the request is
        valid, and the original circuit otherwise.
    """
  *)
  "insert_inverse_circuit_id qc pos idx params =
     (if can_insert_inverse_circuit_id qc pos idx params then
        insert_instructions_at_id qc pos
          (instructions_from_gate_ids (inverses_id ! idx) params)
      else qc)"


datatype obfuscation_step_id =
  (*
    """
      Defines the executable obfuscation step syntax.

      The datatype is symbolic and code-generation friendly. Each constructor
      records the indices and parameters needed by one safe executable
      transformation family.

      args:
        constructors:
          CloakId selects a cloak replacement, DelayId selects a delayed
          replacement, BasisId selects a finite basis replacement, U3BasisId
          selects symbolic selective U3 basis replacement, and InsertInverseId
          selects an inverse-pair insertion.

      returns:
        A symbolic executable obfuscation step.
    """
  *)
    CloakId nat nat
  | DelayId nat nat
  | BasisId nat nat
  | U3BasisId nat basis_id
  | InsertInverseId nat nat "nat list"


fun apply_step_id ::
  "quantum_circuit_id \<Rightarrow> obfuscation_step_id \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Applies one executable obfuscation step to an executable quantum circuit.

      The supported steps are cloak replacement, delayed replacement, finite
      basis replacement, symbolic U3 basis replacement, and inverse-pair
      insertion. Each step uses the safe
      circuit-level executable transformation and returns the original circuit
      unchanged when the request is invalid.

      args:
        qc:
          The executable quantum circuit.

        step:
          The executable obfuscation step.

      returns:
        The circuit obtained after applying the selected obfuscation step.
    """
  *)
  "apply_step_id qc (CloakId pos idx) =
     replace_by_cloak_circuit_id qc pos idx"
| "apply_step_id qc (DelayId pos idx) =
     replace_by_delayed_circuit_id qc pos idx"
| "apply_step_id qc (BasisId pos idx) =
     replace_by_basis_circuit_id qc pos idx"
| "apply_step_id qc (U3BasisId pos b) =
     replace_by_u3_basis_circuit_id qc pos b"
| "apply_step_id qc (InsertInverseId pos idx params) =
     insert_inverse_circuit_id qc pos idx params"


fun apply_plan_id ::
  "quantum_circuit_id \<Rightarrow> obfuscation_step_id list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Applies a list of executable obfuscation steps to an executable quantum
      circuit.

      The steps are applied from left to right. Each step operates on the circuit
      produced by the previous step.

      args:
        qc:
          The executable quantum circuit.

        steps:
          The list of executable obfuscation steps.

      returns:
        The circuit obtained after applying all executable obfuscation steps.
    """
  *)
  "apply_plan_id qc [] = qc"
| "apply_plan_id qc (step # steps) =
     apply_plan_id (apply_step_id qc step) steps"


definition obfuscate_id ::
  "quantum_circuit_id \<Rightarrow> obfuscation_step_id list \<Rightarrow> quantum_circuit_id"
where
  (*
    """
      Applies an executable obfuscation plan to an executable quantum circuit.

      This is the top-level executable obfuscation function for symbolic quantum
      circuits.

      args:
        qc:
          The executable quantum circuit.

        steps:
          The executable obfuscation steps.

      returns:
        The obfuscated executable quantum circuit.
    """
  *)
  "obfuscate_id qc steps = apply_plan_id qc steps"


lemma valid_empty_circuit_id:
  (*
    """
      Proves that an empty executable quantum circuit is structurally valid.

      The circuit has no instructions, so every instruction in the circuit is
      valid trivially.

      args:
        n:
          The number of qubits in the empty executable circuit.

      conclusion:
        The empty executable circuit is structurally valid.
    """
  *)
  "valid_quantum_circuit_id (empty_circuit_id n)"
  by (simp add:
      valid_quantum_circuit_id_def
      empty_circuit_id_def
      make_quantum_circuit_id_def)


lemma valid_make_instruction_id:
  (*
    """
      Proves that creating an executable instruction from a gate and qubit
      parameters gives a valid instruction when the parameters satisfy the
      required structural conditions.

      The assumptions require the parameter list to be nonempty, distinct, in
      range, and of the correct length for the executable gate arity.

      args:
        n:
          The number of qubits in the circuit.

        g:
          The executable symbolic gate.

        params:
          The qubit parameters assigned to the gate.

      assumptions:
        The parameter list is nonempty.

        The parameter list has no duplicate qubits.

        The parameter list length matches the executable gate arity.

        All qubit parameters are within the circuit range.

      conclusion:
        The instruction created from the gate and parameters is valid.
    """
  *)
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "length params = gate_id_arity g"
  assumes "valid_qubits_id n params"
  shows "valid_instruction_id n (make_instruction_id g params)"
  using assms
  by (simp add:
      valid_instruction_id_def
      make_instruction_id_def)


lemma valid_append_instruction_id:
  (*
    """
      Proves that appending a valid executable instruction preserves executable
      circuit validity.

      If the original circuit is valid and the instruction being appended is
      valid for the same number of qubits, then the resulting circuit is valid.

      args:
        qc:
          The executable quantum circuit.

        instr:
          The executable instruction to append.

      assumptions:
        The original executable circuit is valid.

        The instruction being appended is valid for the circuit's qubit count.

      conclusion:
        The circuit after appending the instruction is valid.
    """
  *)
  assumes "valid_quantum_circuit_id qc"
  assumes "valid_instruction_id (num_qubits_id qc) instr"
  shows "valid_quantum_circuit_id (append_instruction_id qc instr)"
  using assms
  by (simp add:
      valid_quantum_circuit_id_def
      append_instruction_id_def)


lemma valid_insert_instructions_at_id:
  (*
    """
      Proves that inserting valid executable instructions preserves executable
      circuit validity.

      If the original circuit is valid and every inserted instruction is valid
      for the same number of qubits, then the circuit after insertion is valid.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The position where the new instructions are inserted.

        new_instrs:
          The executable instructions being inserted.

      assumptions:
        The original executable circuit is valid.

        Every inserted instruction is valid for the circuit's qubit count.

      conclusion:
        The circuit after inserting the instructions is valid.
    """
  *)
  assumes "valid_quantum_circuit_id qc"
  assumes "list_all (valid_instruction_id (num_qubits_id qc)) new_instrs"
  shows "valid_quantum_circuit_id
           (insert_instructions_at_id qc pos new_instrs)"
  using assms
  apply (auto simp add:
      valid_quantum_circuit_id_def
      insert_instructions_at_id_def
      list_all_iff)
   apply (meson in_set_takeD)
  by (metis in_set_dropD)


lemma valid_replace_instruction_at_id:
  (*
    """
      Proves that replacing an executable instruction with valid executable
      instructions preserves executable circuit validity.

      If the original circuit is valid and every replacement instruction is
      valid for the same number of qubits, then the circuit after replacement is
      valid.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position being replaced.

        new_instrs:
          The executable replacement instructions.

      assumptions:
        The original executable circuit is valid.

        Every replacement instruction is valid for the circuit's qubit count.

      conclusion:
        The circuit after replacement is valid.
    """
  *)
  assumes "valid_quantum_circuit_id qc"
  assumes "list_all (valid_instruction_id (num_qubits_id qc)) new_instrs"
  shows "valid_quantum_circuit_id
           (replace_instruction_at_id qc pos new_instrs)"
  using assms
  apply (auto simp add:
      valid_quantum_circuit_id_def
      replace_instruction_at_id_def
      list_all_iff)
  apply (meson in_set_takeD)
  by (meson in_set_dropD)


lemma valid_instructions_from_gate_ids:
  (*
    """
      Proves that converting a valid symbolic gate sequence into executable
      instructions gives valid executable instructions.

      The symbolic gate sequence is converted by assigning the same qubit
      parameters to every gate in the sequence. The validity condition ensures
      that the sequence is nonempty, the parameters are valid, and every gate in
      the sequence has arity matching the parameter list.

      args:
        n:
          The number of qubits in the circuit.

        gs:
          The symbolic gate sequence.

        params:
          The qubit parameters assigned to every generated instruction.

      assumptions:
        The symbolic gate sequence and parameter list satisfy the executable
        placement validity check.

      conclusion:
        Every generated executable instruction is valid for the circuit.
    """
  *)
  assumes "valid_params_for_gate_seq_id n gs params"
  shows "list_all (valid_instruction_id n)
           (instructions_from_gate_ids gs params)"
  using assms
  by (auto simp add:
      valid_params_for_gate_seq_id_def
      instructions_from_gate_ids_def
      make_instruction_id_def
      valid_instruction_id_def
      list_all_iff)


lemma valid_instruction_nth_id:
  (*
    """
      Extracts the validity of an instruction at a valid position in an
      executable quantum circuit.

      If the whole executable circuit is structurally valid and the requested
      position is inside the instruction list, then the instruction at that
      position is valid for the circuit's qubit count.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position being selected.

      assumptions:
        The executable quantum circuit is structurally valid.

        The selected position is inside the instruction list.

      conclusion:
        The selected instruction is structurally valid for the circuit's qubit
        count.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  assumes pos_lt: "pos < length (instructions_id qc)"
  shows "valid_instruction_id
           (num_qubits_id qc)
           ((instructions_id qc) ! pos)"
  using valid_qc pos_lt
  by (auto simp add:
      valid_quantum_circuit_id_def
      list_all_iff)


lemma valid_params_for_gate_seq_from_instruction_id:
  (*
    """
      Builds a valid gate-sequence placement condition from a valid instruction.

      If an executable instruction is valid and a symbolic gate sequence fits
      the instruction's existing qubit parameters, then that symbolic sequence
      can safely be converted into executable instructions using those same
      qubit parameters.

      args:
        n:
          The number of qubits in the circuit.

        instr:
          The executable instruction whose qubit parameters are reused.

        gs:
          The symbolic gate sequence that will replace the instruction.

      assumptions:
        The executable instruction is structurally valid.

        The symbolic gate sequence fits the instruction's qubit parameters.

      conclusion:
        The symbolic gate sequence is valid for placement on the instruction's
        qubit parameters in a circuit with the given number of qubits.
    """
  *)
  assumes valid_instr: "valid_instruction_id n instr"
  assumes fits: "gate_seq_fits_params_id gs (gate_params_id instr)"
  shows "valid_params_for_gate_seq_id n gs (gate_params_id instr)"
  using valid_instr fits
  
  apply (auto simp add:
      valid_instruction_id_def
      gate_seq_fits_params_id_def
      valid_params_for_gate_seq_id_def)
  using list.pred_mono_strong by fastforce


lemma valid_replace_with_gate_ids_id:
  (*
    """
      Proves that replacing an executable instruction by a fitting symbolic gate
      sequence preserves executable circuit validity.

      The replacement sequence is attached to the same qubit parameters as the
      instruction being replaced. The assumptions ensure that the original
      circuit is valid, the replacement position exists, and the selected
      symbolic gate sequence fits the original instruction's parameters.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        gs:
          The symbolic gate sequence used as replacement.

      assumptions:
        The original executable circuit is structurally valid.

        The selected instruction position exists.

        The replacement gate sequence fits the qubit parameters of the selected
        instruction.

      conclusion:
        The circuit after replacement is structurally valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  assumes can_replace: "can_replace_at_id qc pos"
  assumes fits:
    "gate_seq_fits_params_id
       gs
       (gate_params_id ((instructions_id qc) ! pos))"
  shows "valid_quantum_circuit_id
           (replace_with_gate_ids_id qc pos gs)"
proof -
  have pos_lt:
    "pos < length (instructions_id qc)"
    using can_replace
    by (simp add: can_replace_at_id_def)

  have valid_instr:
    "valid_instruction_id
       (num_qubits_id qc)
       ((instructions_id qc) ! pos)"
    using valid_qc pos_lt
    by (rule valid_instruction_nth_id)

  have valid_params:
    "valid_params_for_gate_seq_id
       (num_qubits_id qc)
       gs
       (gate_params_id ((instructions_id qc) ! pos))"
    using valid_instr fits
    by (rule valid_params_for_gate_seq_from_instruction_id)

  have valid_new_instrs:
    "list_all
       (valid_instruction_id (num_qubits_id qc))
       (instructions_from_gate_ids
          gs
          (gate_params_id ((instructions_id qc) ! pos)))"
    using valid_params
    by (rule valid_instructions_from_gate_ids)

  show ?thesis
    using valid_qc can_replace valid_new_instrs
    by (simp add:
        replace_with_gate_ids_id_def
        can_replace_at_id_def
        valid_replace_instruction_at_id)
qed


lemma valid_replace_by_cloak_circuit_id:
  (*
    """
      Proves that circuit-level executable cloak replacement preserves executable
      circuit validity.

      If the original executable circuit is valid, then applying the safe cloak
      replacement operation produces a valid executable circuit. When the cloak
      request is invalid, the operation returns the original circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected cloak alternative.

      assumptions:
        The original executable circuit is structurally valid.

      conclusion:
        The executable circuit after cloak replacement is structurally valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id
           (replace_by_cloak_circuit_id qc pos idx)"
proof (cases "can_replace_by_cloak_circuit_id qc pos idx")
  case True

  then have can_replace:
    "can_replace_at_id qc pos"
    by (simp add: can_replace_by_cloak_circuit_id_def split: if_splits)

  then have pos_lt:
    "pos < length (instructions_id qc)"
    by (simp add: can_replace_at_id_def)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "(cloak_seq_id (gate_name_id ?instr)) ! idx"

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using True
    by (simp add:
        can_replace_by_cloak_circuit_id_def
        can_replace_at_id_def
        Let_def
        split: if_splits)

  have "valid_quantum_circuit_id
          (replace_with_gate_ids_id qc pos ?seq)"
    using valid_qc can_replace fits
    by (rule valid_replace_with_gate_ids_id)

  then show ?thesis
    using True
    by (simp add:
        replace_by_cloak_circuit_id_def
        Let_def)

next
  case False

  then show ?thesis
    using valid_qc
    by (simp add: replace_by_cloak_circuit_id_def)
qed


lemma valid_replace_by_delayed_circuit_id:
  (*
    """
      Proves that circuit-level executable delayed replacement preserves
      executable circuit validity.

      If the original executable circuit is valid, then applying the safe delayed
      replacement operation produces a valid executable circuit. When the delayed
      request is invalid, the operation returns the original circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected delayed alternative.

      assumptions:
        The original executable circuit is structurally valid.

      conclusion:
        The executable circuit after delayed replacement is structurally valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id
           (replace_by_delayed_circuit_id qc pos idx)"
proof (cases "can_replace_by_delayed_circuit_id qc pos idx")
  case True

  then have can_replace:
    "can_replace_at_id qc pos"
    by (simp add: can_replace_by_delayed_circuit_id_def split: if_splits)

  then have pos_lt:
    "pos < length (instructions_id qc)"
    by (simp add: can_replace_at_id_def)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "(delayed_seq_id (gate_name_id ?instr)) ! idx"

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using True
    by (simp add:
        can_replace_by_delayed_circuit_id_def
        can_replace_at_id_def
        Let_def
        split: if_splits)

  have "valid_quantum_circuit_id
          (replace_with_gate_ids_id qc pos ?seq)"
    using valid_qc can_replace fits
    by (rule valid_replace_with_gate_ids_id)

  then show ?thesis
    using True
    by (simp add:
        replace_by_delayed_circuit_id_def
        Let_def)

next
  case False

  then show ?thesis
    using valid_qc
    by (simp add: replace_by_delayed_circuit_id_def)
qed


lemma valid_replace_by_basis_circuit_id:
  (*
    """
      Proves that circuit-level executable basis replacement preserves
      executable circuit validity.

      If the original executable circuit is valid, then applying the safe basis
      replacement operation produces a valid executable circuit. When the basis
      request is invalid, the operation returns the original circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position to replace.

        idx:
          The selected basis-transformation alternative.

      assumptions:
        The original executable circuit is structurally valid.

      conclusion:
        The executable circuit after basis replacement is structurally valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id
           (replace_by_basis_circuit_id qc pos idx)"
proof (cases "can_replace_by_basis_circuit_id qc pos idx")
  case True

  then have can_replace:
    "can_replace_at_id qc pos"
    by (simp add: can_replace_by_basis_circuit_id_def split: if_splits)

  then have pos_lt:
    "pos < length (instructions_id qc)"
    by (simp add: can_replace_at_id_def)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "(basis_transform_seq_id (gate_name_id ?instr)) ! idx"

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using True
    by (simp add:
        can_replace_by_basis_circuit_id_def
        can_replace_at_id_def
        Let_def
        split: if_splits)

  have "valid_quantum_circuit_id
          (replace_with_gate_ids_id qc pos ?seq)"
    using valid_qc can_replace fits
    by (rule valid_replace_with_gate_ids_id)

  then show ?thesis
    using True
    by (simp add:
        replace_by_basis_circuit_id_def
        Let_def)

next
  case False

  then show ?thesis
    using valid_qc
    by (simp add: replace_by_basis_circuit_id_def)
qed


lemma u3_selective_basis_seq_id_fits:
  (*
    """
      Proves that the symbolic U3 selective sequence fits the same parameters as the original gate.

      The inverse basis marker, opaque conjugated gate marker, and basis marker
      all use the original gate arity. Therefore, when the original gate arity
      matches the parameter list length, the generated U3 sequence fits the same
      parameter list.

      args:
        b:
          The symbolic U3 basis identifier.

        g:
          The symbolic gate being transformed.

        params:
          The qubit parameters used by the original instruction.

      assumptions:
        The original gate arity matches the number of qubit parameters.

      conclusion:
        The generated symbolic U3 sequence fits the same qubit parameters.
    """
  *)
  assumes "gate_id_arity g = length params"
  shows "gate_seq_fits_params_id
           (u3_selective_basis_seq_id b g) params"
  using assms
  by (simp add:
      gate_seq_fits_params_id_def
      u3_selective_basis_seq_id_def)


lemma valid_replace_by_u3_basis_circuit_id:
  (*
    """
      Proves that circuit-level symbolic U3 basis replacement preserves validity.

      A valid U3 request replaces one valid single-qubit instruction by three
      symbolic single-qubit instructions on the same parameters. Invalid
      requests leave the circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The instruction position selected for U3 basis replacement.

        b:
          The symbolic U3 basis identifier.

      assumptions:
        The original executable circuit is valid.

      conclusion:
        The circuit after symbolic U3 basis replacement is valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id
           (replace_by_u3_basis_circuit_id qc pos b)"
proof (cases "can_replace_by_u3_basis_circuit_id qc pos b")
  case True

  then have can_replace:
    "can_replace_at_id qc pos"
    by (simp add: can_replace_by_u3_basis_circuit_id_def split: if_splits)

  then have pos_lt:
    "pos < length (instructions_id qc)"
    by (simp add: can_replace_at_id_def)

  let ?instr = "(instructions_id qc) ! pos"
  let ?seq = "u3_selective_basis_seq_id b (gate_name_id ?instr)"

  have valid_instr:
    "valid_instruction_id (num_qubits_id qc) ?instr"
    using valid_qc pos_lt
    by (auto simp add: valid_quantum_circuit_id_def valid_instruction_nth_id valid_qc)

  have arity_params:
    "gate_id_arity (gate_name_id ?instr) = length (gate_params_id ?instr)"
    using valid_instr
    by (simp add: valid_instruction_id_def)

  have fits:
    "gate_seq_fits_params_id ?seq (gate_params_id ?instr)"
    using arity_params
    by (rule u3_selective_basis_seq_id_fits)

  have "valid_quantum_circuit_id
          (replace_with_gate_ids_id qc pos ?seq)"
    using valid_qc can_replace fits
    by (rule valid_replace_with_gate_ids_id)

  then show ?thesis
    using True
    by (simp add:
        replace_by_u3_basis_circuit_id_def
        Let_def)
next
  case False

  then show ?thesis
    using valid_qc
    by (simp add: replace_by_u3_basis_circuit_id_def)
qed


lemma valid_insert_inverse_circuit_id:
  (*
    """
      Proves that circuit-level executable inverse-pair insertion preserves
      executable circuit validity.

      If the original executable circuit is valid, then applying the safe
      inverse-pair insertion operation produces a valid executable circuit. When
      the insertion request is invalid, the operation returns the original
      circuit unchanged.

      args:
        qc:
          The executable quantum circuit.

        pos:
          The insertion position.

        idx:
          The selected inverse-pair alternative.

        params:
          The qubit parameters for the inserted inverse-pair sequence.

      assumptions:
        The original executable circuit is structurally valid.

      conclusion:
        The executable circuit after inverse-pair insertion is structurally
        valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id
           (insert_inverse_circuit_id qc pos idx params)"
proof (cases "can_insert_inverse_circuit_id qc pos idx params")
  case True

  then have valid_params:
    "valid_params_for_gate_seq_id
       (num_qubits_id qc)
       (inverses_id ! idx)
       params"
    by (simp add:
        can_insert_inverse_circuit_id_def
        can_insert_at_id_def
        split: if_splits)

  have valid_new_instrs:
    "list_all
       (valid_instruction_id (num_qubits_id qc))
       (instructions_from_gate_ids (inverses_id ! idx) params)"
    using valid_params
    by (rule valid_instructions_from_gate_ids)

  have "valid_quantum_circuit_id
          (insert_instructions_at_id
             qc
             pos
             (instructions_from_gate_ids (inverses_id ! idx) params))"
    using valid_qc valid_new_instrs
    by (rule valid_insert_instructions_at_id)

  then show ?thesis
    using True
    by (simp add:
        insert_inverse_circuit_id_def)

next
  case False

  then show ?thesis
    using valid_qc
    by (simp add: insert_inverse_circuit_id_def)
qed


lemma valid_apply_step_id:
  (*
    """
      Proves that applying one executable obfuscation step preserves executable
      circuit validity.

      The executable step may be a cloak replacement, delayed replacement,
      finite basis replacement, symbolic U3 basis replacement, or inverse-pair
      insertion. Each operation is already defined as a safe transformation that
      returns the original circuit unchanged when the request is invalid.

      args:
        qc:
          The executable quantum circuit.

        step:
          The executable obfuscation step to apply.

      assumptions:
        The original executable circuit is structurally valid.

      conclusion:
        The executable circuit after applying the step is structurally valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id (apply_step_id qc step)"
  using valid_qc
  by (cases step)
     (simp_all add:
        valid_replace_by_cloak_circuit_id
       valid_replace_by_delayed_circuit_id
       valid_replace_by_basis_circuit_id
       valid_replace_by_u3_basis_circuit_id
       valid_insert_inverse_circuit_id)


lemma valid_apply_plan_id:
  (*
    """
      Proves that applying an executable obfuscation plan preserves executable
      circuit validity.

      The plan is a list of executable obfuscation steps. The proof proceeds by
      applying one step at a time, using the fact that each individual step
      preserves validity.

      args:
        qc:
          The executable quantum circuit.

        steps:
          The executable obfuscation plan.

      assumptions:
        The original executable circuit is structurally valid.

      conclusion:
        The executable circuit after applying the full plan is structurally
        valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id (apply_plan_id qc steps)"
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

  show ?case
    using Cons.IH[OF valid_after_step]
    by simp
qed


lemma valid_obfuscate_id:
  (*
    """
      Proves that top-level executable obfuscation preserves executable circuit
      validity.

      The top-level obfuscation function applies an executable obfuscation plan
      to the input circuit. Since applying a plan preserves validity, the
      obfuscated circuit is also valid.

      args:
        qc:
          The executable quantum circuit.

        steps:
          The executable obfuscation plan.

      assumptions:
        The original executable circuit is structurally valid.

      conclusion:
        The executable circuit produced by top-level obfuscation is structurally
        valid.
    """
  *)
  assumes valid_qc: "valid_quantum_circuit_id qc"
  shows "valid_quantum_circuit_id (obfuscate_id qc steps)"
  using valid_qc
  by (simp add:
      obfuscate_id_def
      valid_apply_plan_id)


definition example_bell_id :: quantum_circuit_id where
  "example_bell_id =
     cnot_id (h_id (empty_circuit_id 2) 0) 0 1"

definition example_plan_id :: "obfuscation_step_id list" where
  "example_plan_id = [CloakId 0 0, InsertInverseId 1 0 [0]]"

definition example_basis_x_id :: quantum_circuit_id where
  (*
    """
      Defines a one-qubit executable example for basis replacement.

      The example circuit contains a single symbolic X gate on qubit 0. Applying
      the basis example plan replaces that X gate by the first symbolic basis
      transformation alternative.

      args:
        none:
          This example is a fixed executable circuit.

      returns:
        A one-qubit executable circuit containing one X gate.
    """
  *)
  "example_basis_x_id =
     x_id (empty_circuit_id 1) 0"

definition example_basis_plan_id :: "obfuscation_step_id list" where
  (*
    """
      Defines a small executable basis-transformation example plan.

      The plan selects the first basis replacement alternative for the first
      instruction of a circuit. For example_basis_x_id, this replaces the X gate
      by the symbolic sequence H, Z, H on the same qubit.

      args:
        none:
          This example plan is fixed.

      returns:
        A one-step executable obfuscation plan containing a basis replacement.
    """
  *)
  "example_basis_plan_id = [BasisId 0 0]"

definition example_u3_basis_x_id ::
  (*
    """
      Defines a one-qubit executable example for symbolic U3 basis replacement.

      The example circuit contains a single symbolic X gate on qubit zero. The
      symbolic U3 basis plan replaces it with three symbolic U3 basis artifacts.

      args:
        none:
          This example circuit is fixed.

      returns:
        A one-qubit executable circuit containing one X instruction.
    """
  *)
  "quantum_circuit_id"
where
  "example_u3_basis_x_id =
     x_id (empty_circuit_id 1) 0"


definition example_u3_basis_plan_id ::
  (*
    """
      Defines a small executable symbolic U3 basis example plan.

      The plan selects the first instruction and uses the symbolic U3 basis
      identifier with handle zero.

      args:
        none:
          This example plan is fixed.

      returns:
        A one-step executable obfuscation plan containing symbolic U3 basis
        replacement.
    """
  *)
  "obfuscation_step_id list"
where
  "example_u3_basis_plan_id = [U3BasisId 0 (BU3 0)]"

value "valid_quantum_circuit_id example_bell_id"
value "obfuscate_id example_bell_id example_plan_id"
value "valid_quantum_circuit_id example_basis_x_id"
value "obfuscate_id example_basis_x_id example_basis_plan_id"
value "valid_quantum_circuit_id example_u3_basis_x_id"
value "obfuscate_id example_u3_basis_x_id example_u3_basis_plan_id"


export_code
  make_instruction_id make_quantum_circuit_id empty_circuit_id
  valid_qubits_id valid_instruction_id valid_quantum_circuit_id
  append_instruction_id append_gate_id
  x_id y_id z_id h_id s_id sdg_id t_id tdg_id cnot_id
  can_replace_at_id can_insert_at_id
  insert_instructions_at_id replace_instruction_at_id
  instructions_from_gate_ids
  gate_seq_fits_params_id valid_params_for_gate_seq_id
  replace_with_gate_ids_id
  basis_transform_seq_id u3_selective_basis_seq_id
  can_replace_by_cloak_circuit_id replace_by_cloak_circuit_id
  can_replace_by_delayed_circuit_id replace_by_delayed_circuit_id
  can_replace_by_basis_circuit_id replace_by_basis_circuit_id
  can_u3_basis_gate_id
  can_replace_by_u3_basis_circuit_id replace_by_u3_basis_circuit_id
  can_insert_inverse_circuit_id insert_inverse_circuit_id
  apply_step_id apply_plan_id obfuscate_id
  in OCaml
  module_name ExecutableQuantumCircuit
  file "executable_quantum_circuit.ml"

end
