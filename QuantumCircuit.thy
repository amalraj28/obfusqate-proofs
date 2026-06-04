theory QuantumCircuit
  imports Sequences
begin

text \<open>
  This theory defines a structural quantum circuit representation for
  circuit-level obfuscation transformations. It proves that valid
  obfuscation plans preserve structural circuit validity. It does not yet
  prove semantic equivalence of the resulting circuit.
\<close>

section \<open>Circuit Representation\<close>


(*
  """
    Defines one structural quantum circuit instruction.
    
    An instruction stores the matrix for the gate, the qubit parameters that the gate
    acts on, and the arity of the gate.
    
    fields:
      gate_matrix:
        The matrix representing the local gate.
    
      gate_params:
        The qubits used by the instruction.
    
      gate_arity:
        The number of qubits acted on by the gate.
  """
*)

record instruction =
  gate_matrix :: "complex mat" (* The gate itself *)
  gate_params :: "nat list" (* Which qubit(s) is/are the gate acting on *)
  gate_arity :: nat (* Number of qubits the gate is acting on *)


(*
  """
    Defines the structural quantum circuit record.
    
    A circuit stores the number of qubits and the ordered list of instructions that
    make up the circuit.
    
    fields:
      num_qubits:
        The number of qubits in the circuit.
    
      instructions:
        The ordered list of circuit instructions.
  """
*)

record quantum_circuit =
  num_qubits   :: nat
  instructions :: "instruction list"


(*
  """
    Creates a structural circuit instruction.
    
    args:
      Gate:
        The matrix representing the gate.
    
      arity:
        The number of qubits acted on by the gate.
    
      params:
        The qubit parameters used by the gate.
    
    returns:
      An instruction containing the supplied matrix, arity, and qubit parameters.
  """
*)

definition create_instruction :: "complex mat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> instruction" where
  "create_instruction Gate arity params =
     \<lparr> gate_matrix = Gate, gate_params = params, gate_arity = arity\<rparr>" (* Bracket of a record *)


(*
  """
    Creates a structural quantum circuit.
    
    args:
      n:
        The number of qubits in the circuit.
    
      instrs:
        The ordered list of instructions in the circuit.
    
    returns:
      A quantum circuit with the given qubit count and instructions.
  """
*)

definition create_circuit :: "nat \<Rightarrow> instruction list \<Rightarrow> quantum_circuit" where
  "create_circuit n instrs =
     \<lparr> num_qubits = n, instructions = instrs \<rparr>"


(*
  """
    Creates an empty structural quantum circuit.
    
    args:
      n:
        The number of qubits in the circuit.
    
    returns:
      A quantum circuit with no instructions.
  """
*)

definition initialize_circuit :: "nat \<Rightarrow> quantum_circuit" where
  "initialize_circuit n = create_circuit n []"


(*
  """
    Appends one instruction to the end of a structural quantum circuit.
    
    args:
      qc:
        The quantum circuit being extended.
    
      instr:
        The instruction to append.
    
    returns:
      A quantum circuit with the instruction added at the end.
  """
*)

definition append_instruction :: "quantum_circuit \<Rightarrow> instruction \<Rightarrow> quantum_circuit" where
  "append_instruction qc instr = qc \<lparr> instructions := instructions qc @ [instr] \<rparr>"


section \<open>Circuit Validity\<close>

definition are_valid_qubits :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  (*
    """
      Checks whether a given list of qubits is valid (all elements are valid qubit indices)

      args:
        n  (nat)      : the total number of qubits in the circuit
        qs (nat list) : the list of qubit indices to validate
      
      returns:
        (bool)        : boolean value indicating the list is valid or not
    """
  *)
  "are_valid_qubits n qs \<longleftrightarrow> list_all (\<lambda>q. q < n) qs"

definition is_valid_instruction :: "nat \<Rightarrow> instruction \<Rightarrow> bool" where
  (*
    """
      Checks whether a given instruction is valid. Checked using 4 conditions:
        1. gate_params parameter of the instruction should not be empty
        2. all elements in gate_params should be distinct
        3. Number of elements in gate_params should be equal to the number of qubits required by instruction
        4. All entries in gate_params are valid qubit indices

      args:
        n (nat)             : the total number of qubits in the circuit
        instr (instruction) : the instruction to validate 

      returns:
        (bool)              : boolean value indicating the instruction is valid or not
    """
  *)
  "is_valid_instruction n instr \<longleftrightarrow>
     gate_params instr \<noteq> [] \<and>
     distinct (gate_params instr) \<and>
     length (gate_params instr) = gate_arity instr \<and>
     are_valid_qubits n (gate_params instr)"


definition is_valid_circuit :: "quantum_circuit \<Rightarrow> bool" where
  (*
    """
      Checks whether a given circuit is valid. Checked by the logic that a circuit is valid iff
      all the instructions present in the circuit are valid

      args:
        qc (quantum_circuit) : the quantum circuit to validate 

      returns:
        (bool) : boolean value indicating the circuit is valid or not
    """
  *)

  "is_valid_circuit qc \<longleftrightarrow>
     list_all (is_valid_instruction (num_qubits qc)) (instructions qc)"


section \<open>Validity Preservation for Basic Constructors\<close>

lemma valid_append:
  (*
    """
      Proves that if we append a valid instruction to a valid circuit, the new circuit is also valid
    """
  *)
  assumes "is_valid_circuit qc"
  assumes "is_valid_instruction (num_qubits qc) instr"
  shows "is_valid_circuit (append_instruction qc instr)"
  using assms
  by (simp add:
      is_valid_circuit_def
      append_instruction_def)


section \<open>Circuit Editing Operations\<close>

definition insert_instructions ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> instruction list \<Rightarrow> quantum_circuit"
where
  "insert_instructions qc pos new_instrs =
     qc\<lparr> instructions := take pos (instructions qc) @ new_instrs @ drop pos (instructions qc) \<rparr>"

  (*
    """
      Insert a new instruction to a quantum circuit.

      args:
        qc (quantum_circuit) : The quantum circuit to which instructions are to be added.
        pos (nat)            : The position to insert the new instructions.
        new_instrs           : The instructions to insert
        (instruction list)

      returns:
        (quantum_circuit)    : A new quantum circuit having the instructions appended to original
                               quantum circuit
    """
  *)


definition replace_instruction ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> instruction list \<Rightarrow> quantum_circuit"
where
  "replace_instruction qc pos new_instrs =
     qc\<lparr> instructions := take pos (instructions qc) @ new_instrs @ drop (Suc pos) (instructions qc) \<rparr>"

  (*
    """
      Replace the instruction at a given position with a new list of instructions.

      args:
        qc (quantum_circuit) : The quantum circuit for which the instructions are to be modified
        pos (nat)            : The position of the instruction to be replaced.
        new_instrs           : The new instructions which will replace the one at pos.
        (instruction list)

      returns:
        (quantum_circuit)    : A new quantum circuit w
    """
  *)

lemma num_qubits_insert:
  (*
    """
      Proves that number of qubits after insertion is same as number of qubits before insertion.
    """
  *)
  "num_qubits (insert_instructions qc pos new_instrs) = num_qubits qc"
  by (simp add: insert_instructions_def)


lemma instructions_insert:
  (*
    """
      insert_instructions definition is restated as a lemma  
    """
  *)
  "instructions (insert_instructions qc pos new_instrs) =
     take pos (instructions qc) @ new_instrs @ drop pos (instructions qc)"
  by (simp add: insert_instructions_def)


lemma num_qubits_replace:
  (*
    """
      Number of qubits after replacing an instruction using the `replace_instruction` definition
      is equal to the number of qubits before the replacement.
    """
  *)
  "num_qubits (replace_instruction qc pos new_instrs) = num_qubits qc"
  by (simp add: replace_instruction_def)


lemma instructions_replace:
  (*
    """
      replace_instruction definition restated as a lemma
    """
  *)

  "instructions (replace_instruction qc pos new_instrs) =
     take pos (instructions qc) @ new_instrs @ drop (Suc pos) (instructions qc)"
  by (simp add: replace_instruction_def)


lemma valid_insert:
  (*
    """
      After inserting a valid instruction to a valid circuit using `insert_instructions` definition,
      the resulting new circuit will also be a valid one.
    """
  *)
  assumes "is_valid_circuit qc"
  assumes "list_all (is_valid_instruction (num_qubits qc)) new_instrs"
  shows "is_valid_circuit (insert_instructions qc pos new_instrs)"
  using assms
  apply (simp add: is_valid_circuit_def insert_instructions_def is_valid_instruction_def list_all_def)
  by (metis UnE in_set_dropD in_set_takeD)


lemma valid_replace:
  (*
    """
      After replacing an instruction in a valid circuit with a valid list of instructions 
      using `replace_instruction` definition, the resulting new circuit will also be a valid one.
    """
  *)
  assumes "is_valid_circuit qc"
  assumes "list_all (is_valid_instruction (num_qubits qc)) new_instrs"
  shows "is_valid_circuit (replace_instruction qc pos new_instrs)"
  using assms
  apply (simp add:
      is_valid_circuit_def
      replace_instruction_def
      list_all_def)
  by (metis Un_iff in_set_dropD in_set_takeD)


definition can_insert_at :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> bool" where
  "can_insert_at qc pos \<longleftrightarrow> pos \<le> length (instructions qc)"
  (*
    """
      Indicates whether it is possible to insert an instruction at the specified position.
      Condition used is that the position should be in the range 0 \<le> pos \<le> len(instruction)
      
      args:
        qc  (quantum_circuit) : The quantum circuit
        pos (nat)             : Position to check

      returns:
        (bool)  :  Boolean value indicating the position is valid or not
    """
  *)


definition can_replace_at :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> bool" where
  (*
    """
      Indicates whether it is possible to replace the instruction at the specified position.
      Condition used is that the position should be in the range 0 \<le> pos < len(instruction)
      
      args:
        qc  (quantum_circuit) : The quantum circuit
        pos (nat)             : Position to check

      returns:
        (bool)  :  Boolean value indicating the position is valid or not
    """
  *)
  "can_replace_at qc pos \<longleftrightarrow> pos < length (instructions qc)"


section \<open>Matrix Sequences as Circuit Instructions\<close>

(*
  """
    Converts a list of gate matrices into circuit instructions.
    
    Each matrix is turned into an instruction using the same arity and qubit
    parameters.
    
    args:
      mats:
        The gate matrices to convert.
    
      arity:
        The arity assigned to every generated instruction.
    
      params:
        The qubit parameters assigned to every generated instruction.
    
    returns:
      A list of circuit instructions generated from the matrix list.
  """
*)

definition to_instructions ::
  "complex mat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> instruction list"
where
  "to_instructions mats arity params =
     map (\<lambda>G. create_instruction G arity params) mats"

(*
  """
    Shows that converting matrices into instructions preserves list length.
    
    args:
      mats:
        The matrix list being converted.
    
      arity:
        The arity assigned to the generated instructions.
    
      params:
        The qubit parameters assigned to the generated instructions.
    
    conclusion:
      The number of generated instructions is the same as the number of input
      matrices.
  """
*)

lemma length_to_instructions:
  "length (to_instructions mats arity params) = length mats"
  by (simp add: to_instructions_def)


(*
  """
    Shows that converting an empty matrix list produces an empty instruction list.
    
    args:
      arity:
        The arity that would be assigned to generated instructions.
    
      params:
        The qubit parameters that would be assigned to generated instructions.
    
    conclusion:
      The generated instruction list is empty.
  """
*)

lemma to_instructions_Nil:
  "to_instructions [] arity params = []"
  by (simp add: to_instructions_def)


(*
  """
    Shows how conversion behaves on a nonempty matrix list.
    
    args:
      G:
        The first matrix in the list.
    
      Gs:
        The remaining matrices.
    
      arity:
        The arity assigned to generated instructions.
    
      params:
        The qubit parameters assigned to generated instructions.
    
    conclusion:
      The converted instruction list starts with the instruction for the first
      matrix, followed by the converted instructions for the remaining matrices.
  """
*)

lemma to_instructions_Cons:
  "to_instructions (G # Gs) arity params =
     create_instruction G arity params # to_instructions Gs arity params"
  by (simp add: to_instructions_def)


(*
  """
    Proves that generated instructions are valid when the shared parameters are
    valid.
    
    args:
      n:
        The number of qubits in the circuit.
    
      mats:
        The matrix list being converted.
    
      arity:
        The arity assigned to every generated instruction.
    
      params:
        The qubit parameters assigned to every generated instruction.
    
    assumptions:
      The parameter list is nonempty.
    
      The parameter list has no duplicate qubits.
    
      The parameter list length matches the arity.
    
      All parameter entries are valid qubit indices.
    
    conclusion:
      Every generated instruction is valid for the circuit.
  """
*)

lemma valid_to_instructions:
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "length params = arity"
  assumes "are_valid_qubits n params"
  shows "list_all (is_valid_instruction n)
           (to_instructions mats arity params)"
  using assms
  by (simp add: 
      to_instructions_def
      is_valid_instruction_def
      create_instruction_def
      are_valid_qubits_def list_all_length)


(*
  """
    Proves validity preservation for replacing an instruction by generated
    matrix-based instructions.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      mats:
        The matrix sequence used for replacement.
    
      arity:
        The arity assigned to generated replacement instructions.
    
      params:
        The qubit parameters assigned to generated replacement instructions.
    
    assumptions:
      The original circuit is valid.
    
      The parameter list is nonempty, distinct, in range, and has the requested
      arity.
    
    conclusion:
      The circuit after replacement is valid.
  """
*)

lemma valid_replace_with_mats_raw:
  assumes "is_valid_circuit qc"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "length params = arity"
  assumes "are_valid_qubits (num_qubits qc) params"
  shows "is_valid_circuit
           (replace_instruction qc pos
             (to_instructions mats arity params))"
  using assms
  by (simp add:
      valid_replace
      valid_to_instructions)


(*
  """
    Proves validity preservation for inserting generated matrix-based instructions.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      mats:
        The matrix sequence being inserted.
    
      arity:
        The arity assigned to inserted instructions.
    
      params:
        The qubit parameters assigned to inserted instructions.
    
    assumptions:
      The original circuit is valid.
    
      The parameter list is nonempty, distinct, in range, and has the requested
      arity.
    
    conclusion:
      The circuit after insertion is valid.
  """
*)

lemma valid_insert_mats_raw:
  assumes "is_valid_circuit qc"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "length params = arity"
  assumes "are_valid_qubits (num_qubits qc) params"
  shows "is_valid_circuit
           (insert_instructions qc pos
             (to_instructions mats arity params))"
  using assms
  by (simp add:
      valid_insert
      valid_to_instructions)


section \<open>Replacing Gates by Matrix Sequences\<close>

(*
  """
    Replaces one circuit instruction with a sequence of matrix gates.
    
    The replacement sequence reuses the arity and qubit parameters of the original
    instruction at the selected position.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to replace.
    
      mats:
        The replacement matrix sequence.
    
    returns:
      A circuit where the selected instruction is replaced by the generated
      instructions for the matrix sequence.
  """
*)

definition replace_with_mats ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> quantum_circuit"
where
  "replace_with_mats qc pos mats =
     (let instr = instructions qc ! pos;
          arity = gate_arity instr;
          params = gate_params instr;
          new_instrs = to_instructions mats arity params
      in replace_instruction qc pos new_instrs)"


(*
  """
    Shows that replacement by a matrix sequence preserves the circuit qubit count.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      mats:
        The replacement matrix sequence.
    
    conclusion:
      The number of qubits is unchanged after replacement.
  """
*)

lemma num_qubits_replace_with_mats:
  "num_qubits (replace_with_mats qc pos mats) = num_qubits qc"
  apply (simp add:
      replace_with_mats_def
      to_instructions_def
      replace_instruction_def create_instruction_def)
  by (metis (lifting) quantum_circuit.select_convs(1) quantum_circuit.surjective
      quantum_circuit.update_convs(2))


(*
  """
    Describes the instruction list after replacing an instruction by a matrix
    sequence.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      mats:
        The replacement matrix sequence.
    
    assumptions:
      The selected position is inside the instruction list.
    
    conclusion:
      The new instruction list consists of the original prefix, the generated
      replacement instructions, and the original suffix after the replaced
      instruction.
  """
*)

lemma instructions_replace_with_mats:
  assumes "pos < length (instructions qc)"
  shows "instructions (replace_with_mats qc pos mats) =
     take pos (instructions qc) @
     to_instructions mats
       (gate_arity ((instructions qc) ! pos))
       (gate_params ((instructions qc) ! pos)) @
     drop (Suc pos) (instructions qc)"
  using assms
  apply (simp add:
      replace_with_mats_def
      replace_instruction_def
      to_instructions_def
      create_instruction_def)
  by (metis instructions_replace replace_instruction_def)


(*
  """
    Proves that replacing a valid circuit instruction by matrix-generated
    instructions preserves circuit validity.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      mats:
        The replacement matrix sequence.
    
    assumptions:
      The original circuit is valid.
    
      The selected position is inside the instruction list.
    
    conclusion:
      The circuit after matrix-sequence replacement is valid.
  """
*)

lemma valid_replace_with_mats:
  assumes "is_valid_circuit qc"
  assumes "pos < length (instructions qc)"
  shows "is_valid_circuit (replace_with_mats qc pos mats)"
proof -
  let ?instr = "(instructions qc) ! pos"
  have instr_valid:
    "is_valid_instruction (num_qubits qc) ?instr"
    using assms
    by (simp add:
        is_valid_circuit_def
        list_all_iff)

  have params_nonempty:
    "gate_params ?instr \<noteq> []"
    using instr_valid
    by (simp add: is_valid_instruction_def)

  have params_distinct:
    "distinct (gate_params ?instr)"
    using instr_valid
    by (simp add: is_valid_instruction_def)

  have params_length:
    "length (gate_params ?instr) = gate_arity ?instr"
    using instr_valid
    by (simp add: is_valid_instruction_def)

  have params_valid:
    "are_valid_qubits (num_qubits qc) (gate_params ?instr)"
    using instr_valid
    by (simp add: is_valid_instruction_def)

  have new_instrs_valid:
    "list_all (is_valid_instruction (num_qubits qc))
       (to_instructions mats (gate_arity ?instr) (gate_params ?instr))"
    using params_nonempty params_distinct params_length params_valid
    by (simp add: valid_to_instructions)

  show ?thesis
    using assms new_instrs_valid
    apply (simp add:
        replace_with_mats_def
        valid_replace
        to_instructions_def
        create_instruction_def
        is_valid_instruction_def)
    by (metis valid_replace)
qed


section \<open>Replacing Gates by Sequence Choices\<close>

(*
  """
    Replaces one instruction using a selected sequence from a sequence table.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to replace.
    
      seqs:
        The available replacement sequence table.
    
      choice:
        The selected replacement alternative.
    
    returns:
      A circuit where the selected instruction is replaced by the chosen matrix
      sequence.
  """
*)

definition replace_with_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "replace_with_choice qc pos seqs choice =
     replace_with_mats qc pos (seqs ! choice)"


(*
  """
    Shows that replacement using a selected sequence preserves the circuit qubit
    count.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      seqs:
        The available replacement sequence table.
    
      choice:
        The selected replacement alternative.
    
    conclusion:
      The number of qubits is unchanged after replacement.
  """
*)

lemma num_qubits_replace_with_choice:
  "num_qubits (replace_with_choice qc pos seqs choice) =
     num_qubits qc"
  by (simp add:
      replace_with_choice_def
      num_qubits_replace_with_mats)


(*
  """
    Describes the instruction list after replacement using a selected sequence.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      seqs:
        The available replacement sequence table.
    
      choice:
        The selected replacement alternative.
    
    assumptions:
      The selected position is inside the instruction list.
    
      The selected alternative is available in the sequence table.
    
    conclusion:
      The resulting instruction list has the chosen generated sequence in place of
      the original instruction.
  """
*)

lemma instructions_replace_with_choice:
  assumes "pos < length (instructions qc)"
  assumes "choice < length seqs"
  shows "instructions (replace_with_choice qc pos seqs choice) =
     take pos (instructions qc) @
     to_instructions (seqs ! choice)
       (gate_arity ((instructions qc) ! pos))
       (gate_params ((instructions qc) ! pos)) @
     drop (Suc pos) (instructions qc)"
  using assms
  by (simp add:
      replace_with_choice_def
      instructions_replace_with_mats)


(*
  """
    Proves that replacement using a valid selected sequence preserves circuit
    validity.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      seqs:
        The available replacement sequence table.
    
      choice:
        The selected replacement alternative.
    
    assumptions:
      The original circuit is valid.
    
      The selected position is inside the instruction list.
    
      The selected alternative is available in the sequence table.
    
    conclusion:
      The circuit after replacement is valid.
  """
*)

lemma valid_replace_with_choice:
  assumes "is_valid_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length seqs"
  shows "is_valid_circuit
           (replace_with_choice qc pos seqs choice)"
  using assms
  by (simp add:
      replace_with_choice_def
      valid_replace_with_mats)


(*
  """
    Checks whether a selected sequence-table alternative exists.
    
    args:
      seqs:
        The available sequence table.
    
      choice:
        The selected alternative index.
    
    returns:
      True when the selected alternative is within the sequence table, and false
      otherwise.
  """
*)

definition is_valid_choice :: "complex mat list list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_valid_choice seqs choice \<longleftrightarrow> choice < length seqs"


(*
  """
    Proves validity preservation for replacement when the replacement request passes
    the helper validity checks.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The position being replaced.
    
      seqs:
        The available replacement sequence table.
    
      choice:
        The selected replacement alternative.
    
    assumptions:
      The original circuit is valid.
    
      The replacement position is valid.
    
      The selected alternative is valid for the sequence table.
    
    conclusion:
      The circuit after replacement is valid.
  """
*)

lemma valid_replace_with_choice_if_valid: (* Rename later  *)
  assumes "is_valid_circuit qc"
  assumes "can_replace_at qc pos"
  assumes "is_valid_choice seqs choice"
  shows "is_valid_circuit
           (replace_with_choice qc pos seqs choice)"
  using assms
  by (simp add:
      can_replace_at_def
      is_valid_choice_def
      valid_replace_with_choice)


section \<open>Replacing Gates by Generated Sequence Choices\<close>

(*
  """
    Generates replacement sequences for the gate at a selected circuit position.
    
    The generator function is applied to the matrix stored by the selected
    instruction.
    
    args:
      seq_fun:
        The function that generates replacement sequences from a gate matrix.
    
      qc:
        The circuit containing the selected instruction.
    
      pos:
        The selected instruction position.
    
    returns:
      The replacement sequences generated for the gate at the selected position.
  """
*)

definition generate_sequences ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list"
where
  "generate_sequences seq_fun qc pos =
     seq_fun (gate_matrix ((instructions qc) ! pos))"


(*
  """
    Replaces one instruction using sequences generated from the instruction's gate.
    
    args:
      seq_fun:
        The function that generates replacement sequences from a gate matrix.
    
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to replace.
    
      choice:
        The selected generated sequence alternative.
    
    returns:
      A circuit where the selected instruction is replaced by the chosen generated
      sequence.
  """
*)

definition replace_with_generated ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "replace_with_generated seq_fun qc pos choice =
     replace_with_choice qc pos
       (generate_sequences seq_fun qc pos)
       choice"


(*
  """
    Shows that replacement using a generated sequence preserves the circuit qubit
    count.
    
    args:
      qc:
        The circuit being modified.
    
      seq_fun:
        The sequence generator.
    
      pos:
        The position being replaced.
    
      choice:
        The selected generated sequence alternative.
    
    conclusion:
      The number of qubits is unchanged after replacement.
  """
*)

lemma num_qubits_replace_with_generated:
  "num_qubits (replace_with_generated seq_fun qc pos choice) =
     num_qubits qc"
  by (simp add:
      replace_with_generated_def
      num_qubits_replace_with_choice)


(*
  """
    Describes the instruction list after replacement using a generated sequence.
    
    args:
      qc:
        The circuit being modified.
    
      seq_fun:
        The sequence generator.
    
      pos:
        The position being replaced.
    
      choice:
        The selected generated sequence alternative.
    
    assumptions:
      The selected position is inside the instruction list.
    
      The selected generated alternative exists.
    
    conclusion:
      The resulting instruction list has the chosen generated sequence in place of
      the original instruction.
  """
*)

lemma instructions_replace_with_generated:
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences seq_fun qc pos)"
  shows "instructions (replace_with_generated seq_fun qc pos choice) =
     take pos (instructions qc) @
     to_instructions ((generate_sequences seq_fun qc pos) ! choice)
       (gate_arity ((instructions qc) ! pos))
       (gate_params ((instructions qc) ! pos)) @
     drop (Suc pos) (instructions qc)"
  using assms
  by (simp add:
      replace_with_generated_def
      instructions_replace_with_choice)


(*
  """
    Checks whether a generated replacement choice is valid.
    
    The check ensures that the circuit position can be replaced and that the
    selected generated sequence exists.
    
    args:
      seq_fun:
        The sequence generator.
    
      qc:
        The circuit being checked.
    
      pos:
        The instruction position.
    
      choice:
        The selected generated sequence alternative.
    
    returns:
      True when the generated replacement request is valid, and false otherwise.
  """
*)

definition is_valid_generated_choice ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_valid_generated_choice seq_fun qc pos choice \<longleftrightarrow>
     can_replace_at qc pos \<and>
     is_valid_choice (generate_sequences seq_fun qc pos) choice"


(*
  """
    Proves that replacement using an available generated sequence preserves circuit
    validity.
    
    args:
      qc:
        The circuit being modified.
    
      seq_fun:
        The sequence generator.
    
      pos:
        The position being replaced.
    
      choice:
        The selected generated sequence alternative.
    
    assumptions:
      The original circuit is valid.
    
      The selected position is inside the instruction list.
    
      The selected generated alternative exists.
    
    conclusion:
      The circuit after generated-sequence replacement is valid.
  """
*)

lemma valid_replace_with_generated:
  assumes "is_valid_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences seq_fun qc pos)"
  shows "is_valid_circuit
           (replace_with_generated seq_fun qc pos choice)"
  using assms
  by (simp add:
      replace_with_generated_def
      valid_replace_with_choice)


(*
  """
    Proves validity preservation for generated replacement when the helper validity
    predicate succeeds.
    
    args:
      qc:
        The circuit being modified.
    
      seq_fun:
        The sequence generator.
    
      pos:
        The position being replaced.
    
      choice:
        The selected generated sequence alternative.
    
    assumptions:
      The original circuit is valid.
    
      The generated replacement request is valid.
    
    conclusion:
      The circuit after generated-sequence replacement is valid.
  """
*)

lemma valid_replace_with_generated_if_valid:
  assumes "is_valid_circuit qc"
  assumes "is_valid_generated_choice seq_fun qc pos choice"
  shows "is_valid_circuit
           (replace_with_generated seq_fun qc pos choice)"
  using assms
  by (simp add:
      is_valid_generated_choice_def
      can_replace_at_def
      is_valid_choice_def
      valid_replace_with_generated)


section \<open>Inserting Matrix Sequences\<close>

(*
  """
    Inserts a matrix sequence into a circuit as instructions.
    
    Each inserted matrix is converted into an instruction using the provided qubit
    parameters. The inserted instruction arity is the number of provided
    parameters.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      mats:
        The matrix sequence to insert.
    
      params:
        The qubit parameters assigned to inserted instructions.
    
    returns:
      A circuit with the generated instructions inserted at the requested position.
  """
*)

definition insert_mats ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_mats qc pos mats params =
     insert_instructions qc pos
       (to_instructions mats (length params) params)"


(*
  """
    Shows that inserting a matrix sequence preserves the circuit qubit count.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      mats:
        The matrix sequence being inserted.
    
      params:
        The qubit parameters assigned to inserted instructions.
    
    conclusion:
      The number of qubits is unchanged after insertion.
  """
*)

lemma num_qubits_insert_mats:
  "num_qubits (insert_mats qc pos mats params) = num_qubits qc"
  by (simp add:
      insert_mats_def
      num_qubits_insert)


(*
  """
    Describes the instruction list after inserting a matrix sequence.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      mats:
        The matrix sequence being inserted.
    
      params:
        The qubit parameters assigned to inserted instructions.
    
    conclusion:
      The resulting instruction list is the original prefix, followed by the
      generated inserted instructions, followed by the original suffix.
  """
*)

lemma instructions_insert_mats:
  "instructions (insert_mats qc pos mats params) =
     take pos (instructions qc) @
     to_instructions mats (length params) params @
     drop pos (instructions qc)"
  by (simp add:
      insert_mats_def
      instructions_insert)


(*
  """
    Proves that inserting matrix-generated instructions preserves circuit validity.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      mats:
        The matrix sequence being inserted.
    
      params:
        The qubit parameters assigned to inserted instructions.
    
    assumptions:
      The original circuit is valid.
    
      The parameter list is nonempty.
    
      The parameter list has no duplicate qubits.
    
      All parameters are valid qubit indices.
    
    conclusion:
      The circuit after insertion is valid.
  """
*)

lemma valid_insert_mats:
  assumes "is_valid_circuit qc"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "are_valid_qubits (num_qubits qc) params"
  shows "is_valid_circuit (insert_mats qc pos mats params)"
  using assms
  by (simp add:
      insert_mats_def
      valid_insert_mats_raw)


(*
  """
    Inserts a selected sequence from a sequence table into a circuit.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      seqs:
        The available sequence table.
    
      choice:
        The selected sequence alternative.
    
      params:
        The qubit parameters assigned to inserted instructions.
    
    returns:
      A circuit with the selected matrix sequence inserted.
  """
*)

definition insert_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_choice qc pos seqs choice params =
     insert_mats qc pos (seqs ! choice) params"


(*
  """
    Checks whether a parameter list is valid for insertion into a circuit.
    
    The check ensures that the parameter list is nonempty, has no duplicate qubits,
    and only refers to qubits inside the circuit.
    
    args:
      qc:
        The circuit providing the qubit bound.
    
      params:
        The parameter list to check.
    
    returns:
      True when the parameter list is structurally valid for the circuit, and false
      otherwise.
  """
*)

definition are_valid_params ::
  "quantum_circuit \<Rightarrow> nat list \<Rightarrow> bool"
where
  "are_valid_params qc params \<longleftrightarrow>
     params \<noteq> [] \<and>
     distinct params \<and>
     are_valid_qubits (num_qubits qc) params"


(*
  """
    Checks whether a selected sequence insertion request is valid.
    
    The check combines validity of the insertion position, validity of the selected
    sequence alternative, and validity of the parameter list.
    
    args:
      qc:
        The circuit being checked.
    
      pos:
        The insertion position.
    
      seqs:
        The available sequence table.
    
      choice:
        The selected sequence alternative.
    
      params:
        The qubit parameters for inserted instructions.
    
    returns:
      True when the insertion request is valid, and false otherwise.
  """
*)

definition is_valid_insert_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "is_valid_insert_choice qc pos seqs choice params \<longleftrightarrow>
     can_insert_at qc pos \<and>
     is_valid_choice seqs choice \<and>
     are_valid_params qc params"


(*
  """
    Proves that inserting a selected valid sequence preserves circuit validity.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      seqs:
        The available sequence table.
    
      choice:
        The selected sequence alternative.
    
      params:
        The qubit parameters for inserted instructions.
    
    assumptions:
      The original circuit is valid.
    
      The selected insertion request is valid.
    
    conclusion:
      The circuit after insertion is valid.
  """
*)

lemma valid_insert_choice:
  assumes "is_valid_circuit qc"
  assumes "is_valid_insert_choice qc pos seqs choice params"
  shows "is_valid_circuit
           (insert_choice qc pos seqs choice params)"
  using assms
  by (simp add:
      insert_choice_def
      is_valid_insert_choice_def
      can_insert_at_def
      is_valid_choice_def
      are_valid_params_def
      valid_insert_mats)


(*
  """
    Proves validity preservation for insertion using explicit validity assumptions.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      seqs:
        The available sequence table.
    
      choice:
        The selected sequence alternative.
    
      params:
        The qubit parameters for inserted instructions.
    
    assumptions:
      The original circuit is valid.
    
      The insertion position is within the valid insertion range.
    
      The selected sequence alternative exists.
    
      The parameter list is nonempty, distinct, and in range.
    
    conclusion:
      The circuit after insertion is valid.
  """
*)

lemma valid_insert_choice_direct:
  assumes "is_valid_circuit qc"
  assumes "pos \<le> length (instructions qc)"
  assumes "choice < length seqs"
  assumes "params \<noteq> []"
  assumes "distinct params"
  assumes "are_valid_qubits (num_qubits qc) params"
  shows "is_valid_circuit
           (insert_choice qc pos seqs choice params)"
  using assms
  by (simp add:
      insert_choice_def
      valid_insert_mats)


section \<open>Obfuscation Step Syntax\<close>

(*
  """
    Defines the syntax of circuit-level obfuscation steps.
    
    The datatype supports replacing a gate by a cloaked sequence, replacing a gate
    by a delayed sequence, and inserting an inverse-pair sequence at a selected
    position.
    
    constructors:
      Cloak:
        Replaces the instruction at a position with a selected cloak alternative.
    
      Delay:
        Replaces the instruction at a position with a selected delayed alternative.
    
      InsertInverse:
        Inserts a selected inverse-pair sequence using the provided qubit
        parameters.
  """
*)

datatype obfuscation_step =
    Cloak nat nat
  | Delay nat nat
  | InsertInverse nat nat "nat list"


(*
Cloak pos choice
Delay pos choice
InsertInverse pos choice params

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


section \<open>Gate-Level Circuit Constructors and Obfuscation Wrappers\<close>

context gate
begin

subsection \<open>Gate Constructors\<close>


(*
  """
    Appends a H gate instruction to a circuit.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    returns:
      A circuit with the H gate appended on the target qubit.
  """
*)

definition h :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "h qc q = append_instruction qc (create_instruction H 1 [q])"


(*
  """
    Appends a X gate instruction to a circuit.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    returns:
      A circuit with the X gate appended on the target qubit.
  """
*)

definition x :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "x qc q = append_instruction qc (create_instruction X 1 [q])"


(*
  """
    Appends a Y gate instruction to a circuit.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    returns:
      A circuit with the Y gate appended on the target qubit.
  """
*)

definition y :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "y qc q = append_instruction qc (create_instruction Y 1 [q])"


(*
  """
    Appends a Z gate instruction to a circuit.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    returns:
      A circuit with the Z gate appended on the target qubit.
  """
*)

definition z :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "z qc q = append_instruction qc (create_instruction Z 1 [q])"


(*
  """
    Appends a S gate instruction to a circuit.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    returns:
      A circuit with the S gate appended on the target qubit.
  """
*)

definition s :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "s qc q = append_instruction qc (create_instruction S 1 [q])"


(*
  """
    Appends a T gate instruction to a circuit.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    returns:
      A circuit with the T gate appended on the target qubit.
  """
*)

definition t :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "t qc q = append_instruction qc (create_instruction T 1 [q])"


(*
  """
    Appends a CNOT gate instruction to a circuit.
    
    args:
      qc:
        The circuit being extended.
    
      control:
        The control qubit.
    
      target:
        The target qubit.
    
    returns:
      A circuit with a CNOT gate appended on the given control and target qubits.
  """
*)

definition cnot :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  quantum_circuit" where
  "cnot qc control target = append_instruction qc (create_instruction CNOT 2 [control, target])"


subsection \<open>Validity Preservation for Gate Constructors\<close>

(*
  """
    Proves that appending a H gate preserves circuit validity.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    assumptions:
      The original circuit is valid.
    
      The target qubit is within the circuit range.
    
    conclusion:
      The circuit after appending the H gate is valid.
  """
*)

lemma valid_h:
  assumes "is_valid_circuit qc"
  assumes "q < num_qubits qc"
  shows "is_valid_circuit (h qc q)"
  using assms
  by (simp add:
      h_def
      valid_append
      is_valid_instruction_def
      are_valid_qubits_def
      create_instruction_def)


(*
  """
    Proves that appending a X gate preserves circuit validity.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    assumptions:
      The original circuit is valid.
    
      The target qubit is within the circuit range.
    
    conclusion:
      The circuit after appending the X gate is valid.
  """
*)

lemma valid_x:
  assumes "is_valid_circuit qc"
  assumes "q < num_qubits qc"
  shows "is_valid_circuit (x qc q)"
  using assms
  by (simp add:
      x_def
      valid_append
      is_valid_instruction_def
      are_valid_qubits_def
      create_instruction_def)


(*
  """
    Proves that appending a Y gate preserves circuit validity.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    assumptions:
      The original circuit is valid.
    
      The target qubit is within the circuit range.
    
    conclusion:
      The circuit after appending the Y gate is valid.
  """
*)

lemma valid_y:
  assumes "is_valid_circuit qc"
  assumes "q < num_qubits qc"
  shows "is_valid_circuit (y qc q)"
  using assms
  by (simp add:
      y_def
      valid_append
      is_valid_instruction_def
      are_valid_qubits_def
      create_instruction_def)


(*
  """
    Proves that appending a Z gate preserves circuit validity.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    assumptions:
      The original circuit is valid.
    
      The target qubit is within the circuit range.
    
    conclusion:
      The circuit after appending the Z gate is valid.
  """
*)

lemma valid_z:
  assumes "is_valid_circuit qc"
  assumes "q < num_qubits qc"
  shows "is_valid_circuit (z qc q)"
  using assms
  by (simp add:
      z_def
      valid_append
      is_valid_instruction_def
      are_valid_qubits_def
      create_instruction_def)


(*
  """
    Proves that appending a S gate preserves circuit validity.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    assumptions:
      The original circuit is valid.
    
      The target qubit is within the circuit range.
    
    conclusion:
      The circuit after appending the S gate is valid.
  """
*)

lemma valid_s:
  assumes "is_valid_circuit qc"
  assumes "q < num_qubits qc"
  shows "is_valid_circuit (s qc q)"
  using assms
  by (simp add:
      s_def
      valid_append
      is_valid_instruction_def
      are_valid_qubits_def
      create_instruction_def)


(*
  """
    Proves that appending a T gate preserves circuit validity.
    
    args:
      qc:
        The circuit being extended.
    
      q:
        The target qubit.
    
    assumptions:
      The original circuit is valid.
    
      The target qubit is within the circuit range.
    
    conclusion:
      The circuit after appending the T gate is valid.
  """
*)

lemma valid_t:
  assumes "is_valid_circuit qc"
  assumes "q < num_qubits qc"
  shows "is_valid_circuit (t qc q)"
  using assms
  by (simp add:
      t_def
      valid_append
      is_valid_instruction_def
      are_valid_qubits_def
      create_instruction_def)


(*
  """
    Proves that appending a CNOT gate preserves circuit validity.
    
    args:
      qc:
        The circuit being extended.
    
      control:
        The control qubit.
    
      target:
        The target qubit.
    
    assumptions:
      The original circuit is valid.
    
      The control and target qubits are within range.
    
      The control and target qubits are distinct.
    
    conclusion:
      The circuit after appending the CNOT gate is valid.
  """
*)

lemma valid_cnot:
  assumes "is_valid_circuit qc"
  assumes "control < num_qubits qc"
  assumes "target < num_qubits qc"
  assumes "control \<noteq> target"
  shows "is_valid_circuit (cnot qc control target)"
  using assms
  by (simp add:
      cnot_def
      valid_append
      is_valid_instruction_def
      are_valid_qubits_def
      create_instruction_def)


subsection \<open>Cloaking and Delaying\<close>

(*
  """
    Applies a cloak replacement to a circuit instruction.
    
    The selected instruction is replaced by a generated cloak sequence for the
    instruction's gate matrix.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to cloak.
    
      choice:
        The selected cloak alternative.
    
    returns:
      A circuit with the selected instruction replaced by the chosen cloak sequence.
  """
*)

definition cloak ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "cloak qc pos choice =
     replace_with_generated cloak_seq qc pos choice"


(*
  """
    Checks whether a cloak replacement request is valid.
    
    args:
      qc:
        The circuit being checked.
    
      pos:
        The instruction position to cloak.
    
      choice:
        The selected cloak alternative.
    
    returns:
      True when the cloak request has a valid position and available generated
      choice, and false otherwise.
  """
*)

definition is_valid_cloak ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_valid_cloak qc pos choice \<longleftrightarrow>
     is_valid_generated_choice cloak_seq qc pos choice"


(*
  """
    Proves that a valid cloak replacement preserves circuit validity.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to cloak.
    
      choice:
        The selected cloak alternative.
    
    assumptions:
      The original circuit is valid.
    
      The cloak request is valid.
    
    conclusion:
      The circuit after cloaking is valid.
  """
*)

lemma valid_cloak:
  assumes "is_valid_circuit qc"
  assumes "is_valid_cloak qc pos choice"
  shows "is_valid_circuit (cloak qc pos choice)"
  using assms
  by (simp add:
      cloak_def
      is_valid_cloak_def
      valid_replace_with_generated_if_valid)


(*
  """
    Proves cloak validity preservation from explicit range assumptions.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to cloak.
    
      choice:
        The selected cloak alternative.
    
    assumptions:
      The original circuit is valid.
    
      The selected position is inside the instruction list.
    
      The selected cloak alternative exists.
    
    conclusion:
      The circuit after cloaking is valid.
  """
*)

lemma valid_cloak_direct:
  assumes "is_valid_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences cloak_seq qc pos)"
  shows "is_valid_circuit (cloak qc pos choice)"
  using assms
  by (simp add:
      cloak_def
      valid_replace_with_generated)


(*
  """
    Applies a delayed-sequence replacement to a circuit instruction.
    
    The selected instruction is replaced by a generated delayed sequence for the
    instruction's gate matrix.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to delay.
    
      choice:
        The selected delayed alternative.
    
    returns:
      A circuit with the selected instruction replaced by the chosen delayed
      sequence.
  """
*)

definition delay ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "delay qc pos choice =
     replace_with_generated delayed_seq qc pos choice"


(*
  """
    Checks whether a delayed replacement request is valid.
    
    args:
      qc:
        The circuit being checked.
    
      pos:
        The instruction position to delay.
    
      choice:
        The selected delayed alternative.
    
    returns:
      True when the delayed replacement request has a valid position and available
      generated choice, and false otherwise.
  """
*)

definition is_valid_delay ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_valid_delay qc pos choice \<longleftrightarrow>
     is_valid_generated_choice delayed_seq qc pos choice"


(*
  """
    Proves that a valid delayed replacement preserves circuit validity.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to delay.
    
      choice:
        The selected delayed alternative.
    
    assumptions:
      The original circuit is valid.
    
      The delayed replacement request is valid.
    
    conclusion:
      The circuit after delayed replacement is valid.
  """
*)

lemma valid_delay:
  assumes "is_valid_circuit qc"
  assumes "is_valid_delay qc pos choice"
  shows "is_valid_circuit (delay qc pos choice)"
  using assms
  by (simp add:
      delay_def
      is_valid_delay_def
      valid_replace_with_generated_if_valid)


(*
  """
    Proves delayed replacement validity preservation from explicit range
    assumptions.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The instruction position to delay.
    
      choice:
        The selected delayed alternative.
    
    assumptions:
      The original circuit is valid.
    
      The selected position is inside the instruction list.
    
      The selected delayed alternative exists.
    
    conclusion:
      The circuit after delayed replacement is valid.
  """
*)

lemma valid_delay_direct:
  assumes "is_valid_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences delayed_seq qc pos)"
  shows "is_valid_circuit (delay qc pos choice)"
  using assms
  by (simp add:
      delay_def
      valid_replace_with_generated)


subsection \<open>Inverse Pair Insertion\<close>

(*
  """
    Inserts an inverse-pair sequence into a circuit.
    
    The selected inverse-pair sequence is inserted at the chosen position using the
    provided qubit parameters.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      choice:
        The selected inverse-pair alternative.
    
      params:
        The qubit parameters assigned to inserted instructions.
    
    returns:
      A circuit with the selected inverse-pair sequence inserted.
  """
*)

definition insert_inverse_pair ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_inverse_pair qc pos choice params =
     insert_choice qc pos inverses choice params"


(*
  """
    Checks whether an inverse-pair insertion request is valid.
    
    args:
      qc:
        The circuit being checked.
    
      pos:
        The insertion position.
    
      choice:
        The selected inverse-pair alternative.
    
      params:
        The qubit parameters for inserted instructions.
    
    returns:
      True when the inverse-pair insertion request is valid, and false otherwise.
  """
*)

definition is_valid_inverse_insert ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "is_valid_inverse_insert qc pos choice params \<longleftrightarrow>
     is_valid_insert_choice qc pos inverses choice params"


(*
  """
    Proves that a valid inverse-pair insertion preserves circuit validity.
    
    args:
      qc:
        The circuit being modified.
    
      pos:
        The insertion position.
    
      choice:
        The selected inverse-pair alternative.
    
      params:
        The qubit parameters for inserted instructions.
    
    assumptions:
      The original circuit is valid.
    
      The inverse-pair insertion request is valid.
    
    conclusion:
      The circuit after inverse-pair insertion is valid.
  """
*)

lemma valid_insert_inverse_pair:
  assumes "is_valid_circuit qc"
  assumes "is_valid_inverse_insert qc pos choice params"
  shows "is_valid_circuit
           (insert_inverse_pair qc pos choice params)"
  using assms
  by (simp add:
      insert_inverse_pair_def
      is_valid_inverse_insert_def
      valid_insert_choice)


subsection \<open>Obfuscation Plans\<close>

(*
  """
    Applies one obfuscation step to a circuit.
    
    The step may be a cloak replacement, delayed replacement, or inverse-pair
    insertion.
    
    args:
      qc:
        The circuit being transformed.
    
      step:
        The obfuscation step to apply.
    
    returns:
      The circuit obtained after applying the step.
  """
*)

fun apply_step ::
  "quantum_circuit \<Rightarrow> obfuscation_step \<Rightarrow> quantum_circuit"
where
  "apply_step qc (Cloak pos choice) =
     cloak qc pos choice"
| "apply_step qc (Delay pos choice) =
     delay qc pos choice"
| "apply_step qc (InsertInverse pos choice params) =
     insert_inverse_pair qc pos choice params"


(*
  """
    Checks whether one obfuscation step is valid for a circuit.
    
    args:
      qc:
        The circuit being checked.
    
      step:
        The obfuscation step to validate.
    
    returns:
      True when the step is valid for the circuit, and false otherwise.
  """
*)

fun is_valid_step ::
  "quantum_circuit \<Rightarrow> obfuscation_step \<Rightarrow> bool"
where
  "is_valid_step qc (Cloak pos choice) =
     is_valid_cloak qc pos choice"
| "is_valid_step qc (Delay pos choice) =
     is_valid_delay qc pos choice"
| "is_valid_step qc (InsertInverse pos choice params) =
     is_valid_inverse_insert qc pos choice params"


(*
  """
    Applies an obfuscation plan to a circuit.
    
    The steps are applied from left to right, with each step operating on the
    circuit produced by the previous step.
    
    args:
      qc:
        The initial circuit.
    
      steps:
        The obfuscation plan.
    
    returns:
      The circuit obtained after applying every step in the plan.
  """
*)

fun apply_plan ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> quantum_circuit"
where
  "apply_plan qc [] = qc"
| "apply_plan qc (step # steps) =
     apply_plan (apply_step qc step) steps"


(*
  """
    Checks whether an obfuscation plan is valid for a circuit.
    
    The plan is valid when the first step is valid for the current circuit and the
    remaining plan is valid for the circuit produced after applying that step.
    
    args:
      qc:
        The initial circuit.
    
      steps:
        The obfuscation plan.
    
    returns:
      True when the full plan is valid, and false otherwise.
  """
*)

fun is_valid_plan ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> bool"
where
  "is_valid_plan qc [] = True"
| "is_valid_plan qc (step # steps) =
     (is_valid_step qc step \<and>
      is_valid_plan (apply_step qc step) steps)"


(*
  """
    Proves that applying a valid obfuscation step preserves circuit validity.
    
    args:
      qc:
        The circuit being transformed.
    
      step:
        The obfuscation step being applied.
    
    assumptions:
      The original circuit is valid.
    
      The selected step is valid for the original circuit.
    
    conclusion:
      The circuit after applying the step is valid.
  """
*)

lemma valid_apply_step:
  assumes "is_valid_circuit qc"
  assumes "is_valid_step qc step"
  shows "is_valid_circuit (apply_step qc step)"
  using assms
  by (cases step)
     (simp_all add:
        valid_cloak
        valid_delay
        valid_insert_inverse_pair)


(*
  """
    Proves that applying a valid obfuscation plan preserves circuit validity.
    
    args:
      qc:
        The initial circuit.
    
      steps:
        The obfuscation plan.
    
    assumptions:
      The original circuit is valid.
    
      The full obfuscation plan is valid.
    
    conclusion:
      The circuit after applying the full plan is valid.
  """
*)

lemma valid_apply_plan:
  assumes "is_valid_circuit qc"
  assumes "is_valid_plan qc steps"
  shows "is_valid_circuit (apply_plan qc steps)"
  using assms
proof (induction steps arbitrary: qc)
  case Nil
  then show ?case
    by simp
next
  case (Cons step steps)
  have step_valid:
    "is_valid_step qc step"
    using Cons.prems
    by simp

  have rest_valid:
    "is_valid_plan (apply_step qc step) steps"
    using Cons.prems
    by simp

  have after_step_valid:
    "is_valid_circuit (apply_step qc step)"
    using Cons.prems(1) step_valid
    by (rule valid_apply_step)

  show ?case
    using Cons.IH[OF after_step_valid rest_valid]
    by simp
qed


subsection \<open>Top-Level Obfuscation Interface\<close>

(*
  """
    Applies the top-level obfuscation interface to a circuit.
    
    This function delegates to the plan application function.
    
    args:
      qc:
        The circuit to obfuscate.
    
      steps:
        The obfuscation plan.
    
    returns:
      The circuit obtained after applying the obfuscation plan.
  """
*)

definition obfuscate ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> quantum_circuit"
where
  "obfuscate qc steps = apply_plan qc steps"


(*
  """
    Proves that top-level obfuscation preserves circuit validity.
    
    args:
      qc:
        The circuit to obfuscate.
    
      steps:
        The obfuscation plan.
    
    assumptions:
      The original circuit is valid.
    
      The obfuscation plan is valid for the original circuit.
    
    conclusion:
      The obfuscated circuit is valid.
  """
*)

lemma valid_obfuscate:
  assumes "is_valid_circuit qc"
  assumes "is_valid_plan qc steps"
  shows "is_valid_circuit (obfuscate qc steps)"
  using assms
  by (simp add:
      obfuscate_def
      valid_apply_plan)

subsection \<open>Examples\<close>

text \<open>
  Example 1:
  Qiskit equivalent:

    qc = QuantumCircuit(1)
    qc.h(0)

  Isabelle circuit:
    one qubit, one H gate acting on qubit 0.
\<close>

(*
  """
    Defines a one-qubit example circuit containing a single H gate.
    
    returns:
      A structural quantum circuit with one qubit and one instruction.
  """
*)

definition example_h_circuit :: quantum_circuit where
  "example_h_circuit = h (initialize_circuit 1) 0"

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

(*
  """
    Defines a two-qubit Bell-style example circuit.
    
    The circuit applies an H gate to the first qubit and then a CNOT gate using the
    first qubit as control and the second qubit as target.
    
    returns:
      A structural quantum circuit with two qubits and two instructions.
  """
*)

definition example_bell_circuit :: quantum_circuit where
  "example_bell_circuit = 
      (let qc0 = initialize_circuit 2;
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

(*
  """
    Defines a three-qubit example circuit.
    
    The circuit applies an H gate, a CNOT gate, an X gate, and a Z gate over three
    qubits.
    
    returns:
      A structural quantum circuit with three qubits and four instructions.
  """
*)

definition example_three_qubit_circuit :: quantum_circuit where
  "example_three_qubit_circuit = 
      (let qc0 = initialize_circuit 3;
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


(*
  """
    Proves that the one-qubit H example circuit is valid.
    
    conclusion:
      The example circuit satisfies the structural circuit validity predicate.
  """
*)

lemma valid_example_h:
  "is_valid_circuit example_h_circuit"
  by (simp add:
      example_h_circuit_def
      h_def
      is_valid_circuit_def
      is_valid_instruction_def
      are_valid_qubits_def
      append_instruction_def
      initialize_circuit_def
      create_circuit_def
      create_instruction_def)


(*
  """
    Proves that the Bell-style example circuit is valid.
    
    conclusion:
      The example circuit satisfies the structural circuit validity predicate.
  """
*)

lemma valid_example_bell:
  "is_valid_circuit example_bell_circuit"
  by (simp add:
      example_bell_circuit_def
      h_def
      cnot_def
      is_valid_circuit_def
      is_valid_instruction_def
      are_valid_qubits_def
      append_instruction_def
      initialize_circuit_def
      create_circuit_def
      create_instruction_def)


(*
  """
    Proves that the three-qubit example circuit is valid.
    
    conclusion:
      The example circuit satisfies the structural circuit validity predicate.
  """
*)

lemma valid_example_three_qubit:
  "is_valid_circuit example_three_qubit_circuit"
  by (simp add:
      example_three_qubit_circuit_def
      h_def
      cnot_def
      x_def
      z_def
      is_valid_circuit_def
      is_valid_instruction_def
      are_valid_qubits_def
      append_instruction_def
      initialize_circuit_def
      create_circuit_def
      create_instruction_def)


(*
  """
    Proves that a concrete replacement operation on the three-qubit example circuit
    preserves validity.
    
    conclusion:
      Replacing the selected example instruction with the selected sequence produces
      a valid circuit.
  """
*)

lemma valid_example_replace_choice:
  "is_valid_circuit
     (replace_with_choice
        example_three_qubit_circuit
        2
        [[S, Y, S, Z], [Z, S, Y, S]]
        0)"
proof (rule valid_replace_with_choice)
  show "is_valid_circuit example_three_qubit_circuit"
    by (rule valid_example_three_qubit)

  show "length (instructions example_three_qubit_circuit) > 2"
    by (simp add:
        example_three_qubit_circuit_def
        h_def cnot_def x_def z_def
        append_instruction_def
        initialize_circuit_def
        create_circuit_def
        create_instruction_def)

  show "length [[S, Y, S, Z], [Z, S, Y, S]] > 0"
    by simp
qed


(* 
value "is_valid_circuit (x (initialize_circuit 3) 2)"
value "is_valid_circuit (x (initialize_circuit 3) 3)"
value "is_valid_circuit (cnot (initialize_circuit 3) 0 1)"
value "is_valid_circuit (cnot (initialize_circuit 3) 0 3)"

value "is_valid_circuit example_h_circuit"
value "is_valid_circuit example_bell_circuit"
value "is_valid_circuit example_three_qubit_circuit"
*)
end

section \<open>Value Checks\<close>

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


value "are_valid_qubits 3 [0, 1, 2]"
value "are_valid_qubits 3 [0, 3]"

value "is_valid_instruction 3 (create_instruction X 1 [2])"
value "is_valid_instruction 3 (create_instruction X 1 [3])"
value "is_valid_instruction 3 (create_instruction X 1 [0, 1])"
value "is_valid_instruction 3 (create_instruction CNOT 2 [0, 1])"
value "is_valid_instruction 3 (create_instruction CNOT 2 [0])"
value "is_valid_instruction 3 (create_instruction CNOT 2 [0, 0])"
end