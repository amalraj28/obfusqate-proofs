theory QuantumCircuitSemantics
  imports QuantumCircuit Circuit
begin

text \<open>
  This theory defines an abstract semantic layer for the structural quantum
  circuit model in QuantumCircuit.thy.

  The structural theory defines circuits as lists of placed instructions and
  provides circuit-level obfuscation operations such as cloaking, delaying, and
  inverse-pair insertion. This theory assigns semantics to those placed
  instructions through an abstract gate-placement function:

    place_gate n G params

  Intuitively, place_gate embeds a local gate matrix G into the full n-qubit
  circuit space, acting on the qubits listed in params.

  The theory assumes three semantic properties of place_gate:
    1. it maps local gates to full-system carrier matrices;
    2. it preserves composition of local gate sequences;
    3. it maps local identity gates to the full-system identity.

  Under these assumptions, the main result is that semantically valid
  obfuscation plans preserve circuit functionality:

    eval_circuit (obfuscate qc steps) = eval_circuit qc

  This proves semantic correctness of the obfuscation framework at the abstract
  placed-gate level. A concrete tensor/permutation-based implementation of
  place_gate can be supplied and proved later as a separate instantiation.
\<close>

locale gate_placement =
  (*
    """
    Defines the abstract interface for placing local quantum gates into a full circuit space.
  
    This locale does not commit to a concrete tensor-product implementation. Instead, it assumes the carrier, composition, and identity laws needed by the semantic preservation proofs.
  
    args:
      place_gate:
        The abstract function that embeds a local gate into an n-qubit circuit using the given qubit parameters.
  
    assumptions:
      Local gates with valid dimensions are placed into full-system matrices with valid dimensions.
  
      Placing a composed local sequence agrees with composing the placed sequence.
  
      Placing a local identity gate gives the full-system identity.
  
    purpose:
      Provides the semantic foundation used to evaluate and reason about placed circuit instructions.
    """
  *)
  fixes place_gate :: "nat \<Rightarrow> complex mat \<Rightarrow> nat list \<Rightarrow> complex mat"

  assumes place_gate_carrier:
    "G \<in> carrier_mat (2 ^ length params) (2 ^ length params)
     \<Longrightarrow> place_gate n G params \<in> carrier_mat (2 ^ n) (2 ^ n)"

  assumes place_gate_compose:
    "\<lbrakk> mats \<noteq> [];
       \<forall>G \<in> set mats. G \<in> carrier_mat (2 ^ length params) (2 ^ length params) \<rbrakk>
     \<Longrightarrow> compose (map (\<lambda>G. place_gate n G params) mats) (2 ^ n)
       = place_gate n (compose mats (2 ^ length params)) params"

  assumes place_gate_identity:
    "place_gate n (1\<^sub>m (2 ^ length params)) params = 1\<^sub>m (2 ^ n)"
begin

section \<open>Evaluation Semantics\<close>

definition eval_instruction ::
  (*
    """
    Evaluates one matrix-based circuit instruction.
  
    The instruction stores a local gate matrix and the qubits on which the gate acts. Evaluation embeds that local gate into the full circuit space using the abstract placement function.
  
    args:
      n:
        The number of qubits in the full circuit.
  
      instr:
        The instruction being evaluated.
  
    returns:
      The full-system matrix corresponding to the placed instruction.
    """
  *)
  "nat \<Rightarrow> instruction \<Rightarrow> complex mat"
where
  "eval_instruction n instr =
     place_gate n (gate_matrix instr) (gate_params instr)"


definition eval_instructions ::
  (*
    """
    Evaluates a list of matrix-based circuit instructions.
  
    Each instruction is evaluated independently using the same circuit size. The result is a list of full-system matrices.
  
    args:
      n:
        The number of qubits in the full circuit.
  
      instrs:
        The instruction list being evaluated.
  
    returns:
      The list of full-system matrices corresponding to the instruction list.
    """
  *)
  "nat \<Rightarrow> instruction list \<Rightarrow> complex mat list"
where
  "eval_instructions n instrs =
     map (eval_instruction n) instrs"


definition eval_circuit ::
  (*
    """
    Evaluates a matrix-based quantum circuit.
  
    The circuit instructions are first converted into full-system matrices. These matrices are then composed in circuit order using the circuit dimension.
  
    args:
      qc:
        The matrix-based quantum circuit being evaluated.
  
    returns:
      The full-system matrix semantics of the circuit.
    """
  *)
  "quantum_circuit \<Rightarrow> complex mat"
where
  "eval_circuit qc =
     compose
       (eval_instructions (num_qubits qc) (instructions qc))
       (2 ^ num_qubits qc)"


lemma eval_instructions_append:
  (*
    """
    Shows that evaluating an appended instruction list distributes over append.
  
    This is a list-shape lemma used when reasoning about circuit edits that split an instruction list into a prefix and suffix.
  
    args:
      n:
        The number of qubits used for instruction evaluation.
  
      xs:
        The first instruction list.
  
      ys:
        The second instruction list.
  
    conclusion:
      Evaluating the appended list gives the appended list of evaluated instructions.
    """
  *)
  "eval_instructions n (xs @ ys) =
   eval_instructions n xs @ eval_instructions n ys"
  by (simp add: eval_instructions_def)


lemma eval_instructions_take:
  (*
    """
    Shows that evaluation commutes with taking a prefix of an instruction list.
  
    This is used when preserving the prefix of a circuit during replacement and insertion proofs.
  
    args:
      n:
        The number of qubits used for instruction evaluation.
  
      k:
        The length of the prefix to keep.
  
      xs:
        The instruction list.
  
    conclusion:
      Evaluating the prefix is the same as taking the prefix after evaluation.
    """
  *)
  "eval_instructions n (take k xs) =
   take k (eval_instructions n xs)"
  by (simp add: eval_instructions_def take_map)


lemma eval_instructions_drop:
  (*
    """
    Shows that evaluation commutes with dropping a prefix of an instruction list.
  
    This is used when preserving the suffix of a circuit during replacement and insertion proofs.
  
    args:
      n:
        The number of qubits used for instruction evaluation.
  
      k:
        The number of leading instructions to drop.
  
      xs:
        The instruction list.
  
    conclusion:
      Evaluating the suffix is the same as taking the suffix after evaluation.
    """
  *)
  "eval_instructions n (drop k xs) =
   drop k (eval_instructions n xs)"
  by (simp add: eval_instructions_def drop_map)


lemma eval_to_instructions:
  (*
    """
    Shows how generated matrix instructions evaluate.
  
    A list of local gate matrices can be converted into instructions using a common arity and parameter list. This lemma states that evaluating those generated instructions places each original local matrix using the same parameters.
  
    args:
      n:
        The number of qubits in the full circuit.
  
      mats:
        The local gate matrices.
  
      arity:
        The arity stored in each generated instruction.
  
      params:
        The qubit parameters stored in each generated instruction.
  
    conclusion:
      The evaluated generated instructions are exactly the placed local matrices.
    """
  *)
  "eval_instructions n (to_instructions mats arity params) =
   map (\<lambda>G. place_gate n G params) mats"
  by (simp add:
      eval_instructions_def
      eval_instruction_def
      to_instructions_def
      create_instruction_def)


section \<open>Replacement and Insertion Shapes\<close>

lemma eval_replace_mats:
  (*
    """
    Describes the evaluated instruction list after replacing one instruction by matrix gates.
  
    The evaluated circuit is split into the unchanged prefix, the placed replacement matrices, and the unchanged suffix after the replaced instruction.
  
    args:
      qc:
        The matrix-based quantum circuit being edited.
  
      pos:
        The position of the instruction being replaced.
  
      mats:
        The replacement local matrices.
  
    assumptions:
      The replacement position is inside the circuit instruction list.
  
    conclusion:
      Evaluation of the replaced circuit has the expected prefix, replacement, and suffix shape.
    """
  *)
  assumes "pos < length (instructions qc)"
  shows
  "eval_instructions (num_qubits qc)
     (instructions (replace_with_mats qc pos mats)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G
          (gate_params ((instructions qc) ! pos))) mats @
   drop (Suc pos) (eval_instructions (num_qubits qc) (instructions qc))"
  using assms
  by (simp add:
      instructions_replace_with_mats
      eval_instructions_append
      eval_instructions_take
      eval_instructions_drop
      eval_to_instructions)


lemma eval_insert_mats:
  (*
    """
    Describes the evaluated instruction list after inserting matrix gates.
  
    The evaluated circuit is split into the unchanged prefix, the placed inserted matrices, and the unchanged suffix starting at the insertion point.
  
    args:
      qc:
        The matrix-based quantum circuit being edited.
  
      pos:
        The insertion position.
  
      mats:
        The inserted local matrices.
  
      params:
        The qubit parameters used by the inserted matrices.
  
    conclusion:
      Evaluation of the circuit after insertion has the expected prefix, insertion, and suffix shape.
    """
  *)
  "eval_instructions (num_qubits qc)
     (instructions (insert_mats qc pos mats params)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G params) mats @
   drop pos (eval_instructions (num_qubits qc) (instructions qc))"
  by (simp add:
      instructions_insert_mats
      eval_instructions_append
      eval_instructions_take
      eval_instructions_drop
      eval_to_instructions)


section \<open>Replacement by Chosen and Generated Sequences\<close>

lemma eval_replace_choice:
  (*
    """
    Describes evaluation after replacing an instruction by a selected sequence.
  
    The selected sequence is taken from a table of local matrix sequences. Evaluation places that selected sequence on the parameters of the instruction being replaced.
  
    args:
      qc:
        The matrix-based quantum circuit being edited.
  
      pos:
        The instruction position being replaced.
  
      seqs:
        The available replacement sequence table.
  
      choice:
        The selected replacement alternative.
  
    assumptions:
      The replacement position is inside the circuit.
  
      The selected alternative is available.
  
    conclusion:
      Evaluation of the resulting circuit has the expected replacement shape.
    """
  *)
  assumes "pos < length (instructions qc)"
  assumes "choice < length seqs"
  shows
  "eval_instructions (num_qubits qc)
     (instructions (replace_with_choice qc pos seqs choice)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G
          (gate_params ((instructions qc) ! pos))) (seqs ! choice) @
   drop (Suc pos) (eval_instructions (num_qubits qc) (instructions qc))"
  using assms
  by (simp add:
      replace_with_choice_def
      eval_replace_mats)


lemma eval_replace_generated:
  (*
    """
    Describes evaluation after replacing an instruction by a generated sequence.
  
    The replacement sequence table is generated from the matrix stored at the selected instruction. The selected generated sequence is then placed on the original instruction parameters.
  
    args:
      seq_fun:
        The sequence generator used to produce alternatives for a local gate.
  
      qc:
        The matrix-based quantum circuit being edited.
  
      pos:
        The instruction position being replaced.
  
      choice:
        The selected generated alternative.
  
    assumptions:
      The replacement position is inside the circuit.
  
      The selected generated alternative is available.
  
    conclusion:
      Evaluation of the resulting circuit has the expected generated-replacement shape.
    """
  *)
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences seq_fun qc pos)"
  shows
  "eval_instructions (num_qubits qc)
     (instructions (replace_with_generated seq_fun qc pos choice)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G
          (gate_params ((instructions qc) ! pos)))
       ((generate_sequences seq_fun qc pos) ! choice) @
   drop (Suc pos) (eval_instructions (num_qubits qc) (instructions qc))"
  using assms
  by (simp add:
      replace_with_generated_def
      eval_replace_choice)


section \<open>Insertion by Chosen Sequences\<close>

lemma eval_insert_choice:
  (*
    """
    Describes evaluation after inserting a selected matrix sequence.
  
    The selected sequence is taken from a table of local matrix sequences and placed using the supplied qubit parameters.
  
    args:
      qc:
        The matrix-based quantum circuit being edited.
  
      pos:
        The insertion position.
  
      seqs:
        The available insertion sequence table.
  
      choice:
        The selected insertion alternative.
  
      params:
        The qubit parameters used by the inserted sequence.
  
    assumptions:
      The selected insertion alternative is available.
  
    conclusion:
      Evaluation of the resulting circuit has the expected insertion shape.
    """
  *)
  assumes "choice < length seqs"
  shows
  "eval_instructions (num_qubits qc)
     (instructions (insert_choice qc pos seqs choice params)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G params) (seqs ! choice) @
   drop pos (eval_instructions (num_qubits qc) (instructions qc))"
  using assms
  by (simp add:
      insert_choice_def
      eval_insert_mats)


section \<open>Carrier Lemmas for Evaluated Instructions\<close>

lemma carrier_placed_seq:
  (*
    """
    Lifts local carrier conditions to placed matrices.
  
    If every local matrix in a sequence has the correct local dimension for the parameter list, then every placed matrix has the full-system dimension.
  
    args:
      mats:
        The local matrix sequence.
  
      n:
        The number of qubits in the full circuit.
  
      params:
        The qubit parameters used for placement.
  
    assumptions:
      Every local matrix has dimensions determined by the parameter list.
  
    conclusion:
      Every placed matrix has dimensions determined by the full circuit size.
    """
  *)
  assumes "\<forall>G \<in> set mats. G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
  shows "\<forall>G \<in> set (map (\<lambda>G. place_gate n G params) mats).
           G \<in> carrier_mat (2 ^ n) (2 ^ n)"
  using assms
  by (auto simp add: place_gate_carrier)


lemma carrier_eval_instructions:
  (*
    """
    Shows that evaluating carrier-correct instructions gives full-system carrier-correct matrices.
  
    Each instruction may have its own parameter list. If the local matrix inside each instruction matches the parameter length of that instruction, then evaluation places every instruction into the full circuit dimension.
  
    args:
      n:
        The number of qubits in the full circuit.
  
      instrs:
        The instruction list being evaluated.
  
    assumptions:
      Every instruction stores a matrix with dimensions matching its parameter list.
  
    conclusion:
      Every evaluated instruction has full-system dimensions.
    """
  *)
  assumes "\<forall>instr \<in> set instrs.
             gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                           (2 ^ length (gate_params instr))"
  shows "\<forall>G \<in> set (eval_instructions n instrs).
           G \<in> carrier_mat (2 ^ n) (2 ^ n)"
  using assms
  by (auto simp add:
      eval_instructions_def
      eval_instruction_def
      place_gate_carrier)

end

section \<open>Specialized Obfuscation Transformations\<close>

locale obfuscation_semantics =
  (*
    """
    Combines gate placement assumptions with the quantum gate locale.
  
    This locale provides the setting for proving that cloak, delay, and inverse insertion transformations preserve circuit semantics.
  
    assumptions:
      The abstract gate placement function satisfies the required carrier, composition, and identity laws.
  
      The standard quantum gate matrices and sequence correctness results are available.
  
    purpose:
      Establishes the semantic preservation theory for circuit-level obfuscation.
    """
  *)
  gate_placement + gate
begin

lemma eval_cloak:
  (*
    """
    Describes evaluation after applying a cloak transformation.
  
    The selected cloak sequence is generated from the gate being replaced and then placed on the original instruction parameters.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being cloaked.
  
      choice:
        The selected cloak alternative.
  
    assumptions:
      The selected position is inside the circuit.
  
      The selected cloak alternative is available.
  
    conclusion:
      Evaluation of the cloaked circuit has the expected replacement shape.
    """
  *)
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences cloak_seq qc pos)"
  shows
  "eval_instructions (num_qubits qc)
     (instructions (cloak qc pos choice)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G
          (gate_params ((instructions qc) ! pos)))
       ((generate_sequences cloak_seq qc pos) ! choice) @
   drop (Suc pos) (eval_instructions (num_qubits qc) (instructions qc))"
  using assms
  by (simp add:
      cloak_def
      eval_replace_generated)


lemma eval_delay:
  (*
    """
    Describes evaluation after applying a delay transformation.
  
    The selected delayed sequence is generated from the gate being replaced and then placed on the original instruction parameters.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being delayed.
  
      choice:
        The selected delayed alternative.
  
    assumptions:
      The selected position is inside the circuit.
  
      The selected delayed alternative is available.
  
    conclusion:
      Evaluation of the delayed circuit has the expected replacement shape.
    """
  *)
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences delayed_seq qc pos)"
  shows
  "eval_instructions (num_qubits qc)
     (instructions (delay qc pos choice)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G
          (gate_params ((instructions qc) ! pos)))
       ((generate_sequences delayed_seq qc pos) ! choice) @
   drop (Suc pos) (eval_instructions (num_qubits qc) (instructions qc))"
  using assms
  by (simp add:
      delay_def
      eval_replace_generated)


lemma eval_insert_inverse:
  (*
    """
    Describes evaluation after inserting a selected inverse-pair sequence.
  
    The selected inverse-pair sequence is placed using the supplied qubit parameters and inserted into the evaluated instruction list.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The insertion position.
  
      choice:
        The selected inverse-pair alternative.
  
      params:
        The qubit parameters used by the inserted inverse pair.
  
    assumptions:
      The selected inverse-pair alternative is available.
  
    conclusion:
      Evaluation of the circuit after inverse-pair insertion has the expected insertion shape.
    """
  *)
  assumes "choice < length inverses"
  shows
  "eval_instructions (num_qubits qc)
     (instructions (insert_inverse_pair qc pos choice params)) =
   take pos (eval_instructions (num_qubits qc) (instructions qc)) @
   map (\<lambda>G. place_gate (num_qubits qc) G params) (inverses ! choice) @
   drop pos (eval_instructions (num_qubits qc) (instructions qc))"
  using assms
  by (simp add:
      insert_inverse_pair_def
      eval_insert_choice)


section \<open>Preservation by Replacement and Insertion\<close>

lemma preserve_replace_mats:
  (*
    """
    Proves semantic preservation for replacing one instruction by an equivalent matrix sequence.
  
    The replacement sequence must have the correct local carrier dimensions and must compose to the same local matrix as the instruction being replaced.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being replaced.
  
      mats:
        The replacement local matrix sequence.
  
    assumptions:
      The selected position is inside the circuit.
  
      Every instruction in the original circuit has the correct carrier dimensions.
  
      Every replacement matrix has the carrier dimensions required by the replaced instruction parameters.
  
      The replacement sequence composes to the original local gate matrix.
  
    conclusion:
      The evaluated circuit is unchanged by the replacement.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes mats_carrier:
    "\<forall>G \<in> set mats.
       G \<in> carrier_mat
             (2 ^ length (gate_params ((instructions qc) ! pos)))
             (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes local_eq:
    "compose mats (2 ^ length (gate_params ((instructions qc) ! pos))) =
     gate_matrix ((instructions qc) ! pos)"
  shows
    "eval_circuit (replace_with_mats qc pos mats) =
     eval_circuit qc"
proof -
  let ?n = "num_qubits qc"
  let ?d = "2 ^ ?n"
  let ?params = "gate_params ((instructions qc) ! pos)"
  let ?old =
    "eval_instructions ?n (instructions qc)"
  let ?new_mid =
    "map (\<lambda>G. place_gate ?n G ?params) mats"

  have old_carrier:
    "\<forall>G \<in> set ?old. G \<in> carrier_mat ?d ?d"
    using qc_carrier
    by (simp add: carrier_eval_instructions)

  have new_mid_carrier:
    "\<forall>G \<in> set ?new_mid. G \<in> carrier_mat ?d ?d"
    using mats_carrier
    by (simp add: carrier_placed_seq)

  have old_mid_eq:
    "?old ! pos =
     place_gate ?n (gate_matrix ((instructions qc) ! pos)) ?params"
    using pos_lt
    by (simp add:
        eval_instructions_def
        eval_instruction_def)

  have new_mid_comp:
    "compose ?new_mid ?d =
     place_gate ?n (gate_matrix ((instructions qc) ! pos)) ?params"
  proof -
    have "compose ?new_mid ?d =
          place_gate ?n
            (compose mats (2 ^ length ?params))
            ?params"
      using mats_carrier
      by (cases "mats = []")
         (simp_all add: place_gate_compose local_eq place_gate_identity)
    also have "... =
          place_gate ?n (gate_matrix ((instructions qc) ! pos)) ?params"
      using local_eq
      by simp
    finally show ?thesis .
  qed

  have replaced_list_eq:
    "eval_instructions ?n
       (instructions (replace_with_mats qc pos mats)) =
     take pos ?old @ ?new_mid @ drop (Suc pos) ?old"
    using pos_lt
    by (simp add: eval_replace_mats)

  have compose_replaced:
    "compose
       (eval_instructions ?n
          (instructions (replace_with_mats qc pos mats)))
       ?d =
     compose ?old ?d"
    using replacement_preservation[
      of pos ?old ?new_mid ?d
    ] pos_lt old_carrier new_mid_carrier old_mid_eq new_mid_comp replaced_list_eq
    apply (simp add: replace_gate_def)
    by (metis eval_instructions_def length_map)
    
  show ?thesis
    using compose_replaced
    by (simp add:
        eval_circuit_def
        num_qubits_replace_with_mats)
qed


lemma preserve_insert_mats:
  (*
    """
    Proves semantic preservation for inserting an identity matrix sequence.
  
    The inserted sequence must have the correct local carrier dimensions and must compose to the local identity matrix for the supplied parameters.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The insertion position.
  
      mats:
        The inserted local matrix sequence.
  
      params:
        The qubit parameters used by the inserted sequence.
  
    assumptions:
      Every instruction in the original circuit has the correct carrier dimensions.
  
      Every inserted matrix has the carrier dimensions required by the supplied parameters.
  
      The inserted sequence composes to the local identity matrix.
  
    conclusion:
      The evaluated circuit is unchanged by the insertion.
    """
  *)
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes mats_carrier:
    "\<forall>G \<in> set mats.
       G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
  assumes local_id:
    "compose mats (2 ^ length params) = 1\<^sub>m (2 ^ length params)"
  shows
    "eval_circuit (insert_mats qc pos mats params) =
     eval_circuit qc"
proof -
  let ?n = "num_qubits qc"
  let ?d = "2 ^ ?n"
  let ?old =
    "eval_instructions ?n (instructions qc)"
  let ?mid =
    "map (\<lambda>G. place_gate ?n G params) mats"

  have old_carrier:
    "\<forall>G \<in> set ?old. G \<in> carrier_mat ?d ?d"
    using qc_carrier
    by (simp add: carrier_eval_instructions)

  have mid_carrier:
    "\<forall>G \<in> set ?mid. G \<in> carrier_mat ?d ?d"
    using mats_carrier
    by (simp add: carrier_placed_seq)

  have mid_comp:
    "compose ?mid ?d = 1\<^sub>m ?d"
  proof -
    have "compose ?mid ?d =
          place_gate ?n
            (compose mats (2 ^ length params))
            params"
      using mats_carrier
      by (cases "mats = []")
         (simp_all add: place_gate_compose local_id place_gate_identity)
    also have "... =
          place_gate ?n (1\<^sub>m (2 ^ length params)) params"
      using local_id
      by simp
    also have "... = 1\<^sub>m ?d"
      by (simp add: place_gate_identity)
    finally show ?thesis .
  qed

  have inserted_list_eq:
    "eval_instructions ?n
       (instructions (insert_mats qc pos mats params)) =
     take pos ?old @ ?mid @ drop pos ?old"
    by (simp add: eval_insert_mats)

  have compose_inserted:
    "compose
       (eval_instructions ?n
          (instructions (insert_mats qc pos mats params)))
       ?d =
     compose ?old ?d"
    using identity_insertion[
      of ?mid ?d ?old pos
    ] old_carrier mid_carrier mid_comp inserted_list_eq
    by (simp add: insert_seq_def)

  show ?thesis
    using compose_inserted
    by (simp add:
        eval_circuit_def
        num_qubits_insert_mats)
qed


section \<open>Preservation for Chosen and Generated Sequences\<close>

lemma preserve_replace_choice:
  (*
    """
    Proves semantic preservation for replacement by a selected equivalent sequence.
  
    This specializes matrix-sequence replacement to the case where the replacement sequence is selected from a table.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being replaced.
  
      seqs:
        The table of replacement alternatives.
  
      choice:
        The selected alternative.
  
    assumptions:
      The selected position is inside the circuit.
  
      The selected alternative is available.
  
      The original circuit and selected sequence have the required carrier dimensions.
  
      The selected sequence composes to the matrix being replaced.
  
    conclusion:
      The evaluated circuit is unchanged by the selected replacement.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes choice_lt: "choice < length seqs"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set (seqs ! choice).
       G \<in> carrier_mat
             (2 ^ length (gate_params ((instructions qc) ! pos)))
             (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes local_eq:
    "compose (seqs ! choice)
       (2 ^ length (gate_params ((instructions qc) ! pos))) =
     gate_matrix ((instructions qc) ! pos)"
  shows
    "eval_circuit (replace_with_choice qc pos seqs choice) =
     eval_circuit qc"
  using assms
  by (simp add:
      replace_with_choice_def
      preserve_replace_mats)


lemma preserve_replace_generated:
  (*
    """
    Proves semantic preservation for replacement by a generated equivalent sequence.
  
    This specializes replacement by choice to the case where the alternatives are generated from the gate stored in the selected instruction.
  
    args:
      seq_fun:
        The sequence generator used to produce replacement alternatives.
  
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being replaced.
  
      choice:
        The selected generated alternative.
  
    assumptions:
      The selected position is inside the circuit.
  
      The selected generated alternative is available.
  
      The original circuit and selected sequence have the required carrier dimensions.
  
      The selected generated sequence composes to the matrix being replaced.
  
    conclusion:
      The evaluated circuit is unchanged by the generated replacement.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes choice_lt: "choice < length (generate_sequences seq_fun qc pos)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set ((generate_sequences seq_fun qc pos) ! choice).
       G \<in> carrier_mat
             (2 ^ length (gate_params ((instructions qc) ! pos)))
             (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes local_eq:
    "compose ((generate_sequences seq_fun qc pos) ! choice)
       (2 ^ length (gate_params ((instructions qc) ! pos))) =
     gate_matrix ((instructions qc) ! pos)"
  shows
    "eval_circuit (replace_with_generated seq_fun qc pos choice) =
     eval_circuit qc"
  using assms
  by (simp add:
      replace_with_generated_def
      preserve_replace_choice)


section \<open>Preservation for Cloaking and Delaying\<close>

lemma preserve_cloak:
  (*
    """
    Proves semantic preservation for a cloak transformation when sequence correctness is provided.
  
    The selected cloak sequence must be available, carrier-correct, and equivalent to the gate being replaced.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being cloaked.
  
      choice:
        The selected cloak alternative.
  
    assumptions:
      The selected position is inside the circuit.
  
      The selected cloak alternative is available.
  
      The original circuit and selected cloak sequence have the required carrier dimensions.
  
      The selected cloak sequence composes to the matrix being replaced.
  
    conclusion:
      The evaluated circuit is unchanged by the cloak transformation.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes choice_lt: "choice < length (generate_sequences cloak_seq qc pos)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set ((generate_sequences cloak_seq qc pos) ! choice).
       G \<in> carrier_mat
             (2 ^ length (gate_params ((instructions qc) ! pos)))
             (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes local_eq:
    "compose ((generate_sequences cloak_seq qc pos) ! choice)
       (2 ^ length (gate_params ((instructions qc) ! pos))) =
     gate_matrix ((instructions qc) ! pos)"
  shows
    "eval_circuit (cloak qc pos choice) =
     eval_circuit qc"
  using assms
  by (simp add:
      cloak_def
      preserve_replace_generated)


lemma preserve_delay:
  (*
    """
    Proves semantic preservation for a delay transformation when sequence correctness is provided.
  
    The selected delayed sequence must be available, carrier-correct, and equivalent to the gate being replaced.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being delayed.
  
      choice:
        The selected delayed alternative.
  
    assumptions:
      The selected position is inside the circuit.
  
      The selected delayed alternative is available.
  
      The original circuit and selected delayed sequence have the required carrier dimensions.
  
      The selected delayed sequence composes to the matrix being replaced.
  
    conclusion:
      The evaluated circuit is unchanged by the delay transformation.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes choice_lt: "choice < length (generate_sequences delayed_seq qc pos)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set ((generate_sequences delayed_seq qc pos) ! choice).
       G \<in> carrier_mat
             (2 ^ length (gate_params ((instructions qc) ! pos)))
             (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes local_eq:
    "compose ((generate_sequences delayed_seq qc pos) ! choice)
       (2 ^ length (gate_params ((instructions qc) ! pos))) =
     gate_matrix ((instructions qc) ! pos)"
  shows
    "eval_circuit (delay qc pos choice) =
     eval_circuit qc"
  using assms
  by (simp add:
      delay_def
      preserve_replace_generated)


section \<open>Preservation for Insertion\<close>

lemma preserve_insert_choice:
  (*
    """
    Proves semantic preservation for inserting a selected identity sequence.
  
    This specializes matrix-sequence insertion to the case where the inserted sequence is selected from a table.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The insertion position.
  
      seqs:
        The table of insertion alternatives.
  
      choice:
        The selected insertion alternative.
  
      params:
        The qubit parameters used by the inserted sequence.
  
    assumptions:
      The selected alternative is available.
  
      The original circuit and selected sequence have the required carrier dimensions.
  
      The selected sequence composes to the local identity matrix.
  
    conclusion:
      The evaluated circuit is unchanged by the selected insertion.
    """
  *)
  assumes choice_lt: "choice < length seqs"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set (seqs ! choice).
       G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
  assumes local_id:
    "compose (seqs ! choice) (2 ^ length params) =
     1\<^sub>m (2 ^ length params)"
  shows
    "eval_circuit (insert_choice qc pos seqs choice params) =
     eval_circuit qc"
  using assms
  by (simp add:
      insert_choice_def
      preserve_insert_mats)


lemma preserve_insert_inverse:
  (*
    """
    Proves semantic preservation for inserting a selected inverse-pair sequence.
  
    The selected inverse-pair sequence must be available, carrier-correct, and compose to the local identity matrix.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The insertion position.
  
      choice:
        The selected inverse-pair alternative.
  
      params:
        The qubit parameters used by the inserted inverse pair.
  
    assumptions:
      The selected inverse-pair alternative is available.
  
      The original circuit and selected inverse-pair sequence have the required carrier dimensions.
  
      The selected inverse-pair sequence composes to the local identity matrix.
  
    conclusion:
      The evaluated circuit is unchanged by inverse-pair insertion.
    """
  *)
  assumes choice_lt: "choice < length inverses"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set (inverses ! choice).
       G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
  assumes local_id:
    "compose (inverses ! choice) (2 ^ length params) =
     1\<^sub>m (2 ^ length params)"
  shows
    "eval_circuit (insert_inverse_pair qc pos choice params) =
     eval_circuit qc"
  using assms
  by (simp add:
      insert_inverse_pair_def
      preserve_insert_choice)


section \<open>Preservation for Basis Transformation\<close>

lemma global_basis_sequence_correct:
  assumes B_carrier: "B \<in> carrier_mat d d"
  assumes Binv_carrier: "Binv \<in> carrier_mat d d"
  assumes G_carrier: "G \<in> carrier_mat d d"
  assumes left_inv: "Binv * B = 1\<^sub>m d"
  assumes right_inv: "B * Binv = 1\<^sub>m d"
  shows "compose (global_basis_sequence B Binv G) d = G"
proof -
  have BG_carrier: "B * G \<in> carrier_mat d d"
    using B_carrier G_carrier by simp
  have BGBinv_carrier: "B * G * Binv \<in> carrier_mat d d"
    using BG_carrier Binv_carrier by simp
  have "compose (global_basis_sequence B Binv G) d =
        Binv * ((B * G * Binv) * B)"
    using B_carrier Binv_carrier BGBinv_carrier
    by (simp add: global_basis_sequence_def global_basis_matrix_def)
  also have "... = Binv * ((B * G) * (Binv * B))"
    using B_carrier Binv_carrier G_carrier BG_carrier
    by (smt (verit) assoc_mult_mat mult_carrier_mat)
  also have "... = Binv * ((B * G) * 1\<^sub>m d)"
    using left_inv by simp
  also have "... = Binv * (B * G)"
    using BG_carrier by auto
  also have "... = (Binv * B) * G"
    using B_carrier Binv_carrier G_carrier
    by simp
  also have "... = 1\<^sub>m d * G"
    using left_inv by simp
  also have "... = G"
    using G_carrier by simp
  finally show ?thesis .
qed

lemma selective_basis_sequence_correct:
  assumes B_carrier: "B \<in> carrier_mat d d"
  assumes Binv_carrier: "Binv \<in> carrier_mat d d"
  assumes G_carrier: "G \<in> carrier_mat d d"
  assumes left_inv: "Binv * B = 1\<^sub>m d"
  assumes right_inv: "B * Binv = 1\<^sub>m d"
  shows "compose (selective_basis_sequence B Binv G) d = G"
proof -
  have BinvG_carrier: "Binv * G \<in> carrier_mat d d"
    using Binv_carrier G_carrier by simp
  have BinvGB_carrier: "Binv * G * B \<in> carrier_mat d d"
    using BinvG_carrier B_carrier by simp
  have "compose (selective_basis_sequence B Binv G) d =
        B * ((Binv * G * B) * Binv)"
    using B_carrier Binv_carrier BinvGB_carrier
    by (simp add: selective_basis_sequence_def selective_basis_matrix_def)
  also have "... = B * ((Binv * G) * (B * Binv))"
    using B_carrier Binv_carrier G_carrier BinvG_carrier
    by (smt (verit) assoc_mult_mat mult_carrier_mat)
  also have "... = B * ((Binv * G) * 1\<^sub>m d)"
    using right_inv by simp
  also have "... = B * (Binv * G)"
    using BinvG_carrier by auto
  also have "... = (B * Binv) * G"
    using B_carrier Binv_carrier G_carrier
    by simp
  also have "... = 1\<^sub>m d * G"
    using right_inv by simp
  also have "... = G"
    using G_carrier by simp
  finally show ?thesis .
qed

lemma global_basis_sequence_carrier:
  assumes "B \<in> carrier_mat d d"
  assumes "Binv \<in> carrier_mat d d"
  assumes "G \<in> carrier_mat d d"
  shows "\<forall>M \<in> set (global_basis_sequence B Binv G). M \<in> carrier_mat d d"
  using assms
  by (simp add: global_basis_sequence_def global_basis_matrix_def)

lemma selective_basis_sequence_carrier:
  assumes "B \<in> carrier_mat d d"
  assumes "Binv \<in> carrier_mat d d"
  assumes "G \<in> carrier_mat d d"
  shows "\<forall>M \<in> set (selective_basis_sequence B Binv G). M \<in> carrier_mat d d"
  using assms
  by (simp add: selective_basis_sequence_def selective_basis_matrix_def)

lemma preserve_global_basis:
  assumes pos_lt: "pos < length (instructions qc)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes B_carrier:
    "B \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes Binv_carrier:
    "Binv \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes left_inv:
    "Binv * B =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes right_inv:
    "B * Binv =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
  shows "eval_circuit (apply_global_basis qc pos B Binv) = eval_circuit qc"
proof -
  let ?instr = "(instructions qc) ! pos"
  let ?d = "2 ^ length (gate_params ?instr)"
  have G_carrier: "gate_matrix ?instr \<in> carrier_mat ?d ?d"
    using pos_lt qc_carrier
    by simp
  have seq_carrier:
    "\<forall>M \<in> set (global_basis_sequence B Binv (gate_matrix ?instr)).
       M \<in> carrier_mat ?d ?d"
    using B_carrier Binv_carrier G_carrier
    by (rule global_basis_sequence_carrier)
  have local_eq:
    "compose (global_basis_sequence B Binv (gate_matrix ?instr)) ?d =
     gate_matrix ?instr"
    using B_carrier Binv_carrier G_carrier left_inv right_inv
    by (rule global_basis_sequence_correct)
  show ?thesis
    using pos_lt qc_carrier seq_carrier local_eq
    by (simp add:
        apply_global_basis_def
        preserve_replace_mats)
qed

lemma preserve_selective_basis:
  assumes pos_lt: "pos < length (instructions qc)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes B_carrier:
    "B \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes Binv_carrier:
    "Binv \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes left_inv:
    "Binv * B =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes right_inv:
    "B * Binv =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
  shows "eval_circuit (apply_selective_basis qc pos B Binv) = eval_circuit qc"
proof -
  let ?instr = "(instructions qc) ! pos"
  let ?d = "2 ^ length (gate_params ?instr)"
  have G_carrier: "gate_matrix ?instr \<in> carrier_mat ?d ?d"
    using pos_lt qc_carrier
    by simp
  have seq_carrier:
    "\<forall>M \<in> set (selective_basis_sequence B Binv (gate_matrix ?instr)).
       M \<in> carrier_mat ?d ?d"
    using B_carrier Binv_carrier G_carrier
    by (rule selective_basis_sequence_carrier)
  have local_eq:
    "compose (selective_basis_sequence B Binv (gate_matrix ?instr)) ?d =
     gate_matrix ?instr"
    using B_carrier Binv_carrier G_carrier left_inv right_inv
    by (rule selective_basis_sequence_correct)
  show ?thesis
    using pos_lt qc_carrier seq_carrier local_eq
    by (simp add:
        apply_selective_basis_def
        preserve_replace_mats)
qed


section \<open>Preservation from Sequence Correctness\<close>

lemma preserve_cloak_seq:
  (*
    """
    Proves semantic preservation for cloak using the existing cloak-sequence correctness theorem.
  
    This theorem derives the local equivalence of the selected cloak sequence from the cloak sequence correctness result, then applies the general cloak preservation theorem.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being cloaked.
  
      choice:
        The selected cloak alternative.
  
    assumptions:
      The selected position and cloak alternative are valid.
  
      The original circuit and selected cloak sequence have the required carrier dimensions.
  
      The replaced instruction has single-qubit parameters.
  
    conclusion:
      The evaluated circuit is unchanged by the cloak transformation.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes choice_lt: "choice < length (generate_sequences cloak_seq qc pos)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set ((generate_sequences cloak_seq qc pos) ! choice).
       G \<in> carrier_mat
             (2 ^ length (gate_params ((instructions qc) ! pos)))
             (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes arity_eq:
    "length (gate_params ((instructions qc) ! pos)) = 1"
  shows
    "eval_circuit (cloak qc pos choice) =
     eval_circuit qc"
proof -
  let ?G = "gate_matrix ((instructions qc) ! pos)"

    have local_eq:
    "compose ((generate_sequences cloak_seq qc pos) ! choice)
       (2 ^ length (gate_params ((instructions qc) ! pos))) =
     gate_matrix ((instructions qc) ! pos)"
  proof -
    let ?G = "gate_matrix ((instructions qc) ! pos)"

    have choice_lt_cloak:
      "choice < length (cloak_seq ?G)"
      using choice_lt
      by (simp add: generate_sequences_def)

    have cloak_eq:
      "compose ((cloak_seq ?G) ! choice) 2 = ?G"
      using choice_lt_cloak
      by (metis arity_eq carrier_matD(1) cloak_seq_correct nth_mem pos_lt power_one_right qc_carrier)

    show ?thesis
      using cloak_eq arity_eq
      by (simp add: generate_sequences_def)
  qed

  show ?thesis
    using pos_lt choice_lt qc_carrier seq_carrier local_eq
    by (rule preserve_cloak)
qed


lemma preserve_delay_seq:
  (*
    """
    Proves semantic preservation for delay using the existing delayed-sequence correctness theorem.
  
    This theorem derives the local equivalence of the selected delayed sequence from the delayed sequence correctness result, then applies the general delay preservation theorem.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      pos:
        The instruction position being delayed.
  
      choice:
        The selected delayed alternative.
  
    assumptions:
      The selected position and delayed alternative are valid.
  
      The original circuit and selected delayed sequence have the required carrier dimensions.
  
      The replaced instruction has single-qubit parameters.
  
    conclusion:
      The evaluated circuit is unchanged by the delay transformation.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes choice_lt: "choice < length (generate_sequences delayed_seq qc pos)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes seq_carrier:
    "\<forall>G \<in> set ((generate_sequences delayed_seq qc pos) ! choice).
       G \<in> carrier_mat
             (2 ^ length (gate_params ((instructions qc) ! pos)))
             (2 ^ length (gate_params ((instructions qc) ! pos)))"
  assumes arity_eq:
    "length (gate_params ((instructions qc) ! pos)) = 1"
  shows
    "eval_circuit (delay qc pos choice) =
     eval_circuit qc"
proof -
  let ?G = "gate_matrix ((instructions qc) ! pos)"

  have local_eq:
    "compose ((generate_sequences delayed_seq qc pos) ! choice)
       (2 ^ length (gate_params ((instructions qc) ! pos))) =
     gate_matrix ((instructions qc) ! pos)"
  proof -
    have "compose ((delayed_seq ?G) ! choice) 2 = ?G"
      using choice_lt
      by (metis arity_eq carrier_matD(1) delayed_seq_correct generate_sequences_def nth_mem pos_lt power_one_right
          qc_carrier)
    then show ?thesis
      using arity_eq
      by (simp add: generate_sequences_def)
  qed

  show ?thesis
    using pos_lt choice_lt qc_carrier seq_carrier local_eq
    by (rule preserve_delay)
qed


section \<open>Preservation for Steps and Plans\<close>

definition has_circuit_carrier ::
  (*
    """
    Checks whether every instruction in a matrix-based circuit has a local gate matrix whose dimensions match its parameter list.
  
    This predicate packages the carrier condition required by the semantic preservation proofs.
  
    args:
      qc:
        The matrix-based quantum circuit being checked.
  
    returns:
      True when every instruction has a gate matrix with dimensions matching its parameter list, and False otherwise.
    """
  *)
  "quantum_circuit \<Rightarrow> bool"
where
  "has_circuit_carrier qc \<longleftrightarrow>
     (\<forall>instr \<in> set (instructions qc).
        gate_matrix instr \<in> carrier_mat
          (2 ^ length (gate_params instr))
          (2 ^ length (gate_params instr)))"


definition has_sequence_carrier ::
  (*
    """
    Checks whether a selected sequence alternative has the carrier dimensions required by a parameter list.
  
    This predicate packages the sequence carrier condition used by the semantic step predicate.
  
    args:
      seqs:
        The table of matrix sequence alternatives.
  
      choice:
        The selected alternative.
  
      params:
        The qubit parameters used by the selected sequence.
  
    returns:
      True when every matrix in the selected sequence has dimensions matching the parameter list, and False otherwise.
    """
  *)
  "complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "has_sequence_carrier seqs choice params \<longleftrightarrow>
     (\<forall>G \<in> set (seqs ! choice).
        G \<in> carrier_mat (2 ^ length params) (2 ^ length params))"


fun is_semantic_step ::
  (*
    """
    Checks whether one obfuscation step has enough semantic side conditions for preservation.
  
    The predicate records the position, choice, carrier, arity, and local identity conditions needed by the one-step semantic preservation theorem.
  
    args:
      qc:
        The matrix-based quantum circuit to which the step will be applied.
  
      step:
        The obfuscation step being checked.
  
    returns:
      True when the step satisfies the semantic preservation side conditions, and False otherwise.
    """
  *)
  "quantum_circuit \<Rightarrow> obfuscation_step \<Rightarrow> bool"
where
  "is_semantic_step qc (Cloak pos choice) =
     (pos < length (instructions qc) \<and>
      choice < length (generate_sequences cloak_seq qc pos) \<and>
      has_circuit_carrier qc \<and>
      has_sequence_carrier
        (generate_sequences cloak_seq qc pos)
        choice
        (gate_params ((instructions qc) ! pos)) \<and>
      length (gate_params ((instructions qc) ! pos)) = 1)"

| "is_semantic_step qc (Delay pos choice) =
     (pos < length (instructions qc) \<and>
      choice < length (generate_sequences delayed_seq qc pos) \<and>
      has_circuit_carrier qc \<and>
      has_sequence_carrier
        (generate_sequences delayed_seq qc pos)
        choice
        (gate_params ((instructions qc) ! pos)) \<and>
      length (gate_params ((instructions qc) ! pos)) = 1)"

| "is_semantic_step qc (InsertInverse pos choice params) =
     (choice < length inverses \<and>
      has_circuit_carrier qc \<and>
      has_sequence_carrier inverses choice params \<and>
      compose (inverses ! choice) (2 ^ length params) = 1\<^sub>m (2 ^ length params))"

| "is_semantic_step qc (GlobalBasis pos B Binv) =
     (pos < length (instructions qc) \<and>
      has_circuit_carrier qc \<and>
      B \<in> carrier_mat
            (2 ^ length (gate_params ((instructions qc) ! pos)))
            (2 ^ length (gate_params ((instructions qc) ! pos))) \<and>
      Binv \<in> carrier_mat
            (2 ^ length (gate_params ((instructions qc) ! pos)))
            (2 ^ length (gate_params ((instructions qc) ! pos))) \<and>
      Binv * B =
        1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos))) \<and>
      B * Binv =
        1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos))))"

| "is_semantic_step qc (SelectiveBasis pos B Binv) =
     (pos < length (instructions qc) \<and>
      has_circuit_carrier qc \<and>
      B \<in> carrier_mat
            (2 ^ length (gate_params ((instructions qc) ! pos)))
            (2 ^ length (gate_params ((instructions qc) ! pos))) \<and>
      Binv \<in> carrier_mat
            (2 ^ length (gate_params ((instructions qc) ! pos)))
            (2 ^ length (gate_params ((instructions qc) ! pos))) \<and>
      Binv * B =
        1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos))) \<and>
      B * Binv =
        1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos))))"
      


lemma preserve_step:
  (*
    """
    Proves semantic preservation for one semantically valid obfuscation step.
  
    The proof dispatches on whether the step is cloak, delay, or inverse insertion, then applies the corresponding specialized preservation theorem.
  
    args:
      qc:
        The matrix-based quantum circuit being transformed.
  
      step:
        The obfuscation step being applied.
  
    assumptions:
      The step satisfies the semantic preservation side conditions for the input circuit.
  
    conclusion:
      The evaluated circuit is unchanged after applying the step.
    """
  *)
  assumes step_sem: "is_semantic_step qc step"
  shows "eval_circuit (apply_step qc step) = eval_circuit qc"
proof (cases step)
  case (Cloak pos choice)

  have pos_lt:
    "pos < length (instructions qc)"
    using step_sem Cloak
    by simp

  have choice_lt:
    "choice < length (generate_sequences cloak_seq qc pos)"
    using step_sem Cloak
    by simp

  have qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat
         (2 ^ length (gate_params instr))
         (2 ^ length (gate_params instr))"
    using step_sem Cloak
    by (simp add: has_circuit_carrier_def)

  have seq_carrier:
    "\<forall>G \<in> set ((generate_sequences cloak_seq qc pos) ! choice).
       G \<in> carrier_mat
         (2 ^ length (gate_params ((instructions qc) ! pos)))
         (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem Cloak
    by (meson is_semantic_step.simps(1) has_sequence_carrier_def)

  have arity_eq:
    "length (gate_params ((instructions qc) ! pos)) = 1"
    using step_sem Cloak
    by simp

  have preserve:
    "eval_circuit (cloak qc pos choice) = eval_circuit qc"
    using pos_lt choice_lt qc_carrier seq_carrier arity_eq
    by (rule preserve_cloak_seq)

  show ?thesis
    using Cloak preserve
    by simp

next
  case (Delay pos choice)

  have pos_lt:
    "pos < length (instructions qc)"
    using step_sem Delay
    by simp

  have choice_lt:
    "choice < length (generate_sequences delayed_seq qc pos)"
    using step_sem Delay
    by simp

  have qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat
         (2 ^ length (gate_params instr))
         (2 ^ length (gate_params instr))"
    using step_sem Delay
    by (simp add: has_circuit_carrier_def)

  have seq_carrier:
    "\<forall>G \<in> set ((generate_sequences delayed_seq qc pos) ! choice).
       G \<in> carrier_mat
         (2 ^ length (gate_params ((instructions qc) ! pos)))
         (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem Delay
    by (meson is_semantic_step.simps(2) has_sequence_carrier_def)

  have arity_eq:
    "length (gate_params ((instructions qc) ! pos)) = 1"
    using step_sem Delay
    by simp

  have preserve:
    "eval_circuit (delay qc pos choice) = eval_circuit qc"
    using pos_lt choice_lt qc_carrier seq_carrier arity_eq
    by (rule preserve_delay_seq)

  show ?thesis
    using Delay preserve
    by simp

next
  case (InsertInverse pos choice params)

  have choice_lt:
    "choice < length inverses"
    using step_sem InsertInverse
    by simp

  have qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat
         (2 ^ length (gate_params instr))
         (2 ^ length (gate_params instr))"
    using step_sem InsertInverse
    by (simp add: has_circuit_carrier_def)

  have seq_carrier:
    "\<forall>G \<in> set (inverses ! choice).
       G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
    using step_sem InsertInverse
    by (simp add: has_sequence_carrier_def)

  have local_id:
    "compose (inverses ! choice) (2 ^ length params) =
     1\<^sub>m (2 ^ length params)"
    using step_sem InsertInverse
    by simp

  have preserve:
    "eval_circuit (insert_inverse_pair qc pos choice params) =
     eval_circuit qc"
    apply (rule preserve_insert_inverse)
       apply (rule choice_lt)
      apply (rule qc_carrier)
     apply (rule seq_carrier)
    apply (rule local_id)
    done

  show ?thesis
    using InsertInverse preserve
    by simp

next
  case (GlobalBasis pos B Binv)

  have pos_lt:
    "pos < length (instructions qc)"
    using step_sem GlobalBasis
    by simp

  have qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat
         (2 ^ length (gate_params instr))
         (2 ^ length (gate_params instr))"
    using step_sem GlobalBasis
    by (simp add: has_circuit_carrier_def)

  have B_carrier:
    "B \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem GlobalBasis
    by simp

  have Binv_carrier:
    "Binv \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem GlobalBasis
    by simp

  have left_inv:
    "Binv * B =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem GlobalBasis
    by simp

  have right_inv:
    "B * Binv =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem GlobalBasis
    by simp

  have preserve:
    "eval_circuit (apply_global_basis qc pos B Binv) = eval_circuit qc"
    using pos_lt qc_carrier B_carrier Binv_carrier left_inv right_inv
    by (rule preserve_global_basis)

  show ?thesis
    using GlobalBasis preserve
    by simp

next
  case (SelectiveBasis pos B Binv)

  have pos_lt:
    "pos < length (instructions qc)"
    using step_sem SelectiveBasis
    by simp

  have qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat
         (2 ^ length (gate_params instr))
         (2 ^ length (gate_params instr))"
    using step_sem SelectiveBasis
    by (simp add: has_circuit_carrier_def)

  have B_carrier:
    "B \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem SelectiveBasis
    by simp

  have Binv_carrier:
    "Binv \<in> carrier_mat
          (2 ^ length (gate_params ((instructions qc) ! pos)))
          (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem SelectiveBasis
    by simp

  have left_inv:
    "Binv * B =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem SelectiveBasis
    by simp

  have right_inv:
    "B * Binv =
     1\<^sub>m (2 ^ length (gate_params ((instructions qc) ! pos)))"
    using step_sem SelectiveBasis
    by simp

  have preserve:
    "eval_circuit (apply_selective_basis qc pos B Binv) = eval_circuit qc"
    using pos_lt qc_carrier B_carrier Binv_carrier left_inv right_inv
    by (rule preserve_selective_basis)

  show ?thesis
    using SelectiveBasis preserve
    by simp

qed


fun is_semantic_plan ::
  (*
    """
    Checks whether an obfuscation plan is semantically valid step by step.
  
    Each step must be semantically valid for the circuit produced by all previous steps.
  
    args:
      qc:
        The matrix-based quantum circuit at the start of the plan.
  
      steps:
        The obfuscation plan to check.
  
    returns:
      True when every step in the plan satisfies its semantic preservation side conditions at the point where it is applied, and False otherwise.
    """
  *)
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> bool"
where
  "is_semantic_plan qc [] = True"
| "is_semantic_plan qc (step # steps) =
     (is_semantic_step qc step \<and>
      is_semantic_plan (apply_step qc step) steps)"


lemma preserve_plan:
  (*
    """
    Proves semantic preservation for a semantically valid obfuscation plan.
  
    The proof proceeds by induction over the plan. Each step preserves semantics, and the remaining plan preserves the semantics of the intermediate circuit.
  
    args:
      qc:
        The matrix-based quantum circuit at the start of the plan.
  
      steps:
        The obfuscation plan being applied.
  
    assumptions:
      The plan is semantically valid step by step.
  
    conclusion:
      The evaluated circuit is unchanged after applying the full plan.
    """
  *)
  assumes "is_semantic_plan qc steps"
  shows "eval_circuit (apply_plan qc steps) = eval_circuit qc"
  using assms
proof (induction steps arbitrary: qc)
  case Nil
  then show ?case
    by simp
next
  case (Cons step steps)

  have step_sem:
    "is_semantic_step qc step"
    using Cons.prems
    by simp

  have rest_sem:
    "is_semantic_plan (apply_step qc step) steps"
    using Cons.prems
    by simp

  have step_preserve:
    "eval_circuit (apply_step qc step) = eval_circuit qc"
    using step_sem
    by (rule preserve_step)

  have rest_preserve:
    "eval_circuit
       (apply_plan (apply_step qc step) steps) =
     eval_circuit (apply_step qc step)"
    using Cons.IH[OF rest_sem]
    by simp

  show ?case
    using step_preserve rest_preserve
    by simp
qed

lemma preserve_obfuscate:
  (*
    """
    Proves semantic preservation for the top-level matrix-based obfuscation function.
  
    The top-level obfuscation function applies a semantically valid plan to a matrix-based circuit. This theorem reuses plan preservation to show that the circuit semantics is unchanged.
  
    args:
      qc:
        The matrix-based quantum circuit being obfuscated.
  
      steps:
        The obfuscation plan being applied.
  
    assumptions:
      The obfuscation plan is semantically valid step by step for the input circuit.
  
    conclusion:
      The evaluated circuit is unchanged by top-level obfuscation.
    """
  *)
  assumes "is_semantic_plan qc steps"
  shows "eval_circuit (obfuscate qc steps) = eval_circuit qc"
  using assms
  by (simp add:
      obfuscate_def
      preserve_plan)

end

end
