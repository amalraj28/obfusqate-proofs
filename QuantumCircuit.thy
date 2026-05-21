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


record instruction =
  gate_matrix :: "complex mat" (* The gate itself *)
  gate_params :: "nat list" (* Which qubit(s) is/are the gate acting on *)
  gate_arity :: nat (* Number of qubits the gate is acting on *)


record quantum_circuit =
  num_qubits   :: nat
  instructions :: "instruction list"


definition create_instruction :: "complex mat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> instruction" where
  "create_instruction Gate arity params =
     \<lparr> gate_matrix = Gate, gate_params = params, gate_arity = arity\<rparr>" (* Bracket of a record *)


definition create_circuit :: "nat \<Rightarrow> instruction list \<Rightarrow> quantum_circuit" where
  "create_circuit n instrs =
     \<lparr> num_qubits = n, instructions = instrs \<rparr>"


definition initialize_circuit :: "nat \<Rightarrow> quantum_circuit" where
  "initialize_circuit n = create_circuit n []"


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

definition to_instructions ::
  "complex mat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> instruction list"
where
  "to_instructions mats arity params =
     map (\<lambda>G. create_instruction G arity params) mats"

lemma length_to_instructions:
  "length (to_instructions mats arity params) = length mats"
  by (simp add: to_instructions_def)


lemma to_instructions_Nil:
  "to_instructions [] arity params = []"
  by (simp add: to_instructions_def)


lemma to_instructions_Cons:
  "to_instructions (G # Gs) arity params =
     create_instruction G arity params # to_instructions Gs arity params"
  by (simp add: to_instructions_def)


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

definition replace_with_mats ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> quantum_circuit"
where
  "replace_with_mats qc pos mats =
     (let instr = instructions qc ! pos;
          arity = gate_arity instr;
          params = gate_params instr;
          new_instrs = to_instructions mats arity params
      in replace_instruction qc pos new_instrs)"


lemma num_qubits_replace_with_mats:
  "num_qubits (replace_with_mats qc pos mats) = num_qubits qc"
  apply (simp add:
      replace_with_mats_def
      to_instructions_def
      replace_instruction_def create_instruction_def)
  by (metis (lifting) quantum_circuit.select_convs(1) quantum_circuit.surjective
      quantum_circuit.update_convs(2))


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

definition replace_with_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "replace_with_choice qc pos seqs choice =
     replace_with_mats qc pos (seqs ! choice)"


lemma num_qubits_replace_with_choice:
  "num_qubits (replace_with_choice qc pos seqs choice) =
     num_qubits qc"
  by (simp add:
      replace_with_choice_def
      num_qubits_replace_with_mats)


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


definition is_valid_choice :: "complex mat list list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_valid_choice seqs choice \<longleftrightarrow> choice < length seqs"


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

definition generate_sequences ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list"
where
  "generate_sequences seq_fun qc pos =
     seq_fun (gate_matrix ((instructions qc) ! pos))"


definition replace_with_generated ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "replace_with_generated seq_fun qc pos choice =
     replace_with_choice qc pos
       (generate_sequences seq_fun qc pos)
       choice"


lemma num_qubits_replace_with_generated:
  "num_qubits (replace_with_generated seq_fun qc pos choice) =
     num_qubits qc"
  by (simp add:
      replace_with_generated_def
      num_qubits_replace_with_choice)


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


definition is_valid_generated_choice ::
  "(complex mat \<Rightarrow> complex mat list list) \<Rightarrow> quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_valid_generated_choice seq_fun qc pos choice \<longleftrightarrow>
     can_replace_at qc pos \<and>
     is_valid_choice (generate_sequences seq_fun qc pos) choice"


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

definition insert_mats ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_mats qc pos mats params =
     insert_instructions qc pos
       (to_instructions mats (length params) params)"


lemma num_qubits_insert_mats:
  "num_qubits (insert_mats qc pos mats params) = num_qubits qc"
  by (simp add:
      insert_mats_def
      num_qubits_insert)


lemma instructions_insert_mats:
  "instructions (insert_mats qc pos mats params) =
     take pos (instructions qc) @
     to_instructions mats (length params) params @
     drop pos (instructions qc)"
  by (simp add:
      insert_mats_def
      instructions_insert)


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


definition insert_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_choice qc pos seqs choice params =
     insert_mats qc pos (seqs ! choice) params"


definition are_valid_params ::
  "quantum_circuit \<Rightarrow> nat list \<Rightarrow> bool"
where
  "are_valid_params qc params \<longleftrightarrow>
     params \<noteq> [] \<and>
     distinct params \<and>
     are_valid_qubits (num_qubits qc) params"


definition is_valid_insert_choice ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "is_valid_insert_choice qc pos seqs choice params \<longleftrightarrow>
     can_insert_at qc pos \<and>
     is_valid_choice seqs choice \<and>
     are_valid_params qc params"


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


definition h :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "h qc q = append_instruction qc (create_instruction H 1 [q])"


definition x :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "x qc q = append_instruction qc (create_instruction X 1 [q])"


definition y :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "y qc q = append_instruction qc (create_instruction Y 1 [q])"


definition z :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "z qc q = append_instruction qc (create_instruction Z 1 [q])"


definition s :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "s qc q = append_instruction qc (create_instruction S 1 [q])"


definition t :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> quantum_circuit" where
  "t qc q = append_instruction qc (create_instruction T 1 [q])"


definition cnot :: "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  quantum_circuit" where
  "cnot qc control target = append_instruction qc (create_instruction CNOT 2 [control, target])"


subsection \<open>Validity Preservation for Gate Constructors\<close>

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

definition cloak ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "cloak qc pos choice =
     replace_with_generated cloak_seq qc pos choice"


definition is_valid_cloak ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_valid_cloak qc pos choice \<longleftrightarrow>
     is_valid_generated_choice cloak_seq qc pos choice"


lemma valid_cloak:
  assumes "is_valid_circuit qc"
  assumes "is_valid_cloak qc pos choice"
  shows "is_valid_circuit (cloak qc pos choice)"
  using assms
  by (simp add:
      cloak_def
      is_valid_cloak_def
      valid_replace_with_generated_if_valid)


lemma valid_cloak_direct:
  assumes "is_valid_circuit qc"
  assumes "pos < length (instructions qc)"
  assumes "choice < length (generate_sequences cloak_seq qc pos)"
  shows "is_valid_circuit (cloak qc pos choice)"
  using assms
  by (simp add:
      cloak_def
      valid_replace_with_generated)


definition delay ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> quantum_circuit"
where
  "delay qc pos choice =
     replace_with_generated delayed_seq qc pos choice"


definition is_valid_delay ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "is_valid_delay qc pos choice \<longleftrightarrow>
     is_valid_generated_choice delayed_seq qc pos choice"


lemma valid_delay:
  assumes "is_valid_circuit qc"
  assumes "is_valid_delay qc pos choice"
  shows "is_valid_circuit (delay qc pos choice)"
  using assms
  by (simp add:
      delay_def
      is_valid_delay_def
      valid_replace_with_generated_if_valid)


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

definition insert_inverse_pair ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> quantum_circuit"
where
  "insert_inverse_pair qc pos choice params =
     insert_choice qc pos inverses choice params"


definition is_valid_inverse_insert ::
  "quantum_circuit \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "is_valid_inverse_insert qc pos choice params \<longleftrightarrow>
     is_valid_insert_choice qc pos inverses choice params"


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

fun apply_step ::
  "quantum_circuit \<Rightarrow> obfuscation_step \<Rightarrow> quantum_circuit"
where
  "apply_step qc (Cloak pos choice) =
     cloak qc pos choice"
| "apply_step qc (Delay pos choice) =
     delay qc pos choice"
| "apply_step qc (InsertInverse pos choice params) =
     insert_inverse_pair qc pos choice params"


fun is_valid_step ::
  "quantum_circuit \<Rightarrow> obfuscation_step \<Rightarrow> bool"
where
  "is_valid_step qc (Cloak pos choice) =
     is_valid_cloak qc pos choice"
| "is_valid_step qc (Delay pos choice) =
     is_valid_delay qc pos choice"
| "is_valid_step qc (InsertInverse pos choice params) =
     is_valid_inverse_insert qc pos choice params"


fun apply_plan ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> quantum_circuit"
where
  "apply_plan qc [] = qc"
| "apply_plan qc (step # steps) =
     apply_plan (apply_step qc step) steps"


fun is_valid_plan ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> bool"
where
  "is_valid_plan qc [] = True"
| "is_valid_plan qc (step # steps) =
     (is_valid_step qc step \<and>
      is_valid_plan (apply_step qc step) steps)"


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

definition obfuscate ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> quantum_circuit"
where
  "obfuscate qc steps = apply_plan qc steps"


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