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
  "nat \<Rightarrow> instruction \<Rightarrow> complex mat"
where
  "eval_instruction n instr =
     place_gate n (gate_matrix instr) (gate_params instr)"


definition eval_instructions ::
  "nat \<Rightarrow> instruction list \<Rightarrow> complex mat list"
where
  "eval_instructions n instrs =
     map (eval_instruction n) instrs"


definition eval_circuit ::
  "quantum_circuit \<Rightarrow> complex mat"
where
  "eval_circuit qc =
     compose
       (eval_instructions (num_qubits qc) (instructions qc))
       (2 ^ num_qubits qc)"


lemma eval_instructions_append:
  "eval_instructions n (xs @ ys) =
   eval_instructions n xs @ eval_instructions n ys"
  by (simp add: eval_instructions_def)


lemma eval_instructions_take:
  "eval_instructions n (take k xs) =
   take k (eval_instructions n xs)"
  by (simp add: eval_instructions_def take_map)


lemma eval_instructions_drop:
  "eval_instructions n (drop k xs) =
   drop k (eval_instructions n xs)"
  by (simp add: eval_instructions_def drop_map)


lemma eval_to_instructions:
  "eval_instructions n (to_instructions mats arity params) =
   map (\<lambda>G. place_gate n G params) mats"
  by (simp add:
      eval_instructions_def
      eval_instruction_def
      to_instructions_def
      create_instruction_def)


section \<open>Replacement and Insertion Shapes\<close>

lemma eval_replace_mats:
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
  assumes "\<forall>G \<in> set mats. G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"
  shows "\<forall>G \<in> set (map (\<lambda>G. place_gate n G params) mats).
           G \<in> carrier_mat (2 ^ n) (2 ^ n)"
  using assms
  by (auto simp add: place_gate_carrier)


lemma carrier_eval_instructions:
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
  gate_placement + gate
begin

lemma eval_cloak:
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


section \<open>Preservation from Sequence Correctness\<close>

lemma preserve_cloak_seq:
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
  "quantum_circuit \<Rightarrow> bool"
where
  "has_circuit_carrier qc \<longleftrightarrow>
     (\<forall>instr \<in> set (instructions qc).
        gate_matrix instr \<in> carrier_mat
          (2 ^ length (gate_params instr))
          (2 ^ length (gate_params instr)))"


definition has_sequence_carrier ::
  "complex mat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
where
  "has_sequence_carrier seqs choice params \<longleftrightarrow>
     (\<forall>G \<in> set (seqs ! choice).
        G \<in> carrier_mat (2 ^ length params) (2 ^ length params))"


fun is_semantic_step ::
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
      


lemma preserve_step:
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

qed


fun is_semantic_plan ::
  "quantum_circuit \<Rightarrow> obfuscation_step list \<Rightarrow> bool"
where
  "is_semantic_plan qc [] = True"
| "is_semantic_plan qc (step # steps) =
     (is_semantic_step qc step \<and>
      is_semantic_plan (apply_step qc step) steps)"


lemma preserve_plan:
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
  assumes "is_semantic_plan qc steps"
  shows "eval_circuit (obfuscate qc steps) = eval_circuit qc"
  using assms
  by (simp add:
      obfuscate_def
      preserve_plan)

end

end
