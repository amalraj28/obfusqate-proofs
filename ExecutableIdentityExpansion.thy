theory ExecutableIdentityExpansion
  imports ExecutableQuantumCircuitBridge
begin

text \<open>
  This conservative first theory implements certified base identities, adjoint,
  and composition. Identity extension, qubit permutation, parameter rotation,
  and transitivity-based expression constructors are intentionally reserved for
  a later theory once their executable circuit operations and denotation laws
  are available.
\<close>

section \<open>Matrix Equivalence up to Global Phase\<close>

definition unit_phase ::
  (*
    """
    Purpose:
      Recognizes complex scalars that represent physically irrelevant global phases.

    Arguments:
      z:
        The complex scalar being checked.

    Conclusion:
      The scalar is accepted exactly when its complex norm is one.
    """
  *)
  "complex \<Rightarrow> bool"
where
  "unit_phase z \<longleftrightarrow> norm z = 1"


definition phase_scale_mat ::
  (*
    """
    Purpose:
      Multiplies every entry of a complex matrix by a complex scalar.

    Arguments:
      z:
        The scalar applied to the matrix.

      A:
        The matrix being scaled.

    Conclusion:
      Returns the matrix obtained by applying the scalar to every entry.
    """
  *)
  "complex \<Rightarrow> complex mat \<Rightarrow> complex mat"
where
  "phase_scale_mat z A = z \<cdot>\<^sub>m A"


lemma phase_scale_mat_one[simp]:
  (*
    """
    Purpose:
      Shows that scaling a complex matrix by one leaves it unchanged.

    Arguments:
      A:
        The matrix being scaled.

    Assumptions:
      None.

    Conclusion:
      Unit scalar multiplication preserves the matrix exactly.
    """
  *)
  "phase_scale_mat 1 A = A"
  by (rule mat_eq_iff[THEN iffD2])
     (auto simp add: phase_scale_mat_def)


lemma phase_scale_mat_mult:
  (*
    """
    Purpose:
      Combines two successive matrix phase scalings into one scaling.

    Arguments:
      z:
        The outer complex scalar.

      w:
        The inner complex scalar.

      A:
        The matrix being scaled.

    Assumptions:
      None.

    Conclusion:
      Successive scaling is equivalent to scaling by the product of the scalars.
    """
  *)
  "phase_scale_mat z (phase_scale_mat w A) =
   phase_scale_mat (z * w) A"
  by (rule mat_eq_iff[THEN iffD2])
     (auto simp add: phase_scale_mat_def algebra_simps)


definition equiv_upto_global_phase ::
  (*
    """
    Purpose:
      Defines equality of complex matrices up to a physically irrelevant global phase.

    Arguments:
      A:
        The first matrix.

      B:
        The second matrix.

    Assumptions:
      None.

    Conclusion:
      The matrices are equivalent when they have equal dimensions and one is a
      unit-phase scalar multiple of the other.
    """
  *)
  "complex mat \<Rightarrow> complex mat \<Rightarrow> bool"
where
  "equiv_upto_global_phase A B \<longleftrightarrow>
     dim_row A = dim_row B \<and>
     dim_col A = dim_col B \<and>
     (\<exists>z. unit_phase z \<and> A = phase_scale_mat z B)"


lemma equiv_upto_global_phase_reflexivity:
  (*
    """
    Purpose:
      Proves reflexivity of matrix equivalence up to global phase.

    Arguments:
      A:
        The matrix compared with itself.

    Assumptions:
      None.

    Conclusion:
      Every complex matrix is phase-equivalent to itself.
    """
  *)
  "equiv_upto_global_phase A A"
  apply (auto simp add: equiv_upto_global_phase_def unit_phase_def)
  using norm_one by fastforce


lemma phase_equiv_mat_sym:
  (*
    """
    Purpose:
      Proves symmetry of matrix equivalence up to global phase.

    Arguments:
      A:
        The first matrix.

      B:
        The second matrix.

    Assumptions:
      The first matrix is phase-equivalent to the second matrix.

    Conclusion:
      The second matrix is phase-equivalent to the first matrix.
    """
  *)
  assumes "equiv_upto_global_phase A B"
  shows "equiv_upto_global_phase B A"
proof -
  obtain z where dims:
      "dim_row A = dim_row B"
      "dim_col A = dim_col B"
    and phase: "unit_phase z"
    and A: "A = phase_scale_mat z B"
    using assms by (auto simp add: equiv_upto_global_phase_def)

  have z_nonzero: "z \<noteq> 0"
    using phase by (auto simp add: unit_phase_def)
  have inv_phase: "unit_phase (inverse z)"
    using phase z_nonzero
    by (simp add: unit_phase_def norm_inverse)
  have B: "B = phase_scale_mat (inverse z) A"
  proof -
    have "phase_scale_mat (inverse z) A =
          phase_scale_mat (inverse z) (phase_scale_mat z B)"
      using A by simp
    also have "... = phase_scale_mat (inverse z * z) B"
      by (rule phase_scale_mat_mult)
    also have "... = B"
      using z_nonzero by simp
    finally show ?thesis by simp
  qed

  show ?thesis
    using dims inv_phase B
    by (auto simp add: equiv_upto_global_phase_def)
qed


lemma equiv_upto_global_phase_transitive:
  (*
    """
    Purpose:
      Proves transitivity of matrix equivalence up to global phase.

    Arguments:
      A:
        The first matrix.

      B:
        The intermediate matrix.

      C:
        The final matrix.

    Assumptions:
      The first matrix is phase-equivalent to the intermediate matrix, and the
      intermediate matrix is phase-equivalent to the final matrix.

    Conclusion:
      The first matrix is phase-equivalent to the final matrix.
    """
  *)
  assumes AB: "equiv_upto_global_phase A B"
  assumes BC: "equiv_upto_global_phase B C"
  shows "equiv_upto_global_phase A C"
proof -
  obtain z where z_phase: "unit_phase z" and A: "A = phase_scale_mat z B"
    using AB by (auto simp add: equiv_upto_global_phase_def)
  obtain w where w_phase: "unit_phase w" and B: "B = phase_scale_mat w C"
    using BC by (auto simp add: equiv_upto_global_phase_def)
  have zw_phase: "unit_phase (z * w)"
    using z_phase w_phase
    by (simp add: unit_phase_def norm_mult)
  have A_C: "A = phase_scale_mat (z * w) C"
    using A B phase_scale_mat_mult[of z w C]
    by simp
  show ?thesis
    using AB BC zw_phase A_C
    by (auto simp add: equiv_upto_global_phase_def)
qed


lemma equal_matrices_are_equivalent:
  (*
    """
    Purpose:
      Lifts exact matrix equality to equivalence up to global phase.

    Arguments:
      A:
        The first matrix.

      B:
        The second matrix.

    Assumptions:
      The matrices are exactly equal.

    Conclusion:
      Exactly equal matrices are also phase-equivalent.
    """
  *)
  assumes "A = B"
  shows "equiv_upto_global_phase A B"
  using assms equiv_upto_global_phase_reflexivity by simp


lemma equiv_upto_global_phase_multiplication:
  (*
    """
    Purpose:
      Proves that compatible left and right matrix multiplication preserves
      equivalence up to global phase.

    Arguments:
      A and B:
        The phase-equivalent middle matrices.

      C:
        The matrix multiplied on the left.

      D:
        The matrix multiplied on the right.

    Assumptions:
      The middle matrices are phase-equivalent, and all matrices have compatible
      carrier dimensions for the two products.

    Conclusion:
      Multiplying both middle matrices by the same surrounding matrices preserves
      their phase equivalence.
    """
  *)
  assumes equiv: "equiv_upto_global_phase A B"
  assumes C_carrier: "C \<in> carrier_mat nr r"
  assumes A_carrier: "A \<in> carrier_mat r c"
  assumes B_carrier: "B \<in> carrier_mat r c"
  assumes D_carrier: "D \<in> carrier_mat c nc"
  shows "equiv_upto_global_phase ((C * A) * D) ((C * B) * D)"
proof -
  obtain z where z_phase: "unit_phase z" and A: "A = phase_scale_mat z B"
    using equiv by (auto simp add: equiv_upto_global_phase_def)
  have CB_carrier: "C * B \<in> carrier_mat nr c"
    using C_carrier B_carrier by simp
  have scaled:
    "(C * A) * D = phase_scale_mat z ((C * B) * D)"
  proof -
    have "(C * A) * D = (C * phase_scale_mat z B) * D"
      using A by simp
    also have "... = phase_scale_mat z (C * B) * D"
      using C_carrier B_carrier
      by (simp add: phase_scale_mat_def mult_smult_distrib)
    also have "... = phase_scale_mat z ((C * B) * D)"
      using CB_carrier D_carrier
      by (simp add: phase_scale_mat_def mult_smult_assoc_mat)
    finally show ?thesis .
  qed
  show ?thesis
    using C_carrier A_carrier B_carrier D_carrier z_phase scaled
    using equiv_upto_global_phase_def phase_scale_mat_def by auto
qed


section \<open>Executable Circuit Phase Equivalence\<close>

context obfuscation_semantics_u3
begin

definition append_circuit_id ::
  (*
    """
    Purpose:
      Concatenates the instruction lists of two executable circuits.

    Arguments:
      left:
        The circuit whose instructions occur first.

      right:
        The circuit whose instructions occur second.

    Assumptions:
      Soundness lemmas require both circuits to use the same qubit count.

    Conclusion:
      Returns a circuit with the left qubit count and both instruction lists in
      execution order.
    """
  *)
  "quantum_circuit_id \<Rightarrow> quantum_circuit_id \<Rightarrow> quantum_circuit_id"
where
  "append_circuit_id left right =
     make_quantum_circuit_id
       (num_qubits_id left)
       (instructions_id left @ instructions_id right)"


definition phase_equiv_circuit ::
  (*
    """
    Purpose:
      Defines executable circuit equivalence up to global phase on a fixed
      number of qubits.

    Arguments:
      n:
        The common number of qubits.

      c1 and c2:
        The executable circuits being compared.

    Assumptions:
      None.

    Conclusion:
      The circuits are equivalent when both use the requested qubit count and
      their matrix denotations differ only by a unit global phase.
    """
  *)
  "nat \<Rightarrow> quantum_circuit_id \<Rightarrow> quantum_circuit_id \<Rightarrow> bool"
where
  "phase_equiv_circuit nq c1 c2 \<longleftrightarrow>
     num_qubits_id c1 = nq \<and>
     num_qubits_id c2 = nq \<and>
     equiv_upto_global_phase
       (eval_circuit (denote_circuit_id c1))
       (eval_circuit (denote_circuit_id c2))"


definition phase_identity_circuit ::
  (*
    """
    Purpose:
      Recognizes executable circuits whose semantics is identity up to global phase.

    Arguments:
      n:
        The number of qubits in the identity circuit.

      c:
        The executable circuit being checked.

    Conclusion:
      The circuit is accepted when it is phase-equivalent to the empty circuit
      on the same number of qubits.
    """
  *)
  "nat \<Rightarrow> quantum_circuit_id \<Rightarrow> bool"
where
  "phase_identity_circuit nq c \<longleftrightarrow>
     phase_equiv_circuit nq c (empty_circuit_id nq)"


lemma phase_equiv_circuit_refl:
  (*
    """
    Purpose:
      Proves reflexivity of executable circuit phase equivalence.

    Arguments:
      n:
        The circuit qubit count.

      c:
        The executable circuit compared with itself.

    Assumptions:
      The circuit uses the requested qubit count.

    Conclusion:
      The circuit is phase-equivalent to itself.
    """
  *)
  assumes "num_qubits_id c = n"
  shows "phase_equiv_circuit n c c"
  using assms equiv_upto_global_phase_reflexivity
  by (simp add: phase_equiv_circuit_def)


lemma equal_circuits_are_equivalent:
  (*
    """
    Purpose:
      Lifts exact executable circuit equality to circuit phase equivalence.

    Arguments:
      n:
        The common circuit qubit count.

      c1 and c2:
        The executable circuits being compared.

    Assumptions:
      The circuits are exactly equal and use the requested qubit count.

    Conclusion:
      The circuits are phase-equivalent.
    """
  *)
  assumes "c1 = c2"
  assumes "num_qubits_id c1 = n"
  shows "phase_equiv_circuit n c1 c2"
  using assms phase_equiv_circuit_refl by simp


lemma valid_append_circuit_id:
  (*
    """
    Purpose:
      Proves that concatenating two compatible valid executable circuits preserves validity.

    Arguments:
      left and right:
        The executable circuits being concatenated.

    Assumptions:
      Both circuits are valid and have the same qubit count.

    Conclusion:
      The concatenated executable circuit is valid.
    """
  *)
  assumes left_valid: "valid_quantum_circuit_id left"
  assumes right_valid: "valid_quantum_circuit_id right"
  assumes same_n: "num_qubits_id right = num_qubits_id left"
  shows "valid_quantum_circuit_id (append_circuit_id left right)"
  using assms
  by (simp add:
      append_circuit_id_def
      make_quantum_circuit_id_def
      valid_quantum_circuit_id_def
     )


lemma eval_denote_circuit_carrier:
  (*
    """
    Purpose:
      Establishes the full-system carrier of a valid executable circuit denotation.

    Arguments:
      c:
        The executable circuit being evaluated.

    Assumptions:
      The executable circuit is structurally valid.

    Conclusion:
      Its evaluated matrix is square with dimension determined by its qubit count.
    """
  *)
  assumes valid: "valid_quantum_circuit_id c"
  shows "eval_circuit (denote_circuit_id c) \<in>
         carrier_mat (2 ^ num_qubits_id c) (2 ^ num_qubits_id c)"
proof -
  have local_carrier: "has_circuit_carrier (denote_circuit_id c)"
    using valid by (rule has_circuit_carrier_denote_circuit_id)
  have placed_carrier:
    "\<forall>M \<in> set
       (eval_instructions
         (num_qubits (denote_circuit_id c))
         (instructions (denote_circuit_id c))).
       M \<in> carrier_mat
         (2 ^ num_qubits (denote_circuit_id c))
         (2 ^ num_qubits (denote_circuit_id c))"
    using local_carrier place_gate_carrier
    by (auto simp add:
        has_circuit_carrier_def
        eval_instructions_def
        eval_instruction_def)
  show ?thesis
    using compose_carrier[OF placed_carrier]
    by (simp add: eval_circuit_def)
qed


lemma eval_append_circuit_id:
  (*
    """
    Purpose:
      Relates executable circuit concatenation to matrix multiplication semantics.

    Arguments:
      left and right:
        The executable circuits being concatenated.

    Assumptions:
      Both circuits are valid and have the same qubit count.

    Conclusion:
      The denotation of the concatenated circuit is the denotation of the right
      circuit multiplied by the denotation of the left circuit, matching the
      repository's established circuit ordering convention.
    """
  *)
  assumes left_valid: "valid_quantum_circuit_id left"
  assumes right_valid: "valid_quantum_circuit_id right"
  assumes same_n: "num_qubits_id right = num_qubits_id left"
  shows
    "eval_circuit (denote_circuit_id (append_circuit_id left right)) =
     eval_circuit (denote_circuit_id right) *
     eval_circuit (denote_circuit_id left)"
proof -
  let ?n = "num_qubits_id left"
  let ?left_mats =
    "eval_instructions ?n (instructions (denote_circuit_id left))"
  let ?right_mats =
    "eval_instructions ?n (instructions (denote_circuit_id right))"

  have left_carrier:
    "\<forall>M \<in> set ?left_mats. M \<in> carrier_mat (2 ^ ?n) (2 ^ ?n)"
    using has_circuit_carrier_denote_circuit_id[OF left_valid]
          place_gate_carrier
    by (auto simp add:
        has_circuit_carrier_def
        eval_instructions_def
        eval_instruction_def)
  have right_carrier:
    "\<forall>M \<in> set ?right_mats. M \<in> carrier_mat (2 ^ ?n) (2 ^ ?n)"
    using has_circuit_carrier_denote_circuit_id[OF right_valid]
          place_gate_carrier same_n
    by (auto simp add:
        has_circuit_carrier_def
        eval_instructions_def
        eval_instruction_def)
  have all_carrier:
    "\<forall>M \<in> set (?left_mats @ ?right_mats).
       M \<in> carrier_mat (2 ^ ?n) (2 ^ ?n)"
    using left_carrier right_carrier by auto
  have composed:
    "compose (?left_mats @ ?right_mats) (2 ^ ?n) =
     compose ?right_mats (2 ^ ?n) * compose ?left_mats (2 ^ ?n)"
    using compose_append[OF all_carrier] .
  show ?thesis
    using same_n composed
    by (simp add:
        append_circuit_id_def
        make_quantum_circuit_id_def
        denote_circuit_id_def
        create_circuit_def
        eval_circuit_def
        eval_instructions_append)
qed


lemma phase_identity_append:
  (*
    """
    Purpose:
      Proves closure of certified phase identities under circuit composition.

    Arguments:
      n:
        The common number of qubits.

      first and second:
        The phase-identity circuits being concatenated.

    Assumptions:
      Both circuits are valid phase identities on the same number of qubits.

    Conclusion:
      Their concatenation is also a valid phase identity.
    """
  *)
  assumes first_valid: "valid_quantum_circuit_id first"
  assumes second_valid: "valid_quantum_circuit_id second"
  assumes first_id: "phase_identity_circuit n first"
  assumes second_id: "phase_identity_circuit n second"
  shows
    "valid_quantum_circuit_id (append_circuit_id first second) \<and>
     phase_identity_circuit n (append_circuit_id first second)"
proof -
  have first_n: "num_qubits_id first = n"
    using first_id
    by (simp add: phase_identity_circuit_def phase_equiv_circuit_def)
  have second_n: "num_qubits_id second = n"
    using second_id
    by (simp add: phase_identity_circuit_def phase_equiv_circuit_def)
  have append_valid: "valid_quantum_circuit_id (append_circuit_id first second)"
    using first_valid second_valid first_n second_n
    by (simp add: valid_append_circuit_id)
  have first_equiv:
    "equiv_upto_global_phase
       (eval_circuit (denote_circuit_id first))
       (eval_circuit (denote_circuit_id (empty_circuit_id n)))"
    using first_id
    by (simp add: phase_identity_circuit_def phase_equiv_circuit_def)
  have second_equiv:
    "equiv_upto_global_phase
       (eval_circuit (denote_circuit_id second))
       (eval_circuit (denote_circuit_id (empty_circuit_id n)))"
    using second_id
    by (simp add: phase_identity_circuit_def phase_equiv_circuit_def)
  have first_carrier:
    "eval_circuit (denote_circuit_id first) \<in>
       carrier_mat (2 ^ n) (2 ^ n)"
    using eval_denote_circuit_carrier[OF first_valid] first_n by simp
  have second_carrier:
    "eval_circuit (denote_circuit_id second) \<in>
       carrier_mat (2 ^ n) (2 ^ n)"
    using eval_denote_circuit_carrier[OF second_valid] second_n by simp
  have empty_carrier:
    "eval_circuit (denote_circuit_id (empty_circuit_id n)) \<in>
       carrier_mat (2 ^ n) (2 ^ n)"
    using eval_denote_circuit_carrier[OF valid_empty_circuit_id]
    by (metis phase_equiv_circuit_def phase_identity_circuit_def second_id)
  have one_carrier:
    "1\<^sub>m (2 ^ n) \<in> carrier_mat (2 ^ n) (2 ^ n)"
    by simp
  have first_surrounded:
    "equiv_upto_global_phase
       ((eval_circuit (denote_circuit_id second) *
         eval_circuit (denote_circuit_id first)) * 1\<^sub>m (2 ^ n))
       ((eval_circuit (denote_circuit_id second) *
         eval_circuit (denote_circuit_id (empty_circuit_id n))) * 1\<^sub>m (2 ^ n))"
    using equiv_upto_global_phase_multiplication[OF first_equiv
      second_carrier first_carrier empty_carrier one_carrier] .
  have second_surrounded:
    "equiv_upto_global_phase
       ((1\<^sub>m (2 ^ n) * eval_circuit (denote_circuit_id second)) *
         eval_circuit (denote_circuit_id (empty_circuit_id n)))
       ((1\<^sub>m (2 ^ n) * eval_circuit (denote_circuit_id (empty_circuit_id n))) *
         eval_circuit (denote_circuit_id (empty_circuit_id n)))"
    using equiv_upto_global_phase_multiplication[OF second_equiv
      one_carrier second_carrier empty_carrier empty_carrier] .
  have first_product:
    "equiv_upto_global_phase
       (eval_circuit (denote_circuit_id second) *
        eval_circuit (denote_circuit_id first))
       (eval_circuit (denote_circuit_id second) *
        eval_circuit (denote_circuit_id (empty_circuit_id n)))"
    using first_surrounded second_carrier first_carrier empty_carrier
    by simp
  have second_product:
    "equiv_upto_global_phase
       (eval_circuit (denote_circuit_id second) *
        eval_circuit (denote_circuit_id (empty_circuit_id n)))
       (eval_circuit (denote_circuit_id (empty_circuit_id n)) *
        eval_circuit (denote_circuit_id (empty_circuit_id n)))"
    using second_surrounded second_carrier empty_carrier
    by simp
  have empty_sem:
    "eval_circuit (denote_circuit_id (empty_circuit_id n)) =
     1\<^sub>m (2 ^ n)"
    by (simp add:
        eval_circuit_def empty_circuit_id_def make_quantum_circuit_id_def
        denote_circuit_id_def create_circuit_def eval_instructions_def)
  have product_to_double_empty:
    "equiv_upto_global_phase
       (eval_circuit (denote_circuit_id second) *
        eval_circuit (denote_circuit_id first))
       (eval_circuit (denote_circuit_id (empty_circuit_id n)) *
        eval_circuit (denote_circuit_id (empty_circuit_id n)))"
    using first_product second_product
    by (rule equiv_upto_global_phase_transitive)
  have product_equiv:
    "equiv_upto_global_phase
       (eval_circuit (denote_circuit_id second) *
        eval_circuit (denote_circuit_id first))
       (eval_circuit (denote_circuit_id (empty_circuit_id n)))"
    using product_to_double_empty empty_carrier empty_sem
    by simp
  have append_sem:
    "eval_circuit (denote_circuit_id (append_circuit_id first second)) =
     eval_circuit (denote_circuit_id second) *
     eval_circuit (denote_circuit_id first)"
    using first_valid second_valid first_n second_n
    by (simp add: eval_append_circuit_id)
  have append_n: "num_qubits_id (append_circuit_id first second) = n"
    using first_n by (simp add: append_circuit_id_def make_quantum_circuit_id_def)
  show ?thesis
    using append_valid append_n product_equiv append_sem  phase_equiv_circuit_def phase_identity_circuit_def second_id
    by auto
qed


lemma phase_identity_insertion:
  (*
    """
    Purpose:
      Proves semantic soundness of inserting a certified phase identity between
      an executable prefix and suffix.

    Arguments:
      n:
        The common number of qubits.

      prefix:
        The circuit fragment executed before the inserted identity.

      identity_seq:
        The certified identity circuit being inserted.

      suffix:
        The circuit fragment executed after the inserted identity.

    Assumptions:
      All three circuits are valid on the same number of qubits, and the inserted
      circuit is an identity up to global phase.

    Conclusion:
      Inserting the certified identity preserves the complete circuit up to
      global phase.
    """
  *)
  assumes prefix_valid: "valid_quantum_circuit_id prefix"
  assumes identity_valid: "valid_quantum_circuit_id identity_seq"
  assumes suffix_valid: "valid_quantum_circuit_id suffix"
  assumes prefix_n: "num_qubits_id prefix = n"
  assumes identity_n: "num_qubits_id identity_seq = n"
  assumes suffix_n: "num_qubits_id suffix = n"
  assumes identity: "phase_identity_circuit n identity_seq"
  shows
    "phase_equiv_circuit n
       (append_circuit_id (append_circuit_id prefix identity_seq) suffix)
       (append_circuit_id prefix suffix)"
proof -
  let ?P = "eval_circuit (denote_circuit_id prefix)"
  let ?I = "eval_circuit (denote_circuit_id identity_seq)"
  let ?S = "eval_circuit (denote_circuit_id suffix)"
  let ?E = "eval_circuit (denote_circuit_id (empty_circuit_id n))"

  have P_carrier: "?P \<in> carrier_mat (2 ^ n) (2 ^ n)"
    using eval_denote_circuit_carrier[OF prefix_valid] prefix_n by simp
  have I_carrier: "?I \<in> carrier_mat (2 ^ n) (2 ^ n)"
    using eval_denote_circuit_carrier[OF identity_valid] identity_n by simp
  have S_carrier: "?S \<in> carrier_mat (2 ^ n) (2 ^ n)"
    using eval_denote_circuit_carrier[OF suffix_valid] suffix_n by simp
  have E_carrier: "?E \<in> carrier_mat (2 ^ n) (2 ^ n)"
    using eval_denote_circuit_carrier[OF valid_empty_circuit_id]
    by (metis identity phase_equiv_circuit_def phase_identity_circuit_def)
  have I_equiv: "equiv_upto_global_phase ?I ?E"
    using identity
    by (simp add: phase_identity_circuit_def phase_equiv_circuit_def)
  have surrounded: "equiv_upto_global_phase ((?S * ?I) * ?P) ((?S * ?E) * ?P)"
    using equiv_upto_global_phase_multiplication[OF I_equiv
      S_carrier I_carrier E_carrier P_carrier] .
  have empty_sem: "?E = 1\<^sub>m (2 ^ n)"
    by (simp add:
        eval_circuit_def empty_circuit_id_def make_quantum_circuit_id_def
        denote_circuit_id_def create_circuit_def eval_instructions_def)
  have matrix_equiv: "equiv_upto_global_phase ((?S * ?I) * ?P) (?S * ?P)"
    using surrounded P_carrier S_carrier empty_sem
    by simp
  have prefix_identity_valid:
    "valid_quantum_circuit_id (append_circuit_id prefix identity_seq)"
    using prefix_valid identity_valid prefix_n identity_n
    by (simp add: valid_append_circuit_id)
  have inserted_sem:
    "eval_circuit
       (denote_circuit_id
         (append_circuit_id (append_circuit_id prefix identity_seq) suffix)) =
     (?S * ?I) * ?P"
    using eval_append_circuit_id[OF prefix_valid identity_valid]
          eval_append_circuit_id[OF prefix_identity_valid suffix_valid]
          prefix_n identity_n suffix_n P_carrier I_carrier S_carrier
    by (simp add: append_circuit_id_def make_quantum_circuit_id_def)
  have original_sem:
    "eval_circuit (denote_circuit_id (append_circuit_id prefix suffix)) =
     ?S * ?P"
    using eval_append_circuit_id[OF prefix_valid suffix_valid] prefix_n suffix_n
    by simp
  show ?thesis
    using prefix_n inserted_sem original_sem matrix_equiv
    by (simp add:
        phase_equiv_circuit_def append_circuit_id_def
        make_quantum_circuit_id_def)
qed

end


section \<open>Certified Identity Expressions\<close>

datatype identity_expr =
  (*
    """
    Purpose:
      Represents identities generated from a finite certified basis by the safe
      closure rules supported in the first implementation.

    Arguments:
      Base:
        References one circuit in the certified identity basis.

      Adjoint:
        Applies the separately certified executable adjoint operation.

      Compose:
        Concatenates two generated identity expressions.

    Assumptions:
      Index validity and basis certification are checked separately.

    Conclusion:
      Provides a finite syntax for base, adjoint, and composition identity generation.
    """
  *)
    Base nat
  | Adjoint identity_expr
  | Compose identity_expr identity_expr


context obfuscation_semantics_u3
begin

fun valid_identity_expr ::
  (*
    """
    Purpose:
      Checks that every base reference in a generated identity expression is in bounds.

    Arguments:
      basis_size:
        The number of certified base identity circuits available.

      expr:
        The identity expression being checked.

    Assumptions:
      None.

    Conclusion:
      The expression is valid exactly when all recursively referenced base indices
      are available.
    """
  *)
  "nat \<Rightarrow> identity_expr \<Rightarrow> bool"
where
  "valid_identity_expr basis_size (Base i) = (i < basis_size)"
| "valid_identity_expr basis_size (Adjoint expr) =
     valid_identity_expr basis_size expr"
| "valid_identity_expr basis_size (Compose left right) =
     (valid_identity_expr basis_size left \<and>
      valid_identity_expr basis_size right)"


definition valid_identity_basis ::
  (*
    """
    Purpose:
      Certifies a list of executable circuits as a basis of phase identities.

    Arguments:
      n:
        The common number of qubits.

      basis:
        The executable circuits used as base identities.

    Assumptions:
      None.

    Conclusion:
      The basis is valid when every circuit is structurally valid and denotes an
      identity up to global phase on the requested qubit count.
    """
  *)
  "nat \<Rightarrow> quantum_circuit_id list \<Rightarrow> bool"
where
  "valid_identity_basis nq basis \<longleftrightarrow>
     list_all
       (\<lambda>c. valid_quantum_circuit_id c \<and>
            phase_identity_circuit nq c)
       basis"


end


locale certified_equational_identity_expansion =
  (*
    """
    Purpose:
      Isolates the additional contract required to use executable circuit
      adjoints in certified identity generation.

    Arguments:
      adjoint_circuit_id:
        The executable operation used to construct the adjoint of a circuit.

    Assumptions:
      The operation preserves executable validity and maps phase identities to
      phase identities.

    Conclusion:
      Base, adjoint, and composition expressions can be evaluated and proved sound.
    """
  *)
  obfuscation_semantics_u3 +
  fixes adjoint_circuit_id :: "quantum_circuit_id \<Rightarrow> quantum_circuit_id"
  assumes adjoint_circuit_id_valid:
    "valid_quantum_circuit_id c \<Longrightarrow>
     valid_quantum_circuit_id (adjoint_circuit_id c)"
  assumes adjoint_circuit_id_phase_identity:
    "phase_identity_circuit n c \<Longrightarrow>
     phase_identity_circuit n (adjoint_circuit_id c)"
begin

fun eval_identity_expr ::
  (*
    """
    Purpose:
      Evaluates a certified identity expression into an executable circuit.

    Arguments:
      n:
        The qubit count used by the empty fallback circuit.

      basis:
        The list of certified executable base identities.

      expr:
        The expression generated from base, adjoint, and composition rules.

    Assumptions:
      Soundness requires a valid basis, valid indices, and the locale's certified
      executable adjoint operation.

    Conclusion:
      Returns the executable circuit represented by the identity expression.
    """
  *)
  "nat \<Rightarrow> quantum_circuit_id list \<Rightarrow> identity_expr \<Rightarrow>
   quantum_circuit_id"
where
  "eval_identity_expr qbit_count basis (Base i) =
     (if i < length basis then basis ! i else empty_circuit_id qbit_count)"
| "eval_identity_expr qbit_count basis (Adjoint expr) =
     adjoint_circuit_id (eval_identity_expr qbit_count basis expr)"
| "eval_identity_expr qbit_count basis (Compose left right) =
     append_circuit_id
       (eval_identity_expr qbit_count basis left)
       (eval_identity_expr qbit_count basis right)"


theorem eval_identity_expr_sound:
  (*
    """
    Purpose:
      Proves soundness of identities generated from certified base identities by
      adjoint and composition.

    Arguments:
      n:
        The common number of qubits.

      basis:
        The certified executable identity basis.

      expr:
        The well-formed generated identity expression.

    Assumptions:
      Every basis circuit is a valid phase identity, every base index is in
      bounds, and the locale's executable adjoint operation preserves validity
      and phase identity.

    Conclusion:
      The evaluated expression is a structurally valid executable circuit and an
      identity up to global phase.
    """
  *)
  assumes basis_valid: "valid_identity_basis n basis"
  assumes expr_valid: "valid_identity_expr (length basis) expr"
  shows
    "valid_quantum_circuit_id (eval_identity_expr n basis expr) \<and>
     phase_identity_circuit n (eval_identity_expr n basis expr)"
  using expr_valid
proof (induction expr)
  case (Base i)
  then have i_lt: "i < length basis" by simp
  have member:
    "valid_quantum_circuit_id (basis ! i) \<and>
     phase_identity_circuit n (basis ! i)"
    using basis_valid i_lt
    by (auto simp add: valid_identity_basis_def list_all_iff)
  show ?case
    using i_lt member by simp
next
  case (Adjoint expr)
  then have source:
    "valid_quantum_circuit_id (eval_identity_expr n basis expr) \<and>
     phase_identity_circuit n (eval_identity_expr n basis expr)"
    by simp
  show ?case
    using source adjoint_circuit_id_valid adjoint_circuit_id_phase_identity
    by simp
next
  case (Compose left right)
  then have left:
    "valid_quantum_circuit_id (eval_identity_expr n basis left) \<and>
     phase_identity_circuit n (eval_identity_expr n basis left)"
    by simp
  from Compose have right:
    "valid_quantum_circuit_id (eval_identity_expr n basis right) \<and>
     phase_identity_circuit n (eval_identity_expr n basis right)"
    by simp
  show ?case
    by (simp add: left phase_identity_append right)
qed


theorem generated_identity_insertion_sound:
  (*
    """
    Purpose:
      Connects certified identity generation to semantics-preserving circuit insertion.

    Arguments:
      n:
        The common number of qubits.

      basis and expr:
        The certified basis and well-formed generated identity expression.

      prefix and suffix:
        The executable circuit fragments surrounding the insertion point.

    Assumptions:
      The basis and expression are certified, and the surrounding circuit
      fragments are valid on the same number of qubits.

    Conclusion:
      Inserting the generated identity between the surrounding fragments
      preserves the complete executable circuit up to global phase.
    """
  *)
  assumes basis_valid: "valid_identity_basis n basis"
  assumes expr_valid: "valid_identity_expr (length basis) expr"
  assumes prefix_valid: "valid_quantum_circuit_id prefix"
  assumes suffix_valid: "valid_quantum_circuit_id suffix"
  assumes prefix_n: "num_qubits_id prefix = n"
  assumes suffix_n: "num_qubits_id suffix = n"
  shows
    "phase_equiv_circuit n
       (append_circuit_id
         (append_circuit_id prefix (eval_identity_expr n basis expr))
         suffix)
       (append_circuit_id prefix suffix)"
proof -
  have generated:
    "valid_quantum_circuit_id (eval_identity_expr n basis expr) \<and>
     phase_identity_circuit n (eval_identity_expr n basis expr)"
    using basis_valid expr_valid by (rule eval_identity_expr_sound)
  have generated_n:
    "num_qubits_id (eval_identity_expr n basis expr) = n"
    using generated phase_equiv_circuit_def phase_identity_circuit_def by auto
  show ?thesis
    by (simp add: generated generated_n phase_identity_insertion prefix_n prefix_valid
        suffix_n suffix_valid)
qed

end
end
