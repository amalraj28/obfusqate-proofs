theory U3BasisTransformation
  imports QuantumCircuitSemantics
begin

section \<open>Concrete U3 Basis Transformation\<close>

definition U3 ::
  (*
    """
    Builds the standard single-qubit U3 matrix.

    The matrix is written using real sine and cosine values coerced into complex
    numbers. This avoids ambiguity between real and complex trigonometric
    functions during later entrywise matrix proofs.

    args:
      theta:
        The rotation angle controlling the sine and cosine amplitudes.

      phi:
        The phase applied to the lower-left entry.

      lambda:
        The phase applied to the upper-right entry and combined with phi in the
        lower-right entry.

    returns:
      The two-by-two complex matrix for the U3 gate.
    """
  *)
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex mat"
where
  "U3 theta phi lambda =
     mat_of_cols_list 2
       [[complex_of_real (cos (theta / 2)),
         exp (\<i> * complex_of_real phi) * complex_of_real (sin (theta / 2))],
        [- exp (\<i> * complex_of_real lambda) * complex_of_real (sin (theta / 2)),
         exp (\<i> * complex_of_real (phi + lambda)) *
           complex_of_real (cos (theta / 2))]]"


definition U3_inv ::
  (*
    """
    Builds the inverse basis matrix for U3.

    args:
      theta:
        The rotation angle used by the U3 matrix being inverted.

      phi:
        The phi phase used by the U3 matrix being inverted.

      lambda:
        The lambda phase used by the U3 matrix being inverted.

    returns:
      The explicit two-by-two inverse matrix for the supplied U3 parameters.
    """
  *)
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex mat"
where
  "U3_inv theta phi lambda =
     mat_of_cols_list 2
       [[complex_of_real (cos (theta / 2)),
         - exp (- \<i> * complex_of_real lambda) *
             complex_of_real (sin (theta / 2))],
        [exp (- \<i> * complex_of_real phi) *
             complex_of_real (sin (theta / 2)),
         exp (- \<i> * complex_of_real (phi + lambda)) *
             complex_of_real (cos (theta / 2))]]"

lemma U3_is_carrier_mat[simp]:
  (*
    """
    Proves that every U3 matrix has the expected two-by-two carrier.

    args:
      theta:
        The rotation angle of the U3 matrix.

      phi:
        The phi phase of the U3 matrix.

      lambda:
        The lambda phase of the U3 matrix.

    conclusion:
      The U3 matrix is a two-row, two-column complex matrix.
    """
  *)
  "U3 theta phi lambda \<in> carrier_mat 2 2"
  using carrier_mat_def
  apply (simp add: U3_def mat_of_cols_list_def)
  by (simp add: numeral_2_eq_2)


lemma U3_dim_row[simp]:
  (*
    """
    Computes the row dimension of a U3 matrix.

    args:
      theta:
        The rotation angle of the U3 matrix.

      phi:
        The phi phase of the U3 matrix.

      lambda:
        The lambda phase of the U3 matrix.

    conclusion:
      The U3 matrix has two rows.
    """
  *)
  "dim_row (U3 theta phi lambda) = 2"
  by (simp add: U3_def mat_of_cols_list_def)

lemma U3_dim_col[simp]:
  (*
    """
    Computes the column dimension of a U3 matrix.

    args:
      theta:
        The rotation angle of the U3 matrix.

      phi:
        The phi phase of the U3 matrix.

      lambda:
        The lambda phase of the U3 matrix.

    conclusion:
      The U3 matrix has two columns.
    """
  *)
  "dim_col (U3 theta phi lambda) = 2"
  by (simp add: U3_def mat_of_cols_list_def)


lemma U3_inv_is_carrier_mat[simp]:
  (*
    """
    Proves that every U3 inverse matrix has the expected two-by-two carrier.

    The inverse is the Hermitian conjugate of U3, so it has the same single-qubit carrier dimensions.

    args:
      theta:
        The rotation angle of the U3 inverse.

      phi:
        The phi phase of the U3 inverse.

      lambda:
        The lambda phase of the U3 inverse.

    conclusion:
      The U3 inverse matrix is a two-row, two-column complex matrix.
    """
  *)
  "U3_inv theta phi lambda \<in> carrier_mat 2 2"
  using carrier_mat_def
  by (simp add:
      U3_inv_def
      mat_of_cols_list_def
      numeral_2_eq_2)

lemma U3_inv_dim_row[simp]:
  (*
    """
    Computes the row dimension of a U3 inverse matrix.

    args:
      theta:
        The rotation angle of the U3 inverse.

      phi:
        The phi phase of the U3 inverse.

      lambda:
        The lambda phase of the U3 inverse.

    assumptions:
      None.

    conclusion:
      The U3 inverse matrix has two rows.
    """
  *)
  "dim_row (U3_inv theta phi lambda) = 2"
  using U3_inv_is_carrier_mat by blast


lemma U3_inv_dim_col[simp]:
  (*
    """
    Computes the column dimension of a U3 inverse matrix.

    args:
      theta:
        The rotation angle of the U3 inverse.

      phi:
        The phi phase of the U3 inverse.

      lambda:
        The lambda phase of the U3 inverse.

    conclusion:
      The U3 inverse matrix has two columns.
    """
  *)
  "dim_col (U3_inv theta phi lambda) = 2"
  using U3_inv_is_carrier_mat by blast


lemma unit_phase_left_cancel[simp]:
  (*
    """
    Cancels a unit complex phase followed by its inverse phase.

    This helper is used when expanding products of U3 entries in the inverse proofs.

    args:
      x:
        The real phase angle.

    conclusion:
      The product of exp(-i x) and exp(i x) is one.
    """
  *)
  fixes x :: real
  shows "exp (- (\<i> * x)) * exp (\<i> * x) = 1"
  by (simp add: exp_minus')


lemma unit_phase_shift_cancel[simp]:
  (*
    """
    Cancels the shared phase in a shifted exponential product.

    This helper simplifies off-diagonal U3 products where a conjugated phi phase meets a combined phi-plus-lambda phase.

    args:
      x:
        The phase that is cancelled.

      y:
        The remaining phase after cancellation.

    conclusion:
      Multiplying exp(-i x) by exp(i (x + y)) leaves exp(i y).
    """
  *)
  fixes x y :: real
  shows "exp (- (\<i> * x)) * exp (\<i> * (x + y)) = exp (\<i> * y)"
  by (simp add: mult_exp_exp algebra_simps)


lemma unit_phase_shift_cancel_right[simp]:
  (*
    """
    Cancels the shared phase in the opposite shifted exponential product.

    This helper simplifies off-diagonal U3 products where a combined phase is multiplied by a conjugated lambda phase.

    args:
      x:
        The remaining phase after cancellation.

      y:
        The phase that is cancelled.

    conclusion:
      Multiplying exp(i (x + y)) by exp(-i y) leaves exp(i x).
    """
  *)
  fixes x y :: real
  shows "exp (\<i> * (x + y)) * exp (- (\<i> * y)) = exp (\<i> * x)"
  by (simp add: mult_exp_exp algebra_simps)

lemma sin_squared_plus_cos_squared:
  (*
    """
    Lifts the real sine-cosine square identity into complex arithmetic.

    args:
      x:
        The real angle whose sine and cosine terms are being combined.

    conclusion:
      The complex sum cos(x) * cos(x) + sin(x) * sin(x) is one.
    """
  *)
  fixes x :: real
  shows "complex_of_real (cos x) * complex_of_real (cos x) +
         complex_of_real (sin x) * complex_of_real (sin x) = 1"
  by (metis of_real_add of_real_hom.hom_one of_real_mult sin_cos_squared_add3)


lemma U3_inv_left_inverse:
  (*
    """
    Proves that the U3 inverse is a left inverse of U3.

    The proof expands both two-by-two matrices entrywise, unfolds the explicit
    inverse matrix, cancels matching unit phases, and uses the sine-cosine
    square identity for the diagonal entries.

    args:
      theta:
        The rotation angle of the U3 matrix.

      phi:
        The phi phase of the U3 matrix.

      lambda:
        The lambda phase of the U3 matrix.

    conclusion:
      Multiplying U3_inv by U3 gives the two-by-two identity matrix.
    """
  *)
  "U3_inv theta phi lambda * U3 theta phi lambda = 1\<^sub>m 2"
proof
  fix i j
  assume a0: "i < dim_row (1\<^sub>m 2)"
    and a1: "j < dim_col (1\<^sub>m 2)"

  then have ij: "i \<in> {0, 1} \<and> j \<in> {0, 1}"
    by auto

  show "(U3_inv theta phi lambda * U3 theta phi lambda) $$ (i, j) =
        1\<^sub>m 2 $$ (i, j)"
    using ij sin_squared_plus_cos_squared[of "theta / 2"]
    apply (auto simp add:
        U3_def
        U3_inv_def
        mat_of_cols_list_def
        set_2
        mult_exp_exp
        algebra_simps)
    apply (simp add: vector_space_over_itself.scale_scale exp_minus_inverse)
    by (simp add: exp_minus')
    
next
  show "dim_row (U3_inv theta phi lambda * U3 theta phi lambda) =
        dim_row (1\<^sub>m 2)"
    by simp
next
  show "dim_col (U3_inv theta phi lambda * U3 theta phi lambda) =
        dim_col (1\<^sub>m 2)"
    by simp
qed


lemma U3_inv_right_inverse:
  (*
    """
    Proves that the U3 inverse is a right inverse of U3.

    The proof expands both two-by-two matrices entrywise, unfolds the explicit
    inverse matrix, cancels matching unit phases, and uses the sine-cosine
    square identity for the diagonal entries.

    args:
      theta:
        The rotation angle of the U3 matrix.

      phi:
        The phi phase of the U3 matrix.

      lambda:
        The lambda phase of the U3 matrix.

    conclusion:
      Multiplying U3 by U3_inv gives the two-by-two identity matrix.
    """
  *)
  "U3 theta phi lambda * U3_inv theta phi lambda = 1\<^sub>m 2"
proof
  fix i j
  assume a0: "i < dim_row (1\<^sub>m 2)"
    and a1: "j < dim_col (1\<^sub>m 2)"

  then have ij: "i \<in> {0, 1} \<and> j \<in> {0, 1}"
    by auto

  show "(U3 theta phi lambda * U3_inv theta phi lambda) $$ (i, j) =
        1\<^sub>m 2 $$ (i, j)"
    using ij sin_squared_plus_cos_squared[of "theta / 2"]
    apply (auto simp add:
        U3_def
        U3_inv_def
        mat_of_cols_list_def
        set_2
        mult_exp_exp
        algebra_simps)
    apply (simp add: vector_space_over_itself.scale_scale exp_minus)
    by (simp add: exp_minus')
next
  show "dim_row (U3 theta phi lambda * U3_inv theta phi lambda) =
        dim_row (1\<^sub>m 2)"
    by simp
next
  show "dim_col (U3 theta phi lambda * U3_inv theta phi lambda) =
        dim_col (1\<^sub>m 2)"
    by simp
qed


context obfuscation_semantics
begin

lemma U3_global_basis_sequence_correct:
  (*
    """
    Instantiates the abstract global basis correctness theorem with the concrete U3 basis.

    The global sequence uses the existing ordering convention [B, B * G * Binv, Binv] with B set to U3 and Binv set to its inverse.

    args:
      theta:
        The rotation angle of the U3 basis matrix.

      phi:
        The phi phase of the U3 basis matrix.

      lambda:
        The lambda phase of the U3 basis matrix.

      G:
        The single-qubit gate being represented through the U3 global basis sequence.

    assumptions:
      The gate being transformed is a two-by-two matrix.

    conclusion:
      Composing the U3 global basis sequence returns the original gate.
    """
  *)
  assumes G_carrier: "G \<in> carrier_mat 2 2"
  shows "compose (global_basis_sequence
          (U3 theta phi lambda) (U3_inv theta phi lambda) G) 2 = G"
  using U3_is_carrier_mat U3_inv_is_carrier_mat G_carrier U3_inv_left_inverse U3_inv_right_inverse
  by (rule global_basis_sequence_correct)

lemma U3_selective_basis_sequence_correct:
  (*
    """
    Instantiates the abstract selective basis correctness theorem with the concrete U3 basis.

    The selective sequence uses the existing ordering convention [Binv, Binv * G * B, B] with B set to U3 and Binv set to its inverse.

    args:
      theta:
        The rotation angle of the U3 basis matrix.

      phi:
        The phi phase of the U3 basis matrix.

      lambda:
        The lambda phase of the U3 basis matrix.

      G:
        The single-qubit gate being represented through the U3 selective basis sequence.

    assumptions:
      The gate being transformed is a two-by-two matrix.

    conclusion:
      Composing the U3 selective basis sequence returns the original gate.
    """
  *)
  assumes G_carrier: "G \<in> carrier_mat 2 2"
  shows "compose (selective_basis_sequence
          (U3 theta phi lambda) (U3_inv theta phi lambda) G) 2 = G"
  using U3_is_carrier_mat U3_inv_is_carrier_mat G_carrier
        U3_inv_left_inverse U3_inv_right_inverse
  by (rule selective_basis_sequence_correct)

lemma preserve_U3_global_basis:
  (*
    """
    Proves circuit-level semantic preservation for applying the U3 global basis transform to one single-qubit instruction.

    This theorem specializes the abstract preservation result by supplying the concrete U3 matrix and its proven inverse laws.

    args:
      qc:
        The matrix-based quantum circuit being transformed.

      pos:
        The instruction position selected for basis transformation.

      theta:
        The rotation angle of the U3 basis matrix.

      phi:
        The phi phase of the U3 basis matrix.

      lambda:
        The lambda phase of the U3 basis matrix.

    assumptions:
      The selected position is inside the circuit.

      Every original instruction has a gate matrix with the dimensions implied by its qubit parameters.

      The selected instruction acts on exactly one qubit.

    conclusion:
      Evaluating the circuit after U3 global basis transformation gives the same matrix as evaluating the original circuit.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes one_qubit:
    "length (gate_params ((instructions qc) ! pos)) = 1"
  shows "eval_circuit
          (apply_global_basis qc pos
            (U3 theta phi lambda) (U3_inv theta phi lambda)) =
         eval_circuit qc"
proof (rule preserve_global_basis)
  show "pos < length (instructions qc)"
    using pos_lt .
next
  show "\<forall>instr\<in>set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
    using qc_carrier .
next
  show "U3 theta phi lambda \<in>
       carrier_mat (2 ^ length (gate_params (instructions qc ! pos)))
                   (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit by simp
next
  show "U3_inv theta phi lambda \<in>
       carrier_mat (2 ^ length (gate_params (instructions qc ! pos)))
                   (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit by simp
next
  show "U3_inv theta phi lambda * U3 theta phi lambda =
       1\<^sub>m (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit U3_inv_left_inverse by simp
next
  show "U3 theta phi lambda * U3_inv theta phi lambda =
       1\<^sub>m (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit U3_inv_right_inverse by simp
qed


lemma preserve_U3_selective_basis:
  (*
    """
    Proves circuit-level semantic preservation for applying the U3 selective
    basis transform to one single-qubit instruction.

    This theorem specializes the abstract selective-basis preservation result by
    supplying the concrete U3 matrix and its proven inverse laws.

    args:
      qc:
        The matrix-based quantum circuit being transformed.

      pos:
        The instruction position selected for basis transformation.

      theta:
        The rotation angle of the U3 basis matrix.

      phi:
        The phi phase of the U3 basis matrix.

      lambda:
        The lambda phase of the U3 basis matrix.

    assumptions:
      The selected position is inside the circuit.

      Every original instruction has a gate matrix with the dimensions implied
      by its qubit parameters.

      The selected instruction acts on exactly one qubit.

    conclusion:
      Evaluating the circuit after U3 selective basis transformation gives the
      same matrix as evaluating the original circuit.
    """
  *)
  assumes pos_lt: "pos < length (instructions qc)"
  assumes qc_carrier:
    "\<forall>instr \<in> set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
  assumes one_qubit:
    "length (gate_params ((instructions qc) ! pos)) = 1"
  shows "eval_circuit
          (apply_selective_basis qc pos
            (U3 theta phi lambda) (U3_inv theta phi lambda)) =
         eval_circuit qc"
proof (rule preserve_selective_basis)
  show "pos < length (instructions qc)"
    using pos_lt .
next
  show "\<forall>instr\<in>set (instructions qc).
       gate_matrix instr \<in> carrier_mat (2 ^ length (gate_params instr))
                                     (2 ^ length (gate_params instr))"
    using qc_carrier .
next
  show "U3 theta phi lambda \<in>
       carrier_mat (2 ^ length (gate_params (instructions qc ! pos)))
                   (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit
    by simp
next
  show "U3_inv theta phi lambda \<in>
       carrier_mat (2 ^ length (gate_params (instructions qc ! pos)))
                   (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit
    by simp
next
  show "U3_inv theta phi lambda * U3 theta phi lambda =
       1\<^sub>m (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit U3_inv_left_inverse
    by simp
next
  show "U3 theta phi lambda * U3_inv theta phi lambda =
       1\<^sub>m (2 ^ length (gate_params (instructions qc ! pos)))"
    using one_qubit U3_inv_right_inverse
    by simp
qed


end

end
