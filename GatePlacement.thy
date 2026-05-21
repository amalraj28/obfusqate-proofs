theory GatePlacement
  imports QuantumCircuitSemantics
begin

text \<open>
  This theory is the final semantic grounding layer.

  QuantumCircuitSemantics.thy proves that obfuscation preserves eval_circuit
  for any gate-placement function satisfying the locale gate_placement.

  The intended meaning of:

    place_gate n G params

  is that the local gate G is embedded into the full n-qubit circuit space,
  acting on the qubits listed in params.

  For a single-qubit gate this corresponds to:

    I \<otimes> ... \<otimes> G \<otimes> ... \<otimes> I

  For a two-qubit gate such as CNOT this corresponds to the full-system
  embedding of CNOT on the two qubits listed in params.

  The key point is that we do not want to expand large tensor products
  entry-by-entry inside every obfuscation proof. Instead, we isolate the
  algebraic laws that placed gates must satisfy once and then reuse the
  already-proven abstract correctness theorem from QuantumCircuitSemantics.
\<close>


section \<open>Restating the Required Gate-Placement Laws\<close>

locale tensor_gate_placement =
  fixes place_gate :: "nat \<Rightarrow> complex mat \<Rightarrow> nat list \<Rightarrow> complex mat"

  assumes tensor_place_carrier:
    "G \<in> carrier_mat (2 ^ length params) (2 ^ length params)
     \<Longrightarrow> place_gate n G params \<in> carrier_mat (2 ^ n) (2 ^ n)"

  assumes tensor_place_compose:
    "\<lbrakk> mats \<noteq> [];
       \<forall>G \<in> set mats. G \<in> carrier_mat (2 ^ length params) (2 ^ length params) \<rbrakk>
     \<Longrightarrow> compose (map (\<lambda>G. place_gate n G params) mats) (2 ^ n)
       = place_gate n (compose mats (2 ^ length params)) params"

  assumes tensor_place_identity:
    "place_gate n (1\<^sub>m (2 ^ length params)) params = 1\<^sub>m (2 ^ n)"
begin

text \<open>
  The three assumptions above are exactly the tensor-placement laws needed
  by the abstract circuit-level semantic correctness theorem.

  They express:

    1. placed gates are full-system matrices;
    2. placing a local sequence and composing it is the same as composing
       locally first and then placing the result;
    3. placing a local identity gives the full-system identity.

  The second law is the formal version of the reasoning:

    (I \<otimes> ... \<otimes> G1 \<otimes> ... \<otimes> I)
    (I \<otimes> ... \<otimes> G2 \<otimes> ... \<otimes> I)
    ...
    =
    I \<otimes> ... \<otimes> (G1 * G2 * ...) \<otimes> ... \<otimes> I

  with the multiplication order determined by compose.
\<close>


sublocale semantic_instance: gate_placement place_gate
proof unfold_locales
  fix G :: "complex mat"
  fix params :: "nat list"
  fix n :: nat

  assume G_carrier:
    "G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"

  show "place_gate n G params \<in> carrier_mat (2 ^ n) (2 ^ n)"
    using G_carrier
    by (rule tensor_place_carrier)

next
  fix mats :: "complex mat list"
  fix params :: "nat list"
  fix n :: nat

  assume mats_nonempty:
    "mats \<noteq> []"

  assume mats_carrier:
    "\<forall>G \<in> set mats.
       G \<in> carrier_mat (2 ^ length params) (2 ^ length params)"

  show
    "compose (map (\<lambda>G. place_gate n G params) mats) (2 ^ n) =
     place_gate n (compose mats (2 ^ length params)) params"
    using mats_nonempty mats_carrier
    by (rule tensor_place_compose)

next
  fix n :: nat
  fix params :: "nat list"

  show "place_gate n (1\<^sub>m (2 ^ length params)) params =
        1\<^sub>m (2 ^ n)"
    by (rule tensor_place_identity)
qed

end

end