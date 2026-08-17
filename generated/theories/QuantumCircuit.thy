theory QuantumCircuit
  imports
    Quantum_Circuit_Insertion
    Quantum_Circuit_Deletion
    Quantum_Circuit_Replacement

begin

lemma insert_operation_preserves_valid_quantum_circuit:
  (* Inserting a valid operation into a valid construction state
     preserves the complete structural validity of the quantum circuit.

     Before insertion:

       1. the circuit is well formed;
       2. the graph is acyclic;
       3. all nodes on each valid wire are comparable; and
       4. every valid wire satisfies the stronger linear-chain
          invariant required by the insertion proofs.

     The previously proved insertion theorems establish that the updated
     circuit remains well formed, acyclic, and wire-linear. Since wire
     linearity implies wire-node comparability, the updated circuit
     satisfies every component of is_valid_circuit.
  *)
  assumes valid_circuit:
    "is_valid_circuit circuit"

assumes valid_state:
  "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

shows
  "is_valid_circuit
       (fst (insert_operation circuit frontier op))"
  using
    insert_operation_preserves_acyclicity
    insert_operation_preserves_well_formed_circuit
    insert_operation_preserves_wire_linearity
    is_valid_construction_state_def
    is_valid_circuit_def
    operation_valid valid_circuit
    valid_state
  by simp
lemma delete_operation_preserves_valid_circuit:
  (* Deleting an operation preserves every structural invariant of a
     valid circuit: well-formedness, acyclicity, and wire linearity.
  *)
  assumes
    valid_state:
      "is_valid_construction_state circuit frontier"
  and
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "is_valid_circuit
       (delete_operation circuit operation_node_id)"

proof -
  have well_formed:
    "is_well_formed_circuit
       (delete_operation circuit operation_node_id)"
    using
      valid_state
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_well_formed_circuit)

  have acyclic:
    "is_acyclic_circuit
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_acyclicity)

  have linear:
    "all_wires_linear
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_wire_linearity)

  show ?thesis
    unfolding is_valid_circuit_def
    using well_formed acyclic linear
    by simp
qed
lemma replacement_preserves_valid_circuit:
  (* Replacing an existing operation by a valid operation with the same
     qubit interface preserves the complete valid-circuit invariant.

     The transformation preserves local well-formedness, graph
     acyclicity, and linearity of every circuit wire.
  *)
  assumes
    valid_circuit:
    "is_valid_circuit circuit"
    and
    valid_replacement:
    "valid_operation_replacement
         circuit operation_node_id replacement_op"
  shows
    "is_valid_circuit
       (replace_operation
          operation_node_id
          replacement_op
          circuit)"
  using
    is_valid_circuit_def
    replacement_preserves_acyclicity
    replacement_preserves_well_formed_circuit
    replacement_preserves_wire_linearity
    valid_circuit
    valid_replacement
  by simp

end
