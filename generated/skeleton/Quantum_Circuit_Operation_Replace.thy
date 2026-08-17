theory Quantum_Circuit_Operation_Replace
  imports Quantum_Circuit_Delete_Validity

begin



definition is_operation_node_id ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> bool"
where
  "is_operation_node_id circuit node_id \<longleftrightarrow>
     (\<exists>op. nodes circuit node_id = Some (OperationNode op))"

definition replace_operation ::
  "node_id \<Rightarrow> operation \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
where
  "replace_operation node_id replacement_op circuit =
     (
       case nodes circuit node_id of
         Some (OperationNode old_op) \<Rightarrow>
           insert_node node_id (OperationNode replacement_op) circuit
       | _ \<Rightarrow>
           circuit
     )"

definition valid_operation_replacement ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> operation \<Rightarrow> bool"
where
  "valid_operation_replacement
      circuit operation_node_id replacement_op
   \<longleftrightarrow>
     (\<exists>original_op.
        nodes circuit operation_node_id =
          Some (OperationNode original_op)
      \<and> operation_in_circuit circuit replacement_op
      \<and> op_qargs replacement_op = op_qargs original_op)"


lemma replace_operation_selected_node:
  assumes operation_exists:
    "nodes circuit operation_node_id =
       Some (OperationNode original_op)"
  shows
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       operation_node_id
     =
     Some (OperationNode replacement_op)"

  sorry

lemma valid_replacement_selected_node:
  assumes valid_replacement:
    "valid_operation_replacement
       circuit operation_node_id replacement_op"
  shows
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       operation_node_id
     =
     Some (OperationNode replacement_op)"

sorry

lemma replacement_preserves_other_nodes:
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"
  shows
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       other_node_id
     =
     nodes circuit other_node_id"

\<comment>\<open>operation_node_id can have 4 possible states
  1. None
  2. InputNode q
  3. OutputNode q
  4. OperationNode original_op

  For first three cases, replace_operation returns circuit
  For last case it calls
    insert_node
      operation_node_id
      (OperationNode replacement_op)
      circuit

  Since other_node_id \<noteq> operation_node_id, the lemma "nodes_insert_node_other" shows that other nodes are unchanged.
\<close>

sorry

lemma replacement_preserves_edges:
  "edges
     (replace_operation operation_node_id replacement_op circuit)
   =
   edges circuit"

  sorry
  
lemma replacement_preserves_num_qubits:
  "num_qubits
     (replace_operation operation_node_id replacement_op circuit)
   =
   num_qubits circuit"

  sorry

lemma replacement_preserves_next_id:
  "next_id
     (replace_operation operation_node_id replacement_op circuit)
   =
   next_id circuit"

  sorry

lemma valid_replacement_preserves_node_wire_usage:
  assumes valid_replacement:
    "valid_operation_replacement
       circuit operation_node_id replacement_op"
  shows
    "(case
        nodes
          (replace_operation
             operation_node_id
             replacement_op
             circuit)
          node_id
      of
        None \<Rightarrow> False
      | Some node \<Rightarrow> node_uses_qubit node q)
     =
     (case nodes circuit node_id of
        None \<Rightarrow> False
      | Some node \<Rightarrow> node_uses_qubit node q)"

sorry

lemma replacement_preserves_well_formed_circuit:
  assumes
    well_formed:
      "is_well_formed_circuit circuit"
  and
    valid_replacement:
      "valid_operation_replacement
         circuit
         operation_node_id
         replacement_op"
  shows
    "is_well_formed_circuit
       (replace_operation
          operation_node_id
          replacement_op
          circuit)"

  sorry

lemma replacement_preserves_acyclicity:

  assumes acyclic:
    "is_acyclic_circuit circuit"

  shows
   "is_acyclic_circuit
     (replace_operation
         operation_node_id replacement_op circuit)"

  sorry

lemma replacement_preserves_wire_edge_relation:
  "wire_edge_relation
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q
   =
   wire_edge_relation circuit q"

  sorry

lemma replacement_preserves_wire_reaches:
  "wire_reaches
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_a node_b
   \<longleftrightarrow>
   wire_reaches circuit q node_a node_b"

  sorry

lemma replacement_preserves_unique_wire_predecessor:
  "has_unique_wire_predecessor
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_id
   \<longleftrightarrow>
   has_unique_wire_predecessor circuit q node_id"

  sorry

lemma replacement_preserves_unique_wire_successor:
  "has_unique_wire_successor
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_id
   \<longleftrightarrow>
   has_unique_wire_successor circuit q node_id"

  sorry

lemma valid_replacement_preserves_nodes_comparable_on_wire:
  assumes
    valid_replacement:
      "valid_operation_replacement
         circuit operation_node_id replacement_op"
  and
    original_comparable:
      "nodes_comparable_on_wire circuit q"
  shows
    "nodes_comparable_on_wire
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       q"

  sorry

lemma replacement_preserves_wire_linearity:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    valid_replacement:
      "valid_operation_replacement
         circuit operation_node_id replacement_op"
  shows
    "all_wires_linear
       (replace_operation
          operation_node_id
          replacement_op
          circuit)"

sorry

lemma replacement_preserves_valid_circuit:
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
  sorry

end
