theory Quantum_Circuit_Insert_Validity
  imports Quantum_Circuit_Insert_Core

begin


lemma wire_node_reaches_frontier_or_is_output:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes frontier_valid:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes node_lookup:
  "nodes circuit node_id = Some node_value"

assumes node_uses_q:
  "node_uses_qubit node_value q"

assumes frontier_unique_successor:
  "has_unique_wire_successor circuit q (frontier q)"

shows
  "node_id = get_output_node_id q
       \<or> node_id = frontier q
       \<or> wire_reaches circuit q node_id (frontier q)"

sorry

lemma subdividing_final_edge_preserves_old_reachability:
  assumes old_reachability:
    "wire_reaches circuit q node_a node_b"

assumes output_has_no_successor:
  "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "wire_reaches updated_circuit q node_a node_b"

sorry

lemma subdividing_final_edge_preserves_wire_comparability:
  assumes comparable_before:
    "nodes_comparable_on_wire circuit q"

assumes circuit_well_formed:
  "is_well_formed_circuit circuit"

assumes linear_before:
  "wire_is_linear circuit q"

assumes frontier_valid:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused:
  "nodes circuit new_node_id = None"

assumes new_node_exists_after:
  "nodes updated_circuit new_node_id = Some new_node"

assumes new_node_uses_q:
  "node_uses_qubit new_node q"

assumes old_nodes_unchanged:
  "\<And>node_id.
         node_id \<noteq> new_node_id
         \<Longrightarrow> nodes updated_circuit node_id =
             nodes circuit node_id"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
         insert
           (new_node_id, get_output_node_id q)
           (insert
             (frontier q, new_node_id)
             (wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}))"

shows
  "nodes_comparable_on_wire updated_circuit q"

sorry

lemma subdividing_final_edge_preserves_input_boundary:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused_before:
  "nodes circuit new_node_id = None"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
           insert
             (new_node_id, get_output_node_id q)
             (insert
               (frontier q, new_node_id)
               (wire_edge_relation circuit q -
                  {(frontier q, get_output_node_id q)}))"

assumes new_node_not_input:
  "new_node_id \<noteq> get_input_node_id q"

shows
  "(\<nexists>predecessor_id.
            (predecessor_id, get_input_node_id q)
              \<in> wire_edge_relation updated_circuit q)
         \<and>
         has_unique_wire_successor
           updated_circuit q (get_input_node_id q)"

sorry

lemma subdividing_final_edge_preserves_output_no_successor:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_not_output:
  "new_node_id \<noteq> get_output_node_id q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation updated_circuit q"

sorry

lemma subdividing_final_edge_preserves_output_predecessor:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_not_output:
  "new_node_id \<noteq> get_output_node_id q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "has_unique_wire_predecessor
       updated_circuit q (get_output_node_id q)"

sorry

lemma subdividing_final_edge_preserves_operation_node_degrees:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused_before:
  "nodes circuit new_node_id = None"

assumes new_node_exists_after:
  "nodes updated_circuit new_node_id =
         Some (OperationNode new_op)"

assumes new_node_uses_q:
  "node_uses_qubit (OperationNode new_op) q"

assumes circuit_well_formed:
  "is_well_formed_circuit circuit"

assumes old_nodes_unchanged:
  "\<And>node_id.
         node_id \<noteq> new_node_id
         \<Longrightarrow> nodes updated_circuit node_id =
             nodes circuit node_id"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
         insert
           (new_node_id, get_output_node_id q)
           (insert
             (frontier q, new_node_id)
             (wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}))"

shows
  "\<forall>node_id stored_op.
         nodes updated_circuit node_id =
           Some (OperationNode stored_op)
         \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
         \<longrightarrow> has_unique_wire_predecessor
               updated_circuit q node_id
           \<and> has_unique_wire_successor
               updated_circuit q node_id"

sorry

lemma insert_operation_preserves_wire_linearity:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

assumes linear_before:
  "all_wires_linear circuit"

shows
  "all_wires_linear
           (fst (insert_operation circuit frontier op))"

  sorry

lemma insert_operation_preserves_acyclicity:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"
    and operation_valid:
    "operation_in_circuit circuit op"
    and acyclic:
    "is_acyclic_circuit circuit"
    and linear_before:
    "all_wires_linear circuit"
  shows
    "is_acyclic_circuit
       (fst (insert_operation circuit frontier op))"

sorry

lemma insert_operation_preserves_valid_quantum_circuit:
  assumes valid_circuit:
    "is_valid_circuit circuit"

assumes valid_state:
  "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

shows
  "is_valid_circuit
       (fst (insert_operation circuit frontier op))"
  sorry

lemma initial_construction_state_is_valid:
  "is_valid_construction_state (initial_circuit number_of_qubits) initial_frontier"

  sorry

end
