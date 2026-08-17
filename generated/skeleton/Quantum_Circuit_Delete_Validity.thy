theory Quantum_Circuit_Delete_Validity
  imports Quantum_Circuit_Delete_Core

begin


lemma delete_operation_reachability_preserved:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "(edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+
       \<subseteq>
     (edge_relation circuit)\<^sup>+"
sorry

lemma reconnect_wire_successor_has_unique_predecessor:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor
         current_circuit q successor_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
         wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       successor_id"

sorry

lemma reconnect_wire_predecessor_has_unique_successor:
  assumes
    unique_successor:
      "has_unique_wire_successor
         current_circuit q predecessor_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
         wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  shows
    "has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       predecessor_id"

sorry

lemma reconnect_wire_other_node_has_unique_predecessor:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor
         current_circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_successor:
      "node_id \<noteq> successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_id"

sorry

lemma reconnect_wire_other_node_has_unique_successor:
  assumes
    unique_successor:
      "has_unique_wire_successor
         current_circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_predecessor:
      "node_id \<noteq> predecessor_id"
  shows
    "has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_id"

sorry

lemma reconnect_wire_preserves_remaining_node_degrees:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor current_circuit q node_id"
  and
    unique_successor:
      "has_unique_wire_successor current_circuit q node_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
       wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    remaining_node:
      "node_id \<noteq> operation_node_id"
  and
    predecessor_not_deleted:
      "predecessor_id \<noteq> operation_node_id"
  and
    successor_not_deleted:
      "successor_id \<noteq> operation_node_id"
  and
    predecessor_not_successor:
      "predecessor_id \<noteq> successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit operation_node_id q current_circuit)
       q node_id
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          original_circuit operation_node_id q current_circuit)
       q node_id"
  sorry

lemma fold_reconnect_preserves_operation_degrees:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor circuit q node_id"
  and
    unique_successor:
      "has_unique_wire_successor circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         circuit operation_node_id q =
       Some successor_id"
  and
    remaining_node:
      "node_id \<noteq> operation_node_id"
  and
    predecessor_not_deleted:
      "predecessor_id \<noteq> operation_node_id"
  and
    successor_not_deleted:
      "successor_id \<noteq> operation_node_id"
  and
    predecessor_not_successor:
      "predecessor_id \<noteq> successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_id
     \<and>
     has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_id"

sorry

lemma delete_operation_preserves_acyclicity:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "is_acyclic_circuit
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_preserves_unused_wire_relation:
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation circuit q"

sorry

lemma delete_operation_preserves_linear_unused_wire:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_is_linear circuit q
     \<Longrightarrow>
     wire_is_linear
       (delete_operation circuit operation_node_id)
       q"

sorry

lemma reconnect_wire_preserves_surviving_reachability:
  assumes
    same_relation:
      "wire_edge_relation current_circuit q =
       wire_edge_relation original_circuit q"
  and
    unique_operation_predecessor:
      "has_unique_wire_predecessor
         current_circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor
         current_circuit q operation_node_id"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    old_reachability:
      "wire_reaches current_circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  shows
    "wire_reaches
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_a
       node_b"

sorry

lemma fold_reconnect_preserves_surviving_reachability:
  assumes
    unique_operation_predecessor:
      "has_unique_wire_predecessor
         circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor
         circuit q operation_node_id"
  and
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         circuit operation_node_id q =
       Some successor_id"
  and
    old_reachability:
      "wire_reaches circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "wire_reaches
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_a
       node_b"

sorry

lemma delete_operation_preserves_surviving_wire_reachability:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  and
    old_reachability:
      "wire_reaches circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  shows
    "wire_reaches
       (delete_operation circuit operation_node_id)
       q
       node_a
       node_b"

sorry

lemma delete_operation_used_wire_preserves_comparability:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "nodes_comparable_on_wire
       (delete_operation circuit operation_node_id)
       q"

sorry

lemma delete_operation_used_wire_preserves_input_boundary:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)
     \<and>
     has_unique_wire_successor
       (delete_operation circuit operation_node_id)
       q
       (get_input_node_id q)"

sorry

lemma reconnect_wire_preserves_output_boundary:
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (reconnect_wire
                  circuit
                  operation_node_id
                  q
                  circuit)
               q)"

sorry

lemma reconnect_wire_preserves_output_boundary_from_same_relation:
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         current_circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation current_circuit q"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
         wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
         Some successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (reconnect_wire
                  original_circuit
                  operation_node_id
                  q
                  current_circuit)
               q)"

sorry

lemma fold_reconnect_preserves_output_boundary:
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
  and
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire
         circuit operation_node_id q =
         Some successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (fold
                  (reconnect_wire circuit operation_node_id)
                  qs
                  circuit)
               q)"

sorry

lemma delete_operation_used_wire_preserves_output_boundary:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "has_unique_wire_predecessor
       (delete_operation circuit operation_node_id)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)"

sorry

lemma delete_operation_used_wire_preserves_operation_degrees:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "\<forall>node_id remaining_op.
       nodes
         (delete_operation circuit operation_node_id)
         node_id
       =
       Some (OperationNode remaining_op)
       \<longrightarrow>
       node_uses_qubit (OperationNode remaining_op) q
       \<longrightarrow>
       has_unique_wire_predecessor
         (delete_operation circuit operation_node_id)
         q
         node_id
       \<and>
       has_unique_wire_successor
         (delete_operation circuit operation_node_id)
         q
         node_id"

sorry

lemma delete_operation_preserves_linear_used_wire:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  shows
    "wire_is_linear circuit q
     \<Longrightarrow>
     wire_is_linear
       (delete_operation circuit operation_node_id)
       q"

sorry

lemma delete_operation_preserves_wire_is_linear:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    valid_wire_after:
      "qubit_in_circuit
         (delete_operation circuit operation_node_id)
         q"
  shows
    "wire_is_linear
       (delete_operation circuit operation_node_id)
       q"
  sorry

lemma delete_operation_preserves_wire_linearity:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "all_wires_linear
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_preserves_valid_circuit:
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

sorry

end
