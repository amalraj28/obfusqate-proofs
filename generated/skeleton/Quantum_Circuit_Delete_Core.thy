theory Quantum_Circuit_Delete_Core
  imports Quantum_Circuit_Navigation

begin



definition reconnect_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
where
  "reconnect_wire original_circuit node_id q current_circuit =
     (case
        (predecessor_on_wire original_circuit node_id q,
         successor_on_wire original_circuit node_id q)
      of
        (Some predecessor, Some successor) \<Rightarrow>
          insert_edge
            (make_edge predecessor successor q)
            (delete_edge
              (make_edge node_id successor q)
              (delete_edge
                (make_edge predecessor node_id q)
                current_circuit))
      | _ \<Rightarrow> current_circuit)"

definition delete_operation ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> quantum_circuit"
where
  "delete_operation circuit node_id =
     (case nodes circuit node_id of
        Some (OperationNode op) \<Rightarrow>
          (let
             reconnected_circuit =
               fold
                 (reconnect_wire circuit node_id)
                 (op_qargs op)
                 circuit
           in
             reconnected_circuit
               \<lparr>nodes :=
                  (nodes reconnected_circuit)
                    (node_id := None)\<rparr>)
      | _ \<Rightarrow> circuit)"

lemma reconnect_wire_preserves_nodes[simp]:
  "nodes
     (reconnect_wire original_circuit operation_node_id q circuit)
     node_id
   =
   nodes circuit node_id"

  sorry

lemma fold_reconnect_wire_preserves_nodes[simp]:
  "nodes
     (fold
        (reconnect_wire original_circuit operation_node_id)
        qs
        circuit)
     node_id
   =
   nodes circuit node_id"

sorry

lemma delete_operation_nodes:
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "nodes
       (delete_operation circuit operation_node_id)
     =
     (nodes circuit)(operation_node_id := None)"

sorry

lemma delete_operation_other_node[simp]:
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    different_node:
      "other_node_id \<noteq> operation_node_id"
  shows
    "nodes
       (delete_operation circuit operation_node_id)
       other_node_id
     =
     nodes circuit other_node_id"

  sorry

lemma reconnect_wire_edges_characterisation:
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q =
         Some successor_id"
  shows
    "edges
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
     =
     insert
       (make_edge predecessor_id successor_id q)
       (edges current_circuit
          - { make_edge predecessor_id operation_node_id q,
              make_edge operation_node_id successor_id q })"

  sorry

lemma reconnect_wire_successor_predecessor_characterisation:
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q =
         Some successor_id"
  shows
    "wire_edge_relation
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
     =
     insert
       (predecessor_id, successor_id)
       (wire_edge_relation current_circuit q
          - {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"

sorry

lemma reconnect_wire_preserves_input_boundary:
  assumes
    no_input_predecessor:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_id"
  shows
    "(\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation
                (reconnect_wire
                   circuit
                   operation_node_id
                   q
                   circuit)
                q)
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
       (get_input_node_id q)"

sorry

lemma reconnect_wire_preserves_input_boundary_from_same_relation:
  assumes
    no_input_predecessor:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation current_circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         current_circuit q (get_input_node_id q)"
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
    "(\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation
                (reconnect_wire
                   original_circuit
                   operation_node_id
                   q
                   current_circuit)
                q)
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       (get_input_node_id q)"

sorry

lemma reconnect_wire_preserves_other_wire_relation:
  assumes
    different_wire:
      "r \<noteq> q"
  shows
    "wire_edge_relation
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       r
     =
     wire_edge_relation current_circuit r"

  sorry

lemma fold_reconnect_preserves_other_wire_relation:
  fixes r
  assumes other_wire:
    "r \<notin> set qs"
  shows
    "wire_edge_relation
       (fold
          (reconnect_wire
             original_circuit
             operation_node_id)
          qs
          current_circuit)
       r
     =
     wire_edge_relation current_circuit r"
  sorry

lemma fold_reconnect_preserves_input_boundary:
  assumes
    no_input_predecessor:
      "\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
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
    "(\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation
                (fold
                   (reconnect_wire circuit operation_node_id)
                   qs
                   circuit)
                q)
     \<and>
     has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       (get_input_node_id q)"

sorry

lemma delete_operation_removes_operation_node[simp]:

  assumes operation_node:
    "nodes circuit node_id = Some (OperationNode op)"

  shows
    "nodes (delete_operation circuit node_id) node_id = None"

sorry

lemma reconnect_wire_preserves_num_qubits:
  "num_qubits
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   num_qubits current_circuit"
  
  sorry

lemma reconnect_wire_edge_cases:
  assumes
    edge_after:
      "e \<in>
       edges
         (reconnect_wire
           original_circuit
           operation_node_id
           q
           current_circuit)"
  shows
    "e \<in> edges current_circuit
     \<or>
     (\<exists>predecessor successor. predecessor_on_wire original_circuit operation_node_id q
        = Some predecessor
      \<and>
        successor_on_wire original_circuit operation_node_id q
        = Some successor
      \<and>
        e = make_edge predecessor successor q)"
sorry

lemma fold_reconnect_wire_edge_cases:
  assumes
    edge_after:
      "e \<in>
       edges
         (fold
           (reconnect_wire original_circuit operation_node_id)
           qs
           current_circuit)"
  shows
    "e \<in> edges current_circuit
     \<or>
     (\<exists>q \<in> set qs.
        \<exists>predecessor successor.
          predecessor_on_wire
            original_circuit operation_node_id q
            = Some predecessor
        \<and>
          successor_on_wire
            original_circuit operation_node_id q
            = Some successor
        \<and>
          e = make_edge predecessor successor q)"
  
  sorry

lemma reconnect_wire_inserted_edge_well_formed:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_node_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_node_id"
  shows
    "is_well_formed_edge
       (reconnect_wire circuit operation_node_id q circuit)
       (make_edge predecessor_node_id successor_node_id q)"

sorry

lemma fold_reconnect_wire_preserves_num_qubits:
  "num_qubits
     (fold
       (reconnect_wire original_circuit node_id)
       qs
       current_circuit)
   =
   num_qubits current_circuit"

sorry

lemma operation_incident_edge_on_wire_cases:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    operation_uses_wire:
      "q \<in> set (op_qargs op)"
  and
    incident_edge:
      "e \<in> edges circuit"
  and
    edge_on_wire:
      "edge_wire e = q"
  and
    incident:
      "edge_source e = operation_node_id
       \<or> edge_target e = operation_node_id"
  shows
    "(\<exists>predecessor.
        predecessor_on_wire circuit operation_node_id q =
          Some predecessor
      \<and>
        e = make_edge predecessor operation_node_id q)
     \<or>
     (\<exists>successor.
        successor_on_wire circuit operation_node_id q =
          Some successor
      \<and>
        e = make_edge operation_node_id successor q)"
sorry

lemma fold_reconnect_wire_removes_incident_edges:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in>
       edges
         (fold
           (reconnect_wire circuit operation_node_id)
           (op_qargs op)
           circuit)"
  shows
    "edge_source e \<noteq> operation_node_id
     \<and> edge_target e \<noteq> operation_node_id"
sorry

lemma delete_operation_preserves_num_qubits:

  shows
    "num_qubits (delete_operation circuit node_id) = num_qubits circuit"

sorry

lemma reconnect_wire_preserves_next_id:
  "next_id
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   next_id current_circuit"

  sorry

lemma fold_reconnect_wire_preserves_next_id:
  "next_id
     (fold
        (reconnect_wire original_circuit node_id)
        qs
        current_circuit)
   =
   next_id current_circuit"

sorry

lemma delete_operation_preserves_next_id:
  "next_id (delete_operation circuit node_id) = next_id circuit"

sorry

lemma delete_operation_preserves_boundary_nodes:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_boundary_nodes
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_preserves_operation_nodes:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_operation_nodes
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_edge_preserves_reachability:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    edge_after:
      "(source_id, target_id)
       \<in>
       edge_relation
         (delete_operation circuit operation_node_id)"
  shows
    "(source_id, target_id)
     \<in>
     (edge_relation circuit)\<^sup>+"
sorry

lemma delete_operation_remaining_edges_not_incident:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in> edges
         (delete_operation circuit operation_node_id)"
  shows
    "edge_source e \<noteq> operation_node_id
     \<and> edge_target e \<noteq> operation_node_id"

sorry

lemma delete_operation_preserves_well_formed_edges:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_edges
       (delete_operation circuit operation_node_id)"


sorry

lemma delete_operation_preserves_well_formed_circuit:
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
    "is_well_formed_circuit
       (delete_operation circuit operation_node_id)"

sorry

end
