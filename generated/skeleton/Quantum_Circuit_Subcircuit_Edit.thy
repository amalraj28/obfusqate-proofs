theory Quantum_Circuit_Subcircuit_Edit
  imports Quantum_Circuit_Subcircuit_Model

begin


definition remove_operation_node ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> quantum_circuit"
  where
    "remove_operation_node circuit operation_node_id =
       circuit
         \<lparr>
           nodes :=
             (nodes circuit)
               (operation_node_id := None),
  
           edges :=
             {e \<in> edges circuit.
                edge_source e \<noteq> operation_node_id
              \<and> edge_target e \<noteq> operation_node_id}
         \<rparr>"

lemma remove_operation_node_selected[simp]:
  "nodes
     (remove_operation_node circuit operation_node_id)
     operation_node_id
   = None"

  sorry

lemma remove_operation_node_other[simp]:
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  shows
    "nodes
       (remove_operation_node circuit operation_node_id)
       other_node_id
     =
     nodes circuit other_node_id"

  sorry

lemma edges_remove_operation_node[simp]:
  "edges
     (remove_operation_node circuit operation_node_id)
   =
   {e \<in> edges circuit.
      edge_source e \<noteq> operation_node_id
    \<and> edge_target e \<noteq> operation_node_id}"

  sorry

lemma remove_operation_node_has_no_outgoing_edge:
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  shows
    "edge_source e \<noteq> operation_node_id"

  sorry

lemma remove_operation_node_has_no_incoming_edge:
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  shows
    "edge_target e \<noteq> operation_node_id"

  sorry

lemma remove_operation_node_preserves_unrelated_edge:
  assumes edge_exists:
    "e \<in> edges circuit"

  assumes source_different:
    "edge_source e \<noteq> operation_node_id"

  assumes target_different:
    "edge_target e \<noteq> operation_node_id"

  shows
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  sorry

lemma remove_operation_node_preserves_num_qubits[simp]:
  "num_qubits
     (remove_operation_node circuit operation_node_id)
   =
   num_qubits circuit"

  sorry

lemma remove_operation_node_preserves_next_id[simp]:
  "next_id
     (remove_operation_node circuit operation_node_id)
   =
   next_id circuit"

  sorry

definition insert_subcircuit_nodes ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
where
  "insert_subcircuit_nodes
      original_circuit
      current_circuit
      replacement =
     current_circuit
       \<lparr>
         nodes :=
           (\<lambda>host_node_id.
              let
                renaming_offset =
                  node_id_to_nat (next_id original_circuit);

                host_node_number =
                  node_id_to_nat host_node_id;

                local_node_id =
                  NodeId
                    (host_node_number - renaming_offset)
              in
                if renaming_offset \<le> host_node_number
                   \<and> local_node_id
                       \<in> subcircuit_operation_node_ids replacement
                then
                  nodes
                    (subgraph replacement)
                    local_node_id
                else
                  nodes current_circuit host_node_id)
       \<rparr>"

lemma insert_subcircuit_nodes_node_cases:
  assumes inserted_node:
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          circuit
          replacement)
       node_id
     =
     Some node"
  shows
    "nodes circuit node_id = Some node
     \<or>
     (\<exists>local_node_id.
        local_node_id \<in> subcircuit_operation_node_ids replacement
        \<and>
        node_id =
          rename_subcircuit_node_id
            original_circuit
            local_node_id
        \<and>
        nodes (subgraph replacement) local_node_id = Some node)"


sorry

lemma insert_subcircuit_nodes_copies_operation_node:
  assumes local_operation_node:
    "local_node_id
       \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          current_circuit
          replacement)
       (rename_subcircuit_node_id
          original_circuit
          local_node_id)
     =
     nodes (subgraph replacement) local_node_id"

  sorry

lemma insert_subcircuit_nodes_copies_operation:
  assumes local_operation:
    "nodes (subgraph replacement) local_node_id =
       Some (OperationNode op)"

  assumes allocated_local_node:
    "local_node_id
       \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          current_circuit
          replacement)
       (rename_subcircuit_node_id
          original_circuit
          local_node_id)
     =
     Some (OperationNode op)"

  sorry

lemma insert_subcircuit_nodes_preserves_node_below_next_id:
  assumes existing_namespace:
    "node_id_to_nat node_id
       < node_id_to_nat (next_id original_circuit)"

  shows
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          current_circuit
          replacement)
       node_id
     =
     nodes current_circuit node_id"

  sorry

lemma insert_subcircuit_nodes_preserves_edges[simp]:
  "edges
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   edges current_circuit"

  sorry

lemma insert_subcircuit_nodes_preserves_num_qubits[simp]:
  "num_qubits
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  sorry

lemma insert_subcircuit_nodes_preserves_next_id[simp]:
  "next_id
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  sorry

definition insert_subcircuit_internal_edges ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
where
  "insert_subcircuit_internal_edges
      original_circuit
      current_circuit
      replacement =
     current_circuit
       \<lparr>
         edges :=
           edges current_circuit
           \<union>
           renamed_subcircuit_internal_edges
             original_circuit
             replacement
       \<rparr>"

lemma edges_insert_subcircuit_internal_edges[simp]:
  "edges
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   edges current_circuit
   \<union>
   renamed_subcircuit_internal_edges
     original_circuit
     replacement"

  sorry

lemma insert_subcircuit_internal_edges_preserves_existing_edge:
  assumes existing_edge:
    "e \<in> edges current_circuit"

  shows
    "e \<in>
       edges
         (insert_subcircuit_internal_edges
            original_circuit
            current_circuit
            replacement)"

  sorry

lemma insert_subcircuit_internal_edges_contains_renamed_edge:
  assumes renamed_edge:
    "e \<in>
       renamed_subcircuit_internal_edges
         original_circuit
         replacement"

  shows
    "e \<in>
       edges
         (insert_subcircuit_internal_edges
            original_circuit
            current_circuit
            replacement)"

  sorry

lemma insert_subcircuit_internal_edges_contains_internal_edge:
  assumes internal_edge:
    "e \<in> subcircuit_internal_edges replacement"

  shows
    "rename_subcircuit_edge original_circuit e
       \<in>
       edges
         (insert_subcircuit_internal_edges
            original_circuit
            current_circuit
            replacement)"

  sorry

lemma insert_subcircuit_internal_edges_preserves_nodes[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   nodes current_circuit"

  sorry

lemma insert_subcircuit_internal_edges_preserves_node[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
     node_id
   =
   nodes current_circuit node_id"

  sorry

lemma insert_subcircuit_internal_edges_preserves_num_qubits[simp]:
  "num_qubits
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  sorry

lemma insert_subcircuit_internal_edges_preserves_next_id[simp]:
  "next_id
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  sorry

end
