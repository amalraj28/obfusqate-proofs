theory Quantum_Circuit_Subcircuit_Edit
  imports Quantum_Circuit_Subcircuit_Model

begin

definition remove_operation_node ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> quantum_circuit"
  where
    (* Removes one node from the circuit without reconnecting its wires.
  
       The transformation:
         1. changes the selected node-table entry to None; and
         2. removes every edge whose source or target is the selected node.
  
       All unrelated nodes and edges remain unchanged. The circuit's
       qubit count and next_id are also preserved.
  
       This helper deliberately does not reconnect the surrounding wires.
       Later subcircuit-replacement stages connect the original
       predecessors to the replacement input interface and connect the
       replacement output interface to the original successors.
    *)
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
  (* Looking up the removed node ID after removal returns None. *)
  "nodes
     (remove_operation_node circuit operation_node_id)
     operation_node_id
   = None"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_other[simp]:
  (* Removing one node does not alter the node-table entry stored at
     any different node ID. *)
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  shows
    "nodes
       (remove_operation_node circuit operation_node_id)
       other_node_id
     =
     nodes circuit other_node_id"

  using different_node
  unfolding remove_operation_node_def
  by simp

lemma edges_remove_operation_node[simp]:
  (* The resulting edge set contains exactly the original edges that
     are not incident on the removed node. *)
  "edges
     (remove_operation_node circuit operation_node_id)
   =
   {e \<in> edges circuit.
      edge_source e \<noteq> operation_node_id
    \<and> edge_target e \<noteq> operation_node_id}"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_has_no_outgoing_edge:
  (* After removal, no remaining edge has the removed node as its
     source. *)
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  shows
    "edge_source e \<noteq> operation_node_id"

  using edge_remains
  by simp

lemma remove_operation_node_has_no_incoming_edge:
  (* After removal, no remaining edge has the removed node as its
     target. *)
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  shows
    "edge_target e \<noteq> operation_node_id"

  using edge_remains
  by simp

lemma remove_operation_node_preserves_unrelated_edge:
  (* An original edge remains after node removal when neither endpoint
     is the removed node. *)
  assumes edge_exists:
    "e \<in> edges circuit"

  assumes source_different:
    "edge_source e \<noteq> operation_node_id"

  assumes target_different:
    "edge_target e \<noteq> operation_node_id"

  shows
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  using
    edge_exists
    source_different
    target_different
  by simp

lemma remove_operation_node_preserves_num_qubits[simp]:
  (* Removing a node does not change the circuit's qubit count. *)
  "num_qubits
     (remove_operation_node circuit operation_node_id)
   =
   num_qubits circuit"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_preserves_next_id[simp]:
  (* Removing a node does not allocate any IDs, so next_id remains
     unchanged. *)
  "next_id
     (remove_operation_node circuit operation_node_id)
   =
   next_id circuit"

  unfolding remove_operation_node_def
  by simp

definition insert_subcircuit_nodes ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
where
  (* Copies every operation node from the replacement subcircuit into
     the current host circuit.

     original_circuit fixes the renaming namespace. In particular,
     next_id original_circuit is used as the offset for every copied
     node throughout the complete replacement transformation.

     current_circuit is the circuit currently being transformed. It may
     already have had the original operation node and its incident edges
     removed.

     Only operation nodes are copied. The canonical input and output
     boundary nodes of the subcircuit are not copied because the host
     circuit already provides its own boundary nodes.

     A local node with numeric ID i is stored at

         next_id original_circuit + i.

     After copying, next_id is advanced beyond the complete local node
     namespace of the subcircuit. The edge set and qubit count are left
     unchanged.
  *)
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


proof -
  obtain host_node_number where node_id_eq:
    "node_id = NodeId host_node_number"
    by (cases node_id) simp

  obtain renaming_offset where next_id_eq:
    "next_id original_circuit = NodeId renaming_offset"
    by (cases "next_id original_circuit") simp

  let ?local_node_id =
    "NodeId (host_node_number - renaming_offset)"

  from inserted_node have inserted_node_cases:
    "(if renaming_offset \<le> host_node_number
         \<and>
         ?local_node_id
           \<in> subcircuit_operation_node_ids replacement
      then
        nodes
          (subgraph replacement)
          ?local_node_id
      else
        nodes circuit node_id)
     =
     Some node"
    unfolding
      insert_subcircuit_nodes_def
      node_id_eq
      next_id_eq
    by auto

  show ?thesis
    by (metis
        inserted_node_cases
        next_id_eq
        node_id_eq
        node_id_to_nat.simps
        ordered_cancel_comm_monoid_diff_class.add_diff_inverse
        rename_subcircuit_node_id_def)
qed

lemma insert_subcircuit_nodes_copies_operation_node:
  (* Every local operation node appears at its renamed host-circuit ID
     after insertion. *)
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

  using local_operation_node
  unfolding
    insert_subcircuit_nodes_def
    rename_subcircuit_node_id_def
  by (cases local_node_id;
      cases "next_id original_circuit";
      simp)

lemma insert_subcircuit_nodes_copies_operation:
  (* If a local subcircuit node stores OperationNode op, then its
     renamed host ID stores the same operation after insertion. *)
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

  using
    insert_subcircuit_nodes_copies_operation_node[
      OF allocated_local_node,
      of original_circuit current_circuit]
    local_operation
  by simp

lemma insert_subcircuit_nodes_preserves_node_below_next_id:
  (* Node-table entries below the original next_id cannot belong to the
     renamed subcircuit namespace and therefore remain unchanged. *)
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

  using existing_namespace
  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_edges[simp]:
  (* Copying nodes does not yet insert any subcircuit edges. *)
  "edges
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   edges current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_num_qubits[simp]:
  (* Copying replacement nodes does not change the host's qubit
     universe. *)
  "num_qubits
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_next_id[simp]:
  (* Copying the replacement nodes does not yet advance the host
     circuit's allocation boundary. The complete replacement
     transformation will update next_id once all nodes and edges have
     been installed. *)
  "next_id
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

definition insert_subcircuit_internal_edges ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
where
  (* Inserts all internal edges of the replacement subcircuit into the
     current host circuit.

     original_circuit fixes the renaming offset through its next_id.
     current_circuit is the intermediate circuit being transformed.

     Only edges whose source and target are both operation nodes of the
     replacement are inserted here. Connections between the host
     circuit and the replacement interfaces are added by later helpers.
  *)
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

  unfolding insert_subcircuit_internal_edges_def
  by simp

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

  using existing_edge
  unfolding insert_subcircuit_internal_edges_def
  by simp

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

  using renamed_edge
  unfolding insert_subcircuit_internal_edges_def
  by simp

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

  using
    renamed_subcircuit_internal_edge[
      OF internal_edge,
      of original_circuit]
  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_nodes[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   nodes current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_node[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
     node_id
   =
   nodes current_circuit node_id"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_num_qubits[simp]:
  "num_qubits
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_next_id[simp]:
  "next_id
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

end
