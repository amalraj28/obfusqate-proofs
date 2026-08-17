theory Quantum_Circuit_Replacement
  imports Quantum_Circuit_State

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
section \<open>Subcircuit Replacement\<close>
record subcircuit =
  subgraph :: quantum_circuit

  input_interface :: "qubit \<Rightarrow> node_id option"

  output_interface :: "qubit \<Rightarrow> node_id option"
definition subcircuit_uses_qubit ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> bool"
  where
    "subcircuit_uses_qubit subcircuit q \<longleftrightarrow>
        input_interface subcircuit q \<noteq> None
     \<or> output_interface subcircuit q \<noteq> None"
definition subcircuit_interface_qubits ::
  "subcircuit \<Rightarrow> qubit set"
  where
    "subcircuit_interface_qubits subcircuit =
       {q. input_interface subcircuit q \<noteq> None}"
definition interface_node_uses_qubit ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "interface_node_uses_qubit subcircuit q node_id \<longleftrightarrow>
       (\<exists>node.
          nodes (subgraph subcircuit) node_id = Some node
        \<and> node_uses_qubit node q)"
definition is_input_interface_node ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_input_interface_node subcircuit q node_id \<longleftrightarrow>
         input_interface subcircuit q = Some node_id
       \<and> interface_node_uses_qubit subcircuit q node_id"
definition is_output_interface_node ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_output_interface_node subcircuit q node_id \<longleftrightarrow>
         output_interface subcircuit q = Some node_id
       \<and> interface_node_uses_qubit subcircuit q node_id"
definition is_first_operation_on_subcircuit_wire ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_first_operation_on_subcircuit_wire subcircuit q node_id \<longleftrightarrow>
         (\<exists>op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op))
       \<and> (get_input_node_id q, node_id)
            \<in> wire_edge_relation (subgraph subcircuit) q"
definition is_last_operation_on_subcircuit_wire ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_last_operation_on_subcircuit_wire subcircuit q node_id \<longleftrightarrow>
         (\<exists>op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op))
       \<and> (node_id, get_output_node_id q)
            \<in> wire_edge_relation (subgraph subcircuit) q"
definition subcircuit_operation_qubits ::
  "subcircuit \<Rightarrow> qubit set"
  where
    "subcircuit_operation_qubits subcircuit =
       {q.
          \<exists>node_id op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op)
          \<and> q \<in> set (op_qargs op)}"
definition is_valid_subcircuit ::
  "subcircuit \<Rightarrow> bool"
  where
    "is_valid_subcircuit subcircuit \<longleftrightarrow>
         is_valid_circuit (subgraph subcircuit)
  
       \<and> (\<forall>q.
            (input_interface subcircuit q = None)
            =
            (output_interface subcircuit q = None))
          
        \<and> (\<forall>q input_node_id.
             input_interface subcircuit q = Some input_node_id
             \<longrightarrow>
             is_first_operation_on_subcircuit_wire
               subcircuit q input_node_id)
        
        \<and> (\<forall>q output_node_id.
             output_interface subcircuit q = Some output_node_id
             \<longrightarrow>
             is_last_operation_on_subcircuit_wire
               subcircuit q output_node_id)

        \<and> subcircuit_interface_qubits subcircuit
          = subcircuit_operation_qubits subcircuit
  
       \<and> (\<forall>q input_node_id output_node_id.
            input_interface subcircuit q = Some input_node_id
            \<longrightarrow>
            output_interface subcircuit q = Some output_node_id
            \<longrightarrow>
            (input_node_id, output_node_id)
              \<in> (wire_edge_relation
                   (subgraph subcircuit) q)\<^sup>*)"
definition is_compatible_subcircuit ::
  "qubit list \<Rightarrow> subcircuit \<Rightarrow> bool"
where
  "is_compatible_subcircuit qubits subcircuit \<longleftrightarrow>
       distinct qubits
     \<and> subcircuit_interface_qubits subcircuit = set qubits
     \<and> (\<forall>q \<in> set qubits.
          input_interface subcircuit q \<noteq> None
        \<and> output_interface subcircuit q \<noteq> None)"
definition is_valid_subcircuit_replacement ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> bool"
  where
    "is_valid_subcircuit_replacement
        circuit operation_node_id subcircuit
     \<longleftrightarrow>
       (\<exists>op.
          nodes circuit operation_node_id =
            Some (OperationNode op)
        \<and> is_valid_subcircuit subcircuit
        \<and> num_qubits (subgraph subcircuit) =
            num_qubits circuit
        \<and> is_compatible_subcircuit
            (op_qargs op)
            subcircuit)"
definition operation_node_ids ::
  "quantum_circuit \<Rightarrow> node_id set"
  where
    "operation_node_ids circuit =
       {node_id.
          \<exists>op.
            nodes circuit node_id =
              Some (OperationNode op)}"
definition subcircuit_operation_node_ids ::
  "subcircuit \<Rightarrow> node_id set"
  where
    "subcircuit_operation_node_ids subcircuit =
       operation_node_ids (subgraph subcircuit)"
definition subcircuit_internal_edges ::
  "subcircuit \<Rightarrow> edge set"
  where
    "subcircuit_internal_edges subcircuit =
       {e \<in> edges (subgraph subcircuit).
          edge_source e
            \<in> subcircuit_operation_node_ids subcircuit
        \<and> edge_target e
            \<in> subcircuit_operation_node_ids subcircuit}"
definition rename_subcircuit_node_id ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> node_id"
  where
    "rename_subcircuit_node_id circuit local_node_id =
       NodeId
         (node_id_to_nat (next_id circuit)
          + node_id_to_nat local_node_id)"
definition rename_subcircuit_edge ::
  "quantum_circuit \<Rightarrow> edge \<Rightarrow> edge"
where
  "rename_subcircuit_edge circuit e =
     make_edge
       (rename_subcircuit_node_id
          circuit (edge_source e))
       (rename_subcircuit_node_id
          circuit (edge_target e))
       (edge_wire e)"
definition renamed_subcircuit_internal_edges ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> edge set"
where
  "renamed_subcircuit_internal_edges circuit subcircuit =
     rename_subcircuit_edge circuit
       ` subcircuit_internal_edges subcircuit"
definition renamed_input_interface ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> node_id option"
  where
    "renamed_input_interface circuit subcircuit q =
       map_option
         (rename_subcircuit_node_id circuit)
         (input_interface subcircuit q)"
definition renamed_output_interface ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> node_id option"
  where
    "renamed_output_interface circuit subcircuit q =
       map_option
         (rename_subcircuit_node_id circuit)
         (output_interface subcircuit q)"
lemma rename_subcircuit_node_id_injective:
  assumes renamed_equal:
    "rename_subcircuit_node_id circuit node_id1 =
     rename_subcircuit_node_id circuit node_id2"
  shows
    "node_id1 = node_id2"
  sorry
lemma renamed_subcircuit_node_id_is_unused:
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"
  shows
    "nodes circuit
       (rename_subcircuit_node_id circuit local_node_id)
     = None"
  sorry
lemma rename_subcircuit_edge_preserves_wire:
  "edge_wire (rename_subcircuit_edge circuit e) = edge_wire e"
  sorry
lemma rename_subcircuit_edge_preserves_distinct_endpoints:
  assumes distinct_endpoints:
    "edge_source e \<noteq> edge_target e"

  shows
    "edge_source (rename_subcircuit_edge circuit e)
     \<noteq>
     edge_target (rename_subcircuit_edge circuit e)"
  sorry
lemma renamed_subcircuit_internal_edge:
  assumes internal_edge:
    "e \<in> subcircuit_internal_edges subcircuit"

  shows
    "rename_subcircuit_edge circuit e
       \<in> renamed_subcircuit_internal_edges circuit subcircuit"
  sorry
lemma renamed_input_interface_node_is_unused:
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"

  and renamed_interface:
    "renamed_input_interface circuit subcircuit q =
       Some renamed_node_id"

  shows
    "nodes circuit renamed_node_id = None"
  sorry
lemma renamed_output_interface_node_is_unused:
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"

  and renamed_interface:
    "renamed_output_interface circuit subcircuit q =
       Some renamed_node_id"

  shows
    "nodes circuit renamed_node_id = None"
  sorry
lemma renamed_subcircuit_edge_source:
  "edge_source (rename_subcircuit_edge circuit e) =
     rename_subcircuit_node_id circuit (edge_source e)"
  sorry
lemma renamed_subcircuit_edge_target:
  "edge_target (rename_subcircuit_edge circuit e) =
     rename_subcircuit_node_id circuit (edge_target e)"
  sorry
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
definition connect_subcircuit_input_on_wire ::
  "quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> qubit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> quantum_circuit"
where
  "connect_subcircuit_input_on_wire
      original_circuit
      operation_node
      replacement
      q
      current_circuit =
     (case
        (predecessor_on_wire
           original_circuit
           operation_node
           q,
         renamed_input_interface
           original_circuit
           replacement
           q)
      of
        (Some predecessor, Some input_node) \<Rightarrow>
          insert_edge
            (make_edge predecessor input_node q)
            current_circuit
      | _ \<Rightarrow> current_circuit)"
definition connect_subcircuit_inputs ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
  where

    "connect_subcircuit_inputs
      original_circuit
      current_circuit
      operation_node
      replacement =
     Finite_Set.fold
       (connect_subcircuit_input_on_wire
          original_circuit
          operation_node
          replacement)
       current_circuit
       (subcircuit_interface_qubits replacement)"
lemma connect_subcircuit_input_on_wire_preserves_nodes[simp]:
  "nodes
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   nodes circuit"
  sorry
lemma connect_subcircuit_inputs_preserve_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes
       (connect_subcircuit_inputs
          original_circuit
          circuit
          operation_node
          replacement)
     =
     nodes circuit"
  sorry
lemma connect_subcircuit_input_on_wire_preserves_num_qubits[simp]:
  "num_qubits
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   num_qubits circuit"
  sorry
lemma connect_subcircuit_input_on_wire_preserves_next_id[simp]:
  "next_id
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   next_id circuit"
  sorry
lemma connect_subcircuit_input_on_wire_commute:
  "connect_subcircuit_input_on_wire
      original_circuit
      operation_node
      replacement
      q1
      (connect_subcircuit_input_on_wire
         original_circuit
         operation_node
         replacement
         q2
         circuit)
   =
   connect_subcircuit_input_on_wire
      original_circuit
      operation_node
      replacement
      q2
      (connect_subcircuit_input_on_wire
         original_circuit
         operation_node
         replacement
         q1
         circuit)"
  sorry
interpretation connect_subcircuit_input:
  comp_fun_commute
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement"
  sorry
lemma compatible_subcircuit_interface_qubits_finite:
  assumes compatible:
    "is_compatible_subcircuit qubits replacement"

  shows
    "finite (subcircuit_interface_qubits replacement)"
  sorry
lemma connect_subcircuit_inputs_preserves_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes
       (connect_subcircuit_inputs
          original_circuit
          current_circuit
          operation_node
          replacement)
     =
     nodes current_circuit"
  sorry
definition connect_subcircuit_output_on_wire ::
  "quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> qubit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> quantum_circuit"
  where
  "connect_subcircuit_output_on_wire
      original_circuit
      operation_node
      replacement
      q
      current_circuit =
     (case
        (successor_on_wire
           original_circuit
           operation_node
           q,
         renamed_output_interface
           original_circuit
           replacement
           q)
      of
        (Some successor, Some output_node) \<Rightarrow>
          insert_edge
            (make_edge output_node successor q)
            current_circuit
      | _ \<Rightarrow> current_circuit)"
definition connect_subcircuit_outputs ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
  where
    "connect_subcircuit_outputs
      original_circuit
      current_circuit
      operation_node
      replacement =
     Finite_Set.fold
       (connect_subcircuit_output_on_wire
          original_circuit
          operation_node
          replacement)
       current_circuit
       (subcircuit_interface_qubits replacement)"
lemma connect_subcircuit_output_on_wire_preserves_nodes[simp]:
  "nodes
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   nodes circuit"
  sorry
lemma connect_subcircuit_outputs_preserve_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes
       (connect_subcircuit_outputs
          original_circuit circuit operation_node replacement)
     =
     nodes circuit"
  sorry
lemma connect_subcircuit_output_on_wire_preserves_num_qubits[simp]:
  "num_qubits
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   num_qubits circuit"
  sorry
lemma connect_subcircuit_output_on_wire_preserves_next_id[simp]:
  "next_id
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   next_id circuit"
  sorry
lemma connect_subcircuit_output_on_wire_commute:
  "connect_subcircuit_output_on_wire
      original_circuit
      operation_node
      replacement
      q1
      (connect_subcircuit_output_on_wire
         original_circuit
         operation_node
         replacement
         q2
         circuit)
   =
   connect_subcircuit_output_on_wire
      original_circuit
      operation_node
      replacement
      q2
      (connect_subcircuit_output_on_wire
         original_circuit
         operation_node
         replacement
         q1
         circuit)"
  sorry
interpretation connect_subcircuit_output:
  comp_fun_commute
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement"
  sorry
lemma connect_subcircuit_outputs_preserves_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes
       (connect_subcircuit_outputs
          original_circuit
          current_circuit
          operation_node
          replacement)
     =
     nodes current_circuit"
  sorry
definition update_frontier_after_subcircuit ::
  "quantum_circuit
    \<Rightarrow> frontier
    \<Rightarrow> subcircuit
    \<Rightarrow> frontier"
where
  "update_frontier_after_subcircuit
      original_circuit
      current_frontier
      replacement =
     (\<lambda>q.
        case
          renamed_output_interface
            original_circuit
            replacement
            q
        of
          Some output_node \<Rightarrow> output_node
        | None \<Rightarrow> current_frontier q)"
lemma update_frontier_after_subcircuit_with_output:
  assumes renamed_output:
    "renamed_output_interface
       original_circuit
       replacement
       q
     =
     Some output_node"

  shows
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     output_node"
  sorry
lemma update_frontier_after_subcircuit_without_output:
  assumes no_renamed_output:
    "renamed_output_interface
       original_circuit
       replacement
       q
     =
     None"

  shows
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     current_frontier q"
  sorry
lemma update_frontier_after_subcircuit_output_interface:
  assumes output_interface:
    "output_interface replacement q = Some local_output_node"

  shows
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     rename_subcircuit_node_id
       original_circuit
       local_output_node"
  sorry
lemma update_frontier_after_subcircuit_no_output_interface:
  assumes no_output_interface:
    "output_interface replacement q = None"

  shows
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     current_frontier q"
  sorry
definition replace_operation_by_subcircuit ::
  "quantum_circuit
    \<Rightarrow> frontier
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit \<times> frontier"
where
  "replace_operation_by_subcircuit
      circuit
      frontier
      operation_node
      subcircuit =
     (let
        circuit1 =
          remove_operation_node
            circuit
            operation_node;

       circuit2 =
          insert_subcircuit_nodes
            circuit
            circuit1
            subcircuit;

       circuit3 =
          insert_subcircuit_internal_edges
            circuit
            circuit2
            subcircuit;

       circuit4 =
          connect_subcircuit_inputs
            circuit
            circuit3
            operation_node
            subcircuit;
        
       circuit5 =
          connect_subcircuit_outputs
            circuit
            circuit4
            operation_node
            subcircuit;

       frontier' =
          update_frontier_after_subcircuit
            circuit
            frontier
            subcircuit

      in
        (circuit5
           \<lparr>
             next_id :=
               NodeId
                 (node_id_to_nat (next_id circuit)
                  +
                  node_id_to_nat
                    (next_id (subgraph subcircuit)))
           \<rparr>, \<comment>\<open> The intermediate helpers preserve next_id so that the original allocation boundary can be used consistently for every renaming. Once all replacement nodes and edges have been installed, advance next_id beyond the copied local node namespace. \<close>
         frontier'))"
lemma replace_operation_by_subcircuit_next_id[simp]:
  "next_id
      (fst
        (replace_operation_by_subcircuit
           circuit
           frontier
           operation_node
           replacement))
   =
   NodeId
     (node_id_to_nat (next_id circuit)
      +
      node_id_to_nat
        (next_id (subgraph replacement)))"
  sorry
lemma replace_operation_by_subcircuit_frontier[simp]:
  "snd
      (replace_operation_by_subcircuit
         circuit
         frontier
         operation_node
         replacement)
   =
   update_frontier_after_subcircuit
     circuit
     frontier
     replacement"
  sorry
lemma replace_operation_by_subcircuit_removes_old_operation:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))
       operation_node_id
     = None"
  sorry
lemma replace_operation_by_subcircuit_contains_renamed_nodes:

  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  assumes local_operation:
    "nodes (subgraph replacement) local_node_id =
       Some (OperationNode op)"

  assumes allocated_local_node:
    "local_node_id
       \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))
       (rename_subcircuit_node_id
          original_circuit
          local_node_id)
     =
     Some (OperationNode op)"
  sorry
lemma replace_operation_by_subcircuit_preserves_unrelated_nodes:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  assumes original_node:
    "nodes circuit other_node_id = Some node"

  shows
    "nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))
       other_node_id
     =
     Some node"
  sorry
lemma replace_operation_by_subcircuit_contains_renamed_internal_edges:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes internal_edge:
    "e \<in> subcircuit_internal_edges replacement"

  shows
    "rename_subcircuit_edge original_circuit e
       \<in>
       edges
         (fst
           (replace_operation_by_subcircuit
              original_circuit
              frontier
              operation_node_id
              replacement))"
  sorry
lemma replace_operation_by_subcircuit_connects_inputs:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes predecessor:
    "predecessor_on_wire
       original_circuit
       operation_node_id
       q
     =
     Some predecessor_node"

  assumes input_interface:
    "input_interface replacement q = Some local_input_node"

  shows
    "make_edge
       predecessor_node
       (rename_subcircuit_node_id
          original_circuit
          local_input_node)
       q
     \<in>
     edges
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))"
  sorry
lemma replace_operation_by_subcircuit_connects_outputs:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes successor:
    "successor_on_wire
       original_circuit
       operation_node_id
       q
     =
     Some successor_node"

  assumes output_interface:
    "output_interface replacement q = Some local_output_node"

  shows
    "make_edge
       (rename_subcircuit_node_id
          original_circuit
          local_output_node)
       successor_node
       q
     \<in>
     edges
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))"
  sorry
lemma replace_operation_by_subcircuit_preserves_unrelated_edges:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes unrelated_edge:
    "e \<in> edges original_circuit"

  assumes source_not_removed:
    "edge_source e \<noteq> operation_node_id"

  assumes target_not_removed:
    "edge_target e \<noteq> operation_node_id"

  shows
    "e \<in>
      edges
        (fst
          (replace_operation_by_subcircuit
             original_circuit
             frontier
             operation_node_id
             replacement))"
  sorry
lemma replace_operation_by_subcircuit_node_cases:
  assumes valid_state:
    "is_valid_construction_state original_circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes node_in_result:
    "nodes
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))
       node_id
     =
     Some node"

  shows
    "(node_id \<noteq> operation_node_id
      \<and> nodes original_circuit node_id = Some node)
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
lemma replace_operation_by_subcircuit_edge_cases:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes edge_in_result:
    "e \<in>
       edges
         (fst
           (replace_operation_by_subcircuit
              original_circuit
              frontier
              operation_node_id
              replacement))"

  shows
    "(e \<in> edges original_circuit
      \<and> edge_source e \<noteq> operation_node_id
      \<and> edge_target e \<noteq> operation_node_id)

     \<or>

     e \<in> renamed_subcircuit_internal_edges
              original_circuit
              replacement

     \<or>

     (\<exists>q predecessor_node renamed_input_node.
        q \<in> subcircuit_interface_qubits replacement
        \<and>
        predecessor_on_wire
          original_circuit
          operation_node_id
          q
        =
        Some predecessor_node
        \<and>
        renamed_input_interface
          original_circuit
          replacement
          q
        =
        Some renamed_input_node
        \<and>
        e =
          make_edge
            predecessor_node
            renamed_input_node
            q)

     \<or>

     (\<exists>q renamed_output_node successor_node.
        q \<in> subcircuit_interface_qubits replacement
        \<and>
        renamed_output_interface
          original_circuit
          replacement
          q
        =
        Some renamed_output_node
        \<and>
        successor_on_wire
          original_circuit
          operation_node_id
          q
        =
        Some successor_node
        \<and>
        e =
          make_edge
            renamed_output_node
            successor_node
            q)"
  sorry
lemma replace_operation_by_subcircuit_preserves_boundary_nodes:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "are_well_formed_boundary_nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
  sorry
lemma replace_operation_by_subcircuit_preserves_well_formed_operation_nodes:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "are_well_formed_operation_nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
  sorry
lemma valid_subcircuit_input_interface_uses_qubit:
  assumes valid_subcircuit:
    "is_valid_subcircuit replacement"

  assumes input_interface:
    "input_interface replacement q = Some node_id"

  assumes operation_node:
    "nodes
       (subgraph replacement)
       node_id
     =
     Some (OperationNode op)"

  shows
    "q \<in> set (op_qargs op)"
  sorry
lemma valid_subcircuit_output_interface_uses_qubit:
  assumes valid_subcircuit:
    "is_valid_subcircuit replacement"

  assumes output_interface:
    "output_interface replacement q = Some node_id"

  assumes operation_node:
    "nodes
       (subgraph replacement)
       node_id
     =
     Some (OperationNode op)"

  shows
    "q \<in> set (op_qargs op)"
  sorry
lemma replace_operation_by_subcircuit_preserves_well_formed_edges:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes acyclic_circuit:
    "is_acyclic_circuit circuit"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "are_well_formed_edges
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
  sorry
lemma replace_operation_by_subcircuit_preserves_well_formed_circuit:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes acyclic_circuit:
    "is_acyclic_circuit circuit"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "is_well_formed_circuit
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
  sorry
lemma valid_subcircuit_replacement_is_acyclic:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "is_acyclic_circuit (subgraph replacement)"
  sorry
lemma injective_renaming_trancl_reflects_cycle:
  assumes rename_injective:
    "inj rename"

  assumes renamed_cycle:
    "(renamed_node, renamed_node)
       \<in>
       {(rename source, rename target) |
          source target.
          (source, target) \<in> relation}\<^sup>+"

  shows
    "\<exists>local_node.
       (local_node, local_node) \<in> relation\<^sup>+"
  sorry
lemma renamed_internal_cycle_implies_subcircuit_cycle:
  assumes internal_cycle:
    "(renamed_node, renamed_node)
       \<in>
       {(edge_source e, edge_target e) |
          e.
          e \<in>
            renamed_subcircuit_internal_edges
              circuit
              replacement}\<^sup>+"

  shows
    "\<exists>local_node.
       (local_node, local_node)
         \<in>
         (edge_relation (subgraph replacement))\<^sup>+"
  sorry
lemma replacement_cycle_internal_or_original:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  assumes result_cycle:
    "(node, node)
       \<in>
       (edge_relation
          (fst
            (replace_operation_by_subcircuit
               circuit
               frontier
               operation_node_id
               replacement)))\<^sup>+"

  shows
    "(\<exists>original_node.
        (original_node, original_node)
          \<in> (edge_relation circuit)\<^sup>+)
     \<or>
     (\<exists>renamed_node.
        (renamed_node, renamed_node)
          \<in>
          {(edge_source e, edge_target e) |
             e.
             e \<in>
               renamed_subcircuit_internal_edges
                 circuit
                 replacement}\<^sup>+)"
  sorry
lemma replacement_cycle_cases:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes result_cycle:
    "(node, node)
       \<in>
       (edge_relation
          (fst
            (replace_operation_by_subcircuit
               circuit
               frontier
               operation_node_id
               replacement)))\<^sup>+"

  shows
    "(\<exists>original_node.
        (original_node, original_node)
          \<in> (edge_relation circuit)\<^sup>+)
     \<or>
     (\<exists>replacement_node.
        (replacement_node, replacement_node)
          \<in>
          (edge_relation (subgraph replacement))\<^sup>+)"
  sorry
lemma replace_operation_by_subcircuit_preserves_acyclicity:

  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes original_acyclic:
    "is_acyclic_circuit circuit"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "is_acyclic_circuit
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
  sorry

end
