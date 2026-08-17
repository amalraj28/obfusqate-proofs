theory Quantum_Circuit_Subcircuit_Replace_Core
  imports Quantum_Circuit_Subcircuit_Connect

begin


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

end
