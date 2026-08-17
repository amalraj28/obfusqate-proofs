theory Quantum_Circuit_Subcircuit_Replace_Acyclicity
  imports Quantum_Circuit_Subcircuit_Replace_Core

begin



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
