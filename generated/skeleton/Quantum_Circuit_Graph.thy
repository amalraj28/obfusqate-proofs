theory Quantum_Circuit_Graph
  imports Quantum_Circuit_Model

begin





definition node_exists :: "quantum_circuit \<Rightarrow> node_id \<Rightarrow> bool" where
  "node_exists circuit node_id \<longleftrightarrow>
     nodes circuit node_id \<noteq> None
  "

fun node_uses_qubit :: "circuit_node \<Rightarrow> qubit \<Rightarrow> bool" where
  "node_uses_qubit (InputNode q) r = (q = r)"
| "node_uses_qubit (OutputNode q) r = (q = r)"
| "node_uses_qubit (OperationNode op) r = (r \<in> set (op_qargs op))"



definition qubit_in_circuit :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> bool" where
  "qubit_in_circuit circuit q \<longleftrightarrow>
     get_qubit_index q < num_qubits circuit"

definition is_well_formed_edge :: "quantum_circuit \<Rightarrow> edge \<Rightarrow> bool" where
  "is_well_formed_edge circuit e \<longleftrightarrow>
      node_exists circuit (edge_source e)
    \<and> node_exists circuit (edge_target e)
    \<and> qubit_in_circuit circuit (edge_wire e)
    \<and> (
        case nodes circuit (edge_source e) of
          Some source_node \<Rightarrow> node_uses_qubit source_node (edge_wire e)
          | None \<Rightarrow> False
      )
    \<and> (
        case nodes circuit (edge_target e) of
          Some target_node \<Rightarrow> node_uses_qubit target_node (edge_wire e)
          | None \<Rightarrow> False
      )
  "

definition are_well_formed_edges :: "quantum_circuit \<Rightarrow> bool" where
  "are_well_formed_edges circuit \<longleftrightarrow>
     (\<forall>e \<in> edges circuit. is_well_formed_edge circuit e
     )
  "

definition edge_relation :: "quantum_circuit \<Rightarrow> (node_id \<times> node_id) set" where
  "edge_relation circuit =
     {(source_id, target_id).
        \<exists>e \<in> edges circuit.
          edge_source e = source_id
        \<and> edge_target e = target_id}"

definition is_acyclic_circuit :: "quantum_circuit \<Rightarrow> bool" where
  "is_acyclic_circuit circuit \<longleftrightarrow> acyclic (edge_relation circuit)"

definition wire_edge_relation :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> (node_id \<times> node_id) set" where
  "wire_edge_relation circuit q =
     {(source_id, target_id).
        make_edge source_id target_id q \<in> edges circuit}"

definition wire_reaches :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> node_id \<Rightarrow> bool" where
  \<comment>\<open> node_a reaches node_b along wire q when there is a non-empty
     directed path of q-labelled edges from node_a to node_b.

     The transitive closure (^+) (means one or more edges) is used rather than the reflexive
     transitive closure (^*) because a node should not count as being
     strictly before itself.\<close>

"wire_reaches circuit q node_a node_b \<longleftrightarrow>
     (node_a, node_b) \<in> (wire_edge_relation circuit q)^+"

definition has_unique_wire_predecessor :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool" where
  "has_unique_wire_predecessor circuit q node_id \<longleftrightarrow>
     (\<exists>! predecessor_id. \<comment>\<open>\<exists>! means exactly one\<close>
        (predecessor_id, node_id)
          \<in> wire_edge_relation circuit q)"

definition has_unique_wire_successor :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool" where
  "has_unique_wire_successor circuit q node_id \<longleftrightarrow>
     (\<exists>! successor_id. \<comment>\<open>\<exists>! means exactly one\<close>
        (node_id, successor_id)
          \<in> wire_edge_relation circuit q)"

lemma wire_edge_implies_wire_reaches:
  assumes direct_edge:
    "(source_id, target_id) \<in> wire_edge_relation circuit q"

shows
  "wire_reaches circuit q source_id target_id"

  sorry



definition nodes_comparable_on_wire :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> bool" where
  "nodes_comparable_on_wire circuit q \<longleftrightarrow>
     (\<forall>node_a node_b node_a_value node_b_value.
        nodes circuit node_a = Some node_a_value
        \<longrightarrow> nodes circuit node_b = Some node_b_value
        \<longrightarrow> node_uses_qubit node_a_value q
        \<longrightarrow> node_uses_qubit node_b_value q
        \<longrightarrow> (
             node_a = node_b
           \<or> wire_reaches circuit q node_a node_b
           \<or> wire_reaches circuit q node_b node_a
           ))"

definition wire_is_linear :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> bool" where
  "wire_is_linear circuit q \<longleftrightarrow>
       nodes_comparable_on_wire circuit q \<comment>\<open>This means that for any two existing nodes using q, one must occur before the other along q, unless they are the same node\<close>

     \<and> (\<nexists>predecessor_id. 
         (predecessor_id, get_input_node_id q)
              \<in> wire_edge_relation circuit q) \<comment>\<open>There does not exist a node with an edge into the input node on wire q\<close>

     \<and> has_unique_wire_successor
         circuit q (get_input_node_id q) \<comment> \<open>Exactly one node immediately follows the input node on wire q (no branching)\<close>

     \<and> has_unique_wire_predecessor
         circuit q (get_output_node_id q)  \<comment> \<open>Exactly one node immediately precedes the output boundary node on wire q\<close>

     \<and> (\<nexists>successor_id.
            (get_output_node_id q, successor_id)
              \<in> wire_edge_relation circuit q) \<comment> \<open>No q-labelled edge leaves the output node\<close>

     \<and> (\<forall>node_id op.
          nodes circuit node_id = Some (OperationNode op)
          \<longrightarrow> node_uses_qubit (OperationNode op) q
          \<longrightarrow> has_unique_wire_predecessor circuit q node_id
          \<and> has_unique_wire_successor circuit q node_id)" \<comment> \<open>If the operation node uses q, it must have exactly one incoming q-edge and exactly one outgoing q-edge\<close>

definition all_wires_linear :: "quantum_circuit \<Rightarrow> bool" where
  "all_wires_linear circuit \<longleftrightarrow>
     (\<forall>q.
        qubit_in_circuit circuit q
        \<longrightarrow> wire_is_linear circuit q)"

definition all_wire_nodes_comparable :: "quantum_circuit \<Rightarrow> bool" where
  "all_wire_nodes_comparable circuit \<longleftrightarrow>
     (\<forall>q.
        qubit_in_circuit circuit q
        \<longrightarrow> nodes_comparable_on_wire circuit q)"

lemma initial_circuit_nodes_comparable_on_wire:
  assumes valid_qubit:
    "qubit_in_circuit (initial_circuit number_of_qubits) q"
  shows
    "nodes_comparable_on_wire
       (initial_circuit number_of_qubits)
       q"
  sorry

lemma initial_circuit_all_wire_nodes_comparable:
  "all_wire_nodes_comparable
     (initial_circuit number_of_qubits)"

  sorry

definition operation_in_circuit :: "quantum_circuit \<Rightarrow> operation \<Rightarrow> bool" where
  "operation_in_circuit circuit op \<longleftrightarrow>
      is_valid_operation op
    \<and> (\<forall>q \<in> set (op_qargs op). qubit_in_circuit circuit q)
  "

definition are_well_formed_operation_nodes :: "quantum_circuit \<Rightarrow> bool" where
  "are_well_formed_operation_nodes circuit \<longleftrightarrow>
     (\<forall>node_id op.
        nodes circuit node_id = Some (OperationNode op) \<longrightarrow>
        operation_in_circuit circuit op
     )
  "


definition are_well_formed_boundary_nodes :: "quantum_circuit \<Rightarrow> bool" where

"are_well_formed_boundary_nodes circuit \<longleftrightarrow>
     (
        \<forall>qubit_number < num_qubits circuit.
          nodes circuit (get_input_node_id (Qubit qubit_number))
            = Some (InputNode (Qubit qubit_number))
        \<and> nodes circuit (get_output_node_id (Qubit qubit_number))
            = Some (OutputNode (Qubit qubit_number))
     )
  "

definition is_well_formed_circuit :: "quantum_circuit \<Rightarrow> bool" where
  "is_well_formed_circuit circuit \<longleftrightarrow>
       are_well_formed_boundary_nodes circuit
     \<and> are_well_formed_edges circuit
     \<and> are_well_formed_operation_nodes circuit
  "

definition is_valid_circuit :: "quantum_circuit \<Rightarrow> bool" where
  "is_valid_circuit circuit \<longleftrightarrow>
      is_well_formed_circuit circuit
    \<and> is_acyclic_circuit circuit
    \<and> all_wires_linear circuit"

lemma initial_edges_cases:
  assumes "e \<in> edges (initial_circuit number_of_qubits)"
  obtains qubit_number where
    "qubit_number < number_of_qubits"
    "e = make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)"
  sorry

lemma initial_edge_relation_cases:
  assumes relation_pair:
    "(source_id, target_id) \<in> edge_relation (initial_circuit number_of_qubits)"

obtains qubit_number where
  "qubit_number < number_of_qubits"
  "source_id = get_input_node_id (Qubit qubit_number)"
  "target_id = get_output_node_id (Qubit qubit_number)"

sorry

lemma initial_edge_relation_cannot_compose:
  assumes first_edge:
    "(first_source, middle_node)
       \<in> edge_relation (initial_circuit number_of_qubits)"

assumes second_edge:
  "(middle_node, second_target)
       \<in> edge_relation (initial_circuit number_of_qubits)"

shows False

sorry

lemma initial_circuit_has_no_operation_nodes:
  "nodes (initial_circuit number_of_qubits) node_id \<noteq> Some (OperationNode op)"
  sorry

lemma initial_circuit_is_well_formed:
  "is_well_formed_circuit (initial_circuit number_of_qubits)"

sorry

lemma initial_circuit_is_acyclic:
  "is_acyclic_circuit (initial_circuit number_of_qubits)"

sorry

lemma initial_circuit_has_linear_wires:
  "all_wires_linear (initial_circuit number_of_qubits)"
  sorry

end
