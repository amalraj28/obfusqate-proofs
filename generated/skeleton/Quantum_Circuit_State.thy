theory Quantum_Circuit_State
  imports Quantum_Circuit_Graph

begin

definition increment_node_id :: "node_id \<Rightarrow> node_id" where
  "increment_node_id current_node_id = NodeId (node_id_to_nat current_node_id + 1)"
lemma node_id_to_nat_increment_node_id[simp]:
  "node_id_to_nat (increment_node_id current_node_id) = node_id_to_nat current_node_id + 1"
  sorry
lemma increment_node_id_not_same[simp]:
  "increment_node_id current_node_id \<noteq> current_node_id"
  sorry
type_synonym frontier = "qubit \<Rightarrow> node_id"
definition initial_frontier :: frontier where
  "initial_frontier q = get_input_node_id q"
definition update_frontier :: "frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> frontier" where
  "update_frontier frontier q new_node_id = frontier(q := new_node_id)"
lemma update_frontier_same[simp]:
  "update_frontier frontier q new_node_id q = new_node_id"
  sorry
lemma update_frontier_other[simp]:
  assumes "other_q \<noteq> q"
  shows
    "update_frontier frontier q new_node_id other_q =
     frontier other_q"
  sorry
definition is_valid_frontier :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  "is_valid_frontier circuit frontier \<longleftrightarrow>
     (\<forall>q.
        qubit_in_circuit circuit q \<longrightarrow>
        (\<exists>frontier_node.
           nodes circuit (frontier q) = Some frontier_node
         \<and> node_uses_qubit frontier_node q
         \<and> make_edge
             (frontier q)
             (get_output_node_id q)
             q
           \<in> edges circuit
         \<and> has_unique_wire_successor
             circuit q (frontier q)))"
definition next_id_is_unused :: "quantum_circuit \<Rightarrow> bool" where
  "next_id_is_unused circuit \<longleftrightarrow> nodes circuit (next_id circuit) = None"
definition all_existing_node_ids_below_next_id ::
  "quantum_circuit \<Rightarrow> bool"
  where
    "all_existing_node_ids_below_next_id circuit \<longleftrightarrow>
     (\<forall>existing_node_id.
        nodes circuit existing_node_id \<noteq> None
        \<longrightarrow>
        node_id_to_nat existing_node_id
          < node_id_to_nat (next_id circuit))"
definition is_valid_construction_state :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  "is_valid_construction_state circuit frontier \<longleftrightarrow>
      is_well_formed_circuit circuit
        \<and> is_valid_frontier circuit frontier
        \<and> next_id_is_unused circuit
        \<and> all_existing_node_ids_below_next_id circuit"
definition insert_node :: "node_id \<Rightarrow> circuit_node \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  "insert_node node_id new_node circuit =
     circuit\<lparr>nodes := (nodes circuit)(node_id := Some new_node)\<rparr>"
definition insert_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  "insert_edge e circuit =
     circuit\<lparr>edges := insert e (edges circuit)\<rparr>"
definition delete_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  "delete_edge e circuit =
     circuit\<lparr>edges := edges circuit - {e}\<rparr>"
lemma nodes_insert_node_same[simp]:
  "nodes (insert_node node_id node circuit) node_id = Some node"
  sorry
lemma valid_frontier_has_unique_successor:
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

assumes valid_q:
  "qubit_in_circuit circuit q"

shows
  "has_unique_wire_successor circuit q (frontier q)"
  sorry
lemma nodes_insert_node_other[simp]:
  assumes "other_node_id \<noteq> node_id"
  shows "nodes (insert_node node_id node circuit) other_node_id =
         nodes circuit other_node_id"
  sorry
lemma insert_node_at_unused_id_preserves_valid_frontier:
  assumes valid_frontier: "is_valid_frontier circuit frontier"

assumes node_id_unused: "nodes circuit new_node_id = None"

shows
  "is_valid_frontier 
         (insert_node new_node_id new_node circuit)
         frontier"
  sorry
lemma update_next_id_preserves_valid_frontier:

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

shows 
  "is_valid_frontier (circuit \<lparr> next_id := new_next_id \<rparr>) frontier"
  sorry
lemma edges_insert_edge[simp]:
  "edges (insert_edge e circuit) = insert e (edges circuit)"
  sorry
lemma edges_delete_edge[simp]:
  "edges (delete_edge e circuit) = edges circuit - {e}"
  sorry
lemma initial_frontier_is_valid:
  "is_valid_frontier (initial_circuit number_of_qubits) initial_frontier"
  sorry
lemma initial_next_id_is_unused:
  "next_id_is_unused (initial_circuit number_of_qubits)"
  sorry
lemma initial_existing_node_ids_are_below_next_id:
  "all_existing_node_ids_below_next_id (initial_circuit number_of_qubits)"
  sorry

end
