theory Quantum_Circuit_Wire_Splice
  imports Quantum_Circuit_Construction

begin



definition splice_wire_without_updating_frontier ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> quantum_circuit" where
  "splice_wire_without_updating_frontier circuit frontier q new_node_id =
     (let old_node_id = frontier q;
          out_node_id = get_output_node_id q;
          old_edge = make_edge old_node_id out_node_id q;
          new_in_edge = make_edge old_node_id new_node_id q;
          new_out_edge = make_edge new_node_id out_node_id q
      in
        insert_edge new_out_edge
          (insert_edge new_in_edge
            (delete_edge old_edge circuit)))"

definition splice_wire ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> quantum_circuit \<times> frontier"
  where
    "splice_wire circuit frontier q new_node_id = (
         splice_wire_without_updating_frontier circuit frontier q new_node_id,
         update_frontier frontier q new_node_id
  )"

lemma fst_splice_wire:
  "fst (splice_wire circuit frontier q new_node_id) =
   splice_wire_without_updating_frontier circuit frontier q new_node_id"
  sorry

lemma snd_splice_wire:
  "snd (splice_wire circuit frontier q new_node_id) =
   update_frontier frontier q new_node_id"
  sorry

lemma edges_splice_wire_without_updating_frontier:
  "edges
      (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
   =
   insert
      (make_edge new_node_id (get_output_node_id q) q)
      (insert
          (make_edge (frontier q) new_node_id q)
          (edges circuit -
             {make_edge
                (frontier q)
                (get_output_node_id q)
                q}))"
  sorry

lemma splice_wire_contains_new_output_edge:
  "make_edge
      new_node_id
      (get_output_node_id q)
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  sorry

lemma splice_wire_contains_new_input_edge:
  "make_edge
      (frontier q)
      new_node_id
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  sorry

lemma splice_wire_preserves_output_edge_on_other_wire:
  assumes different_wires:
    "other_q \<noteq> q"

assumes old_output_edge_exists:
  "make_edge
       (frontier other_q)
       (get_output_node_id other_q)
       other_q
     \<in> edges circuit"

shows
  "make_edge
       (frontier other_q)
       (get_output_node_id other_q)
       other_q
     \<in> edges
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)"

  sorry

lemma splice_wire_preserves_nodes[simp]:
  "nodes (fst (splice_wire circuit frontier q new_node_id)) node_id = nodes circuit node_id"
  sorry

lemma splice_wire_without_updating_frontier_preserves_num_qubits[simp]:
  "num_qubits 
     (splice_wire_without_updating_frontier circuit frontier q new_node_id)
   =
   num_qubits circuit"
  sorry

lemma splice_wire_preserves_num_qubits[simp]:
  "num_qubits (fst (splice_wire circuit frontier q new_node_id)) = num_qubits circuit"
  sorry

lemma splice_wire_preserves_other_wire_relation:
  assumes "q \<noteq> current_wire"
  shows
    "wire_edge_relation
       (fst
         (splice_wire
           circuit frontier current_wire new_node_id))
       q
     =
     wire_edge_relation circuit q"

  sorry

lemma splice_wire_preserves_valid_frontier:

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

assumes new_node_exists:
  "nodes circuit new_node_id = Some new_node"

assumes new_node_uses_wire:
  "node_uses_qubit new_node q"

assumes new_node_not_frontier:
  "new_node_id \<noteq> frontier q"

assumes new_node_has_no_other_successor:
  "\<And>successor_id.
       (new_node_id, successor_id)
         \<in> wire_edge_relation circuit q
       \<Longrightarrow> successor_id = get_output_node_id q"

shows
  "is_valid_frontier
       (fst (splice_wire circuit frontier q new_node_id))
       (snd (splice_wire circuit frontier q new_node_id))"

sorry

lemma wire_edge_relation_update_next_id[simp]:
  "wire_edge_relation (circuit\<lparr>next_id := new_next_id\<rparr>) q
   =
   wire_edge_relation circuit q"

  sorry

lemma wire_edge_relation_after_splice_same_wire:
  "wire_edge_relation
     (splice_wire_without_updating_frontier
      circuit frontier q new_node_id)
     q
   =
   (wire_edge_relation circuit q
      - {(frontier q, get_output_node_id q)})
      \<union> {(frontier q, new_node_id),
      (new_node_id, get_output_node_id q)}"

sorry

lemma wire_edge_relation_after_splice_other_wire:
  assumes different_wire:
    "other_q \<noteq> q"

shows
  "wire_edge_relation
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       other_q
     =
     wire_edge_relation circuit other_q"

sorry

lemma old_wire_edge_reaches_after_splice:
  assumes old_edge:
    "(source_id, target_id)
       \<in> wire_edge_relation circuit q"

shows
  "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       source_id
       target_id"

sorry

lemma old_wire_reaches_after_splice:
  assumes old_reachability:
    "wire_reaches circuit q source_id target_id"

shows
  "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       source_id
       target_id"

sorry

lemma old_nodes_comparable_after_splice:
  assumes old_nodes_comparable:
    "nodes_comparable_on_wire circuit q"

assumes node_a_lookup:
  "nodes circuit node_a = Some node_a_value"

assumes node_b_lookup:
  "nodes circuit node_b = Some node_b_value"

assumes node_a_uses_q:
  "node_uses_qubit node_a_value q"

assumes node_b_uses_q:
  "node_uses_qubit node_b_value q"

shows
  "node_a = node_b
     \<or> wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_a node_b
     \<or> wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_b node_a"

sorry

end
