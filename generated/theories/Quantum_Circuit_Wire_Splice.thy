theory Quantum_Circuit_Wire_Splice
  imports Quantum_Circuit_Construction

begin

definition splice_wire_without_updating_frontier ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> quantum_circuit" where
  (* Insert new_node_id on wire q between the current frontier node and the output node. Does not update frontier, for sake of simplicity *)
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
    (* Insert new_node_id on wire q and update the frontier for q in the same step. *)
    "splice_wire circuit frontier q new_node_id = (
         splice_wire_without_updating_frontier circuit frontier q new_node_id,
         update_frontier frontier q new_node_id
  )"

lemma fst_splice_wire:
  (* Says that the first part of splice_wire response is the updated circuit *)
  "fst (splice_wire circuit frontier q new_node_id) =
   splice_wire_without_updating_frontier circuit frontier q new_node_id"
  unfolding splice_wire_def
  by simp

lemma snd_splice_wire:
  (* Says that the second part of splice_wire response is the updated frontier map *)
  "snd (splice_wire circuit frontier q new_node_id) =
   update_frontier frontier q new_node_id"
  unfolding splice_wire_def
  by simp

lemma edges_splice_wire_without_updating_frontier:
  (* The edge set after splicing is obtained by removing the old edge
     from the current frontier to the output node and inserting the two
     new edges through the newly inserted operation node. *)
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
  unfolding splice_wire_without_updating_frontier_def Let_def
  by simp

lemma splice_wire_contains_new_output_edge:
  (* After splicing new_node_id into wire q, the resulting circuit
     contains the new edge from new_node_id to the output node of q. *)
  "make_edge
      new_node_id
      (get_output_node_id q)
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  unfolding splice_wire_without_updating_frontier_def Let_def
  by simp

lemma splice_wire_contains_new_input_edge:
  (* After splicing new_node_id into wire q, the resulting circuit
     contains the new edge from previous frontier node to new_node_id *)
  "make_edge
      (frontier q)
      new_node_id
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  unfolding splice_wire_without_updating_frontier_def Let_def
  by simp

lemma splice_wire_preserves_output_edge_on_other_wire:
  (* Splicing wire q does not remove the final frontier-to-output edge belonging to a different wire "other_q".

     The only edge removed by the splice has wire label q. Since other_q and q are different, the other wire's edge cannot be the removed edge and therefore remains in the updated circuit.  *)
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

  using assms
  by (simp add: edges_splice_wire_without_updating_frontier make_edge_def)

lemma splice_wire_preserves_nodes[simp]:
  (* Splicing a single wire only modifies the edge set and the frontier. The node table remains unchanged. *)
  "nodes (fst (splice_wire circuit frontier q new_node_id)) node_id = nodes circuit node_id"
  unfolding 
    splice_wire_def
    splice_wire_without_updating_frontier_def
    insert_edge_def 
    delete_edge_def
    Let_def
  by simp

lemma splice_wire_without_updating_frontier_preserves_num_qubits[simp]:
  (* Rewiring one qubit wire without updating the frontier changes only the circuit's edges field. The number of qubits remains unchanged. *)
  "num_qubits 
     (splice_wire_without_updating_frontier circuit frontier q new_node_id)
   =
   num_qubits circuit"
  unfolding
    splice_wire_without_updating_frontier_def
    insert_edge_def
    delete_edge_def
    Let_def
  by simp

lemma splice_wire_preserves_num_qubits[simp]:
  (* Splicing a single wire only modifies the edge set and the frontier. The number of qubits remain unchanged *)
  "num_qubits (fst (splice_wire circuit frontier q new_node_id)) = num_qubits circuit"
  unfolding splice_wire_def
  by simp

lemma splice_wire_preserves_other_wire_relation:
  (* Splicing current_wire changes only edges labelled current_wire.
     Therefore, the edge relation of a distinct wire q is unchanged. *)
  assumes "q \<noteq> current_wire"
  shows
    "wire_edge_relation
       (fst
         (splice_wire
           circuit frontier current_wire new_node_id))
       q
     =
     wire_edge_relation circuit q"

  using assms
  unfolding
    wire_edge_relation_def
    splice_wire_def
    splice_wire_without_updating_frontier_def
    insert_edge_def
    delete_edge_def
    make_edge_def
    Let_def
  by simp

lemma splice_wire_preserves_valid_frontier:
  (* Splicing an existing node into a valid qubit wire preserves the
     frontier invariant, provided the inserted node belongs to that wire. *)

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

assumes new_node_exists:
  "nodes circuit new_node_id = Some new_node"

assumes new_node_uses_wire:
  "node_uses_qubit new_node q"

assumes new_node_not_frontier:
  (* The node being spliced is different from the current frontier
       node. Otherwise, the newly inserted frontier-to-node edge would
       become a self-loop and violate unique-successor validity. *)
  "new_node_id \<noteq> frontier q"

assumes new_node_has_no_other_successor:
  (* Before splicing, every existing q-labelled edge leaving the node
       being inserted, if any, already leads to the output node.
  
       This rules out another outgoing q-edge that would make the updated
       frontier branch after the new output edge is inserted.
    *)
  "\<And>successor_id.
       (new_node_id, successor_id)
         \<in> wire_edge_relation circuit q
       \<Longrightarrow> successor_id = get_output_node_id q"

shows
  "is_valid_frontier
       (fst (splice_wire circuit frontier q new_node_id))
       (snd (splice_wire circuit frontier q new_node_id))"

proof -
  let ?updated_circuit = "fst (splice_wire circuit frontier q new_node_id)"

  let ?updated_frontier = "snd (splice_wire circuit frontier q new_node_id)"

  show ?thesis
    unfolding is_valid_frontier_def

  proof (intro allI impI)
    fix queried_wire

    assume queried_wire_valid_after:
      "qubit_in_circuit ?updated_circuit queried_wire"

    show
      "\<exists>frontier_node.
         nodes ?updated_circuit (?updated_frontier queried_wire)
           = Some frontier_node
       \<and> node_uses_qubit frontier_node queried_wire
       \<and> make_edge
           (?updated_frontier queried_wire)
           (get_output_node_id queried_wire)
             queried_wire
           \<in> edges ?updated_circuit
       \<and> has_unique_wire_successor
              ?updated_circuit queried_wire
              (?updated_frontier queried_wire)"
    proof (cases "queried_wire = q")
      case True

      have updated_frontier_lookup: 
        "?updated_frontier queried_wire = new_node_id"
        using True
        by (simp add: snd_splice_wire)

      have new_node_exists_after_splice:
        (* splice_wire changes only edges and the frontier. Therefore, the node stored at new_node_id remains new_node *)
        "nodes ?updated_circuit new_node_id = Some new_node"
        unfolding
          splice_wire_def
          splice_wire_without_updating_frontier_def
          Let_def
          insert_edge_def
          delete_edge_def
        using new_node_exists
        by simp

      have new_node_uses_queried_wire:
        (* The inserted node uses q by assumption, and queried_wire = q in this branch. *)
        "node_uses_qubit new_node queried_wire"
        using new_node_uses_wire True
        by simp

      have new_output_edge_exists:
        (* The splice inserts the final edge from new_node_id to the output node of q. Since queried_wire = q, this is exactly the frontier edge required for queried_wire. *)
        "make_edge
           new_node_id
           (get_output_node_id queried_wire)
           queried_wire
         \<in> edges ?updated_circuit"
        unfolding
          splice_wire_def
          splice_wire_without_updating_frontier_def
          Let_def
          insert_edge_def
          delete_edge_def
        using True
        by simp

      have unique_successor:
        "has_unique_wire_successor
           ?updated_circuit
           queried_wire
           (?updated_frontier queried_wire)"
        unfolding has_unique_wire_successor_def
      proof (rule ex1I[of _ "get_output_node_id queried_wire"])

        show
          "(?updated_frontier queried_wire,
            get_output_node_id queried_wire)
           \<in> wire_edge_relation ?updated_circuit queried_wire"
          using
            updated_frontier_lookup
            new_output_edge_exists
          unfolding wire_edge_relation_def
          by simp

      next
        fix successor_id

        assume successor_edge_after:
          "(?updated_frontier queried_wire, successor_id)
             \<in> wire_edge_relation ?updated_circuit queried_wire"

        show
          "successor_id = get_output_node_id queried_wire"
          using
            successor_edge_after
            updated_frontier_lookup
            True
            new_node_not_frontier
            new_node_has_no_other_successor
          unfolding
            wire_edge_relation_def
            splice_wire_def
            splice_wire_without_updating_frontier_def
            insert_edge_def
            delete_edge_def
            make_edge_def
            Let_def
          by auto
      qed

      show ?thesis
        using
          updated_frontier_lookup
          new_node_exists_after_splice
          new_node_uses_queried_wire
          new_output_edge_exists
          unique_successor
        by simp

    next
      case False
      have updated_frontier_unchanged:
        (* Only the frontier entry for q was updated. Because queried_wire is different from q, its frontier entry remains exactly as it was before the splice. *)
        "?updated_frontier queried_wire = frontier queried_wire"
        using False
        by (simp add: snd_splice_wire)

      have queried_wire_valid_before:
        (* The queried wire was valid before the splice because splice_wire preserves the circuit's number of qubits. *)
        "qubit_in_circuit circuit queried_wire"
        using queried_wire_valid_after
        unfolding qubit_in_circuit_def
        by simp

      obtain old_frontier_node where
        old_frontier_node_exists:
        "nodes circuit (frontier queried_wire) = Some old_frontier_node"
        and old_frontier_node_uses_wire:
        "node_uses_qubit old_frontier_node queried_wire"
        and old_output_edge_exists:
        "make_edge
             (frontier queried_wire)
             (get_output_node_id queried_wire)
             queried_wire
           \<in> edges circuit"

and old_frontier_unique_successor:
"has_unique_wire_successor
             circuit
             queried_wire
             (frontier queried_wire)"
        using
          valid_frontier
          queried_wire_valid_before
        unfolding is_valid_frontier_def
        by auto

      have old_edge_is_not_deleted_edge:
        (* The old frontier edge belongs to queried_wire, while the
           deleted edge belongs to q. Since the wires are different,
           the two edge records cannot be equal *)
        "make_edge
           (frontier queried_wire)
           (get_output_node_id queried_wire)
           queried_wire
         \<noteq>
         make_edge
           (frontier q)
           (get_output_node_id q)
           q"
        using False
        unfolding make_edge_def
        by simp

      have old_output_edge_still_exists:
        (* The splice removes only the old edge on q. Since the frontier
           edge of queried_wire is different, it remains in the edge set.
           The two newly inserted edges do not remove any existing edge. *)
        "make_edge
           (frontier queried_wire)
           (get_output_node_id queried_wire)
           queried_wire
         \<in> edges ?updated_circuit"
        using
          old_output_edge_exists
          old_edge_is_not_deleted_edge
        by (simp add: fst_splice_wire edges_splice_wire_without_updating_frontier)

      have old_frontier_node_still_exists:
        (* splice_wire modifies edges and the frontier, but does not modify the circuit's nodes field. *)
        "nodes ?updated_circuit (frontier queried_wire) = Some old_frontier_node"
        using old_frontier_node_exists
        by simp

      have unaffected_wire_relation_unchanged:
        "wire_edge_relation ?updated_circuit queried_wire
         =
         wire_edge_relation circuit queried_wire"
        using False
        by (simp add:splice_wire_preserves_other_wire_relation)

      show ?thesis
        (* For an unaffected wire, reuse its original frontier node.
           Its frontier lookup, stored node, wire membership, and final
           output edge all remain valid after the splice. *)
        using
          updated_frontier_unchanged
          old_frontier_node_still_exists
          old_frontier_node_uses_wire
          old_output_edge_still_exists
          unaffected_wire_relation_unchanged
          has_unique_wire_successor_def
          old_frontier_unique_successor
        by auto
    qed
  qed
qed

lemma wire_edge_relation_update_next_id[simp]:
  (* Updating only next_id does not change the wire-edge relation, since wire_edge_relation depends only on the edge set. *)
  "wire_edge_relation (circuit\<lparr>next_id := new_next_id\<rparr>) q
   =
   wire_edge_relation circuit q"

  unfolding wire_edge_relation_def
  by simp

lemma wire_edge_relation_after_splice_same_wire:
  (* Splicing new_node_id into wire q removes the old frontier-to-output relation pair and inserts frontier-to-new and new-to-output. *)
  "wire_edge_relation
     (splice_wire_without_updating_frontier
      circuit frontier q new_node_id)
     q
   =
   (wire_edge_relation circuit q
      - {(frontier q, get_output_node_id q)})
      \<union> {(frontier q, new_node_id),
      (new_node_id, get_output_node_id q)}"

proof (rule set_eqI)
  fix relation_pair :: "node_id \<times> node_id"

  obtain source_id target_id where
    [simp]: "relation_pair = (source_id, target_id)"
    by (cases relation_pair) simp

  show
    "relation_pair
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q
     \<longleftrightarrow>
     relation_pair
       \<in> (wire_edge_relation circuit q
            - {(frontier q, get_output_node_id q)})
          \<union> {(frontier q, new_node_id),
             (new_node_id, get_output_node_id q)}"
    unfolding
      wire_edge_relation_def
      splice_wire_without_updating_frontier_def
      delete_edge_def
      insert_edge_def
      make_edge_def
      Let_def
    by auto
qed

lemma wire_edge_relation_after_splice_other_wire:
  (* Splicing wire q removes and inserts only q-labelled edges.
     Therefore, the relation of any different wire other_q is unchanged. *)
  assumes different_wire:
    "other_q \<noteq> q"

shows
  "wire_edge_relation
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       other_q
     =
     wire_edge_relation circuit other_q"

proof (rule set_eqI)
  fix relation_pair :: "node_id \<times> node_id"

  obtain source_id target_id where
    [simp]: "relation_pair = (source_id, target_id)"
    by (cases relation_pair) simp

  show
    "relation_pair
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           other_q
     \<longleftrightarrow>
     relation_pair
       \<in> wire_edge_relation circuit other_q"
    using different_wire
    unfolding
      wire_edge_relation_def
      splice_wire_without_updating_frontier_def
      delete_edge_def
      insert_edge_def
      make_edge_def
      Let_def
    by simp
qed

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

proof (cases
    "(source_id, target_id) =
     (frontier q, get_output_node_id q)")

  case True

  have first_new_edge:
    "(frontier q, new_node_id)
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q"
    using wire_edge_relation_after_splice_same_wire
    by simp

  have second_new_edge:
    "(new_node_id, get_output_node_id q)
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q"
    using wire_edge_relation_after_splice_same_wire
    by simp

  have frontier_reaches_new:
    "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       (frontier q)
       new_node_id"
    using first_new_edge
    by (simp add: wire_edge_implies_wire_reaches)

  have new_reaches_output:
    "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       new_node_id
       (get_output_node_id q)"
    using second_new_edge
    by (simp add: wire_edge_implies_wire_reaches)

  have frontier_reaches_output:
    "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       (frontier q)
       (get_output_node_id q)"
  proof -
    show ?thesis
      unfolding wire_reaches_def
      using frontier_reaches_new new_reaches_output
      unfolding wire_reaches_def
      by (rule trancl_trans)
  qed

  show ?thesis
    using True frontier_reaches_output
    by simp

next

  case False

  have old_edge_not_deleted:
    "(source_id, target_id)
       \<in> wire_edge_relation circuit q
          - {(frontier q, get_output_node_id q)}"
    using old_edge False
    by simp

  have edge_still_present:
    "(source_id, target_id)
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q"
    using old_edge_not_deleted
      wire_edge_relation_after_splice_same_wire
    by auto

  show ?thesis
    using edge_still_present
    by (rule wire_edge_implies_wire_reaches)

qed

lemma old_wire_reaches_after_splice:
  (* If target_id was reachable from source_id along wire q before
     splicing, then it remains reachable afterward.

     The proof lifts old_wire_edge_reaches_after_splice from individual
     relation edges to arbitrary non-empty paths by induction over the
     transitive-closure derivation. *)
  assumes old_reachability:
    "wire_reaches circuit q source_id target_id"

shows
  "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       source_id
       target_id"

proof -
  let ?updated_circuit =
    "splice_wire_without_updating_frontier
       circuit frontier q new_node_id"

  have old_trancl:
    "(source_id, target_id)
       \<in> (wire_edge_relation circuit q)\<^sup>+"
    using old_reachability
    unfolding wire_reaches_def .

  have preserved_trancl:
    "(source_id, target_id)
       \<in> (wire_edge_relation ?updated_circuit q)\<^sup>+"
    using old_trancl
  proof (induction rule: trancl_induct)

    case (base target_id)

    have preserved_edge:
      "wire_reaches
         ?updated_circuit q source_id target_id"
      using base.hyps
      by (rule old_wire_edge_reaches_after_splice)

    then show ?case
      unfolding wire_reaches_def
      .

  next
    case (step middle_id target_id)

    have preserved_prefix:
      "(source_id, middle_id)
         \<in> (wire_edge_relation ?updated_circuit q)\<^sup>+"
      using step.IH .

    have preserved_last_edge:
      "wire_reaches
         ?updated_circuit q middle_id target_id"
      using step.hyps(2)
      by (rule old_wire_edge_reaches_after_splice)

    have preserved_last_trancl:
      "(middle_id, target_id)
         \<in> (wire_edge_relation ?updated_circuit q)\<^sup>+"
      using preserved_last_edge
      unfolding wire_reaches_def
      .

    show ?case
      using preserved_prefix preserved_last_trancl
      by (rule trancl_trans)

  qed

  show ?thesis
    using preserved_trancl
    unfolding wire_reaches_def
    .
qed

lemma old_nodes_comparable_after_splice:
  (* Splicing a new node into wire q does not destroy the ordering between nodes that already existed in the circuit.

     If two old nodes were equal, or one reached the other before the splice, the same comparison remains valid afterward because every old wire path is preserved by old_wire_reaches_after_splice. *)
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

proof -
  have old_comparison:
    "node_a = node_b
     \<or> wire_reaches circuit q node_a node_b
     \<or> wire_reaches circuit q node_b node_a"
    using
      old_nodes_comparable
      node_a_lookup
      node_b_lookup
      node_a_uses_q
      node_b_uses_q
    unfolding nodes_comparable_on_wire_def
    by simp

  from old_comparison show ?thesis
  proof (elim disjE)
    assume nodes_equal:
      "node_a = node_b"

    then show ?thesis
      by simp

  next
    assume node_a_reaches_node_b:
      "wire_reaches circuit q node_a node_b"

    have preserved_reachability:
      "wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_a node_b"
      using node_a_reaches_node_b
      by (rule old_wire_reaches_after_splice)

    then show ?thesis
      by simp

  next
    assume node_b_reaches_node_a:
      "wire_reaches circuit q node_b node_a"

    have preserved_reachability:
      "wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_b node_a"
      using node_b_reaches_node_a
      by (rule old_wire_reaches_after_splice)

    then show ?thesis
      by simp

  qed
qed

end
