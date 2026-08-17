theory Quantum_Circuit_Delete_Validity
  imports Quantum_Circuit_Delete_Core

begin

lemma delete_operation_reachability_preserved:
  (* Every non-empty directed path that exists after deleting an operation
     corresponds to a non-empty directed path that already existed in the
     original circuit.

     Edges unaffected by deletion are original circuit edges. Every new
     predecessor-to-successor edge introduced by reconnect_wire replaces
     the original two-edge path

         predecessor \<rightarrow> operation_node_id \<rightarrow> successor.

     Consequently, deletion may shorten directed paths, but it cannot
     introduce reachability between nodes that were not already reachable
     in the original circuit.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "(edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+
       \<subseteq>
     (edge_relation circuit)\<^sup>+"
proof

  fix node_pair

  assume reachable_after_deletion:
    "node_pair
     \<in>
     (edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+"

  (*
    Expose the source and target components of the pair so that the
    transitive-closure induction can reason about the path endpoints.
  *)
  obtain source_id target_id where
    node_pair:
      "node_pair = (source_id, target_id)"
    by (cases node_pair)

  have source_reaches_target_after_deletion:
    "(source_id, target_id)
     \<in>
     (edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+"
    using reachable_after_deletion node_pair
    by simp

  (*
    Induct over the non-empty path in the deleted circuit.

    The base case contains one deleted-circuit edge. The helper
    delete_operation_edge_preserves_reachability maps that edge to a
    non-empty path in the original circuit.

    In the induction step, the prefix has already been mapped to an
    original-circuit path. The final deleted-circuit edge is independently
    mapped to another original-circuit path, and the two paths are then
    concatenated.
  *)
  have source_reaches_target_original:
    "(source_id, target_id)
     \<in>
     (edge_relation circuit)\<^sup>+"
    using source_reaches_target_after_deletion
  proof (induction rule: trancl_induct)

    case (base intermediate_id)

    (*
      A one-edge path after deletion corresponds either to the same
      original edge or to the original two-edge path through the deleted
      operation node.
    *)
    show ?case
      using
        valid_circuit
        operation_exists
        base.hyps
      by (rule delete_operation_edge_preserves_reachability)

  next

    case (step intermediate_id final_id)

    (*
      The induction hypothesis provides an original-circuit path from the
      fixed source to intermediate_id.
    *)
    have prefix_reachable_original:
      "(source_id, intermediate_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using step.IH .

    (*
      Map the final edge of the deleted-circuit path to a non-empty path
      from intermediate_id to final_id in the original circuit.
    *)
    have final_segment_reachable_original:
      "(intermediate_id, final_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using
        valid_circuit
        operation_exists
        step.hyps(2)
      by (rule delete_operation_edge_preserves_reachability)

    (*
      Concatenate the mapped prefix and final segment to obtain the full
      original-circuit reachability result.
    *)
    show ?case
      using
        prefix_reachable_original
        final_segment_reachable_original
      by (rule trancl_trans)
  qed

  show
    "node_pair \<in> (edge_relation circuit)\<^sup>+"
    using source_reaches_target_original node_pair
    by simp
qed

lemma reconnect_wire_successor_has_unique_predecessor:
  (* The successor of the reconnected operation retains exactly one
     predecessor on q. Its old predecessor, operation_node_id, is replaced
     by predecessor_id through the inserted bypass edge. *)
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor
         current_circuit q successor_id"
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
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       successor_id"

proof -

  have old_incoming_original:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have old_incoming_current:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation current_circuit q"
    using old_incoming_original same_relation
    by simp

  have every_old_predecessor_is_operation:
    "\<And>source_id.
       (source_id, successor_id)
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       source_id = operation_node_id"
    using unique_predecessor old_incoming_current
    unfolding has_unique_wire_predecessor_def
    by blast

  have relation_after:
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
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have bypass_exists:
    "(predecessor_id, successor_id)
       \<in> wire_edge_relation
            (reconnect_wire
               original_circuit
               operation_node_id
               q
               current_circuit)
            q"
    by (simp add: relation_after)

  show ?thesis
    using
      Diff_insert0
      Pair_inject
      every_old_predecessor_is_operation
      has_unique_wire_predecessor_def
      relation_after
    by auto
qed

lemma reconnect_wire_predecessor_has_unique_successor:
  (* The predecessor of the reconnected operation retains exactly one
     successor on q. Its old successor, operation_node_id, is replaced by
     successor_id through the inserted bypass edge. *)
  assumes
    unique_successor:
      "has_unique_wire_successor
         current_circuit q predecessor_id"
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
    "has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       predecessor_id"

proof -

  have old_outgoing_original:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have old_outgoing_current:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation current_circuit q"
    using old_outgoing_original same_relation
    by simp

  have every_old_successor_is_operation:
    "\<And>target_id.
       (predecessor_id, target_id)
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       target_id = operation_node_id"
    using unique_successor old_outgoing_current
    unfolding has_unique_wire_successor_def
    by blast

  have relation_after:
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
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have bypass_exists:
    "(predecessor_id, successor_id)
       \<in> wire_edge_relation
            (reconnect_wire
               original_circuit
               operation_node_id
               q
               current_circuit)
            q"
    by (simp add: relation_after)

  show ?thesis
    using
      every_old_successor_is_operation
      has_unique_wire_successor_def
      relation_after
    by auto
qed

lemma reconnect_wire_other_node_has_unique_predecessor:
  (* A node that is neither the deleted operation nor its successor keeps
     exactly the same incoming q-edges after reconnection. Therefore, its
     unique-predecessor property is preserved. *)
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor
         current_circuit q node_id"
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
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_successor:
      "node_id \<noteq> successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_id"

proof -
  let ?updated_circuit =
    "reconnect_wire
       original_circuit
       operation_node_id
       q
       current_circuit"

  have relation_after:
    "wire_edge_relation ?updated_circuit q =
       insert
         (predecessor_id, successor_id)
         (wire_edge_relation current_circuit q
            -
            {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have incoming_relation_iff:
    "\<And>source_id.
       (source_id, node_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (source_id, node_id)
         \<in> wire_edge_relation current_circuit q"
  proof -
    fix source_id

    show
      "(source_id, node_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (source_id, node_id)
         \<in> wire_edge_relation current_circuit q"
      using
        relation_after
        not_deleted
        not_successor
      by auto
  qed

  show ?thesis
    using has_unique_wire_predecessor_def incoming_relation_iff unique_predecessor
    by fastforce
qed

lemma reconnect_wire_other_node_has_unique_successor:
  (* A node that is neither the deleted operation nor its predecessor keeps
     exactly the same outgoing q-edges after reconnection. Therefore, its
     unique-successor property is preserved. *)
  assumes
    unique_successor:
      "has_unique_wire_successor
         current_circuit q node_id"
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
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_predecessor:
      "node_id \<noteq> predecessor_id"
  shows
    "has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_id"

proof -

  let ?updated_circuit =
    "reconnect_wire
       original_circuit
       operation_node_id
       q
       current_circuit"

  have relation_after:
    "wire_edge_relation ?updated_circuit q =
       insert
         (predecessor_id, successor_id)
         (wire_edge_relation current_circuit q
            -
            {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have outgoing_relation_iff:
    "\<And>target_id.
       (node_id, target_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q"
  proof -
    fix target_id

    show
      "(node_id, target_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q"
      using
        relation_after
        not_deleted
        not_predecessor
      by auto
  qed

  have old_exists:
    "\<exists>target_id.
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q"
    using unique_successor
    unfolding has_unique_wire_successor_def
    by blast

  have old_unique:
    "\<And>target_id target_id'.
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       (node_id, target_id')
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       target_id = target_id'"
    using unique_successor
    unfolding has_unique_wire_successor_def
    by blast

  show ?thesis
    using
      has_unique_wire_successor_def
      old_exists
      old_unique
      outgoing_relation_iff
    by auto
qed

lemma reconnect_wire_preserves_remaining_node_degrees:
  (* Reconnecting predecessor -> operation -> successor preserves the unique
     predecessor and successor properties of every node other than the
     deleted operation.

     There are three cases:
       1. node_id is the predecessor: its outgoing edge is redirected;
       2. node_id is the successor: its incoming edge is redirected;
       3. node_id is neither: both incident edge sets remain unchanged.
  *)
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor current_circuit q node_id"
  and
    unique_successor:
      "has_unique_wire_successor current_circuit q node_id"
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
  and
    remaining_node:
      "node_id \<noteq> operation_node_id"
  and
    predecessor_not_deleted:
      "predecessor_id \<noteq> operation_node_id"
  and
    successor_not_deleted:
      "successor_id \<noteq> operation_node_id"
  and
    predecessor_not_successor:
      "predecessor_id \<noteq> successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit operation_node_id q current_circuit)
       q node_id
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          original_circuit operation_node_id q current_circuit)
       q node_id"
  by (metis
      predecessor
      reconnect_wire_other_node_has_unique_predecessor
      reconnect_wire_other_node_has_unique_successor
      reconnect_wire_predecessor_has_unique_successor
      reconnect_wire_successor_has_unique_predecessor
      remaining_node
      same_relation
      successor
      unique_predecessor
      unique_successor)

lemma fold_reconnect_preserves_operation_degrees:
  (* Reconnecting a distinct list of wires preserves the predecessor and
     successor degrees of a remaining node on q.

     Reconnections before q do not alter q's wire relation. The reconnection
     of q preserves the node's degrees using the local theorem. Reconnections
     after q again leave q's relation unchanged.
  *)
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor circuit q node_id"
  and
    unique_successor:
      "has_unique_wire_successor circuit q node_id"
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
    remaining_node:
      "node_id \<noteq> operation_node_id"
  and
    predecessor_not_deleted:
      "predecessor_id \<noteq> operation_node_id"
  and
    successor_not_deleted:
      "successor_id \<noteq> operation_node_id"
  and
    predecessor_not_successor:
      "predecessor_id \<noteq> successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_id
     \<and>
     has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_id"

proof -
  obtain before after where
    qs_decomposition:
      "qs = before @ q # after"
    using used_wire
    by (meson split_list)

  have q_not_in_before:
    "q \<notin> set before"
    using distinct_wires qs_decomposition
    by auto

  have q_not_in_after:
    "q \<notin> set after"
    using distinct_wires qs_decomposition
    by auto

  let ?before_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       before
       circuit"

  let ?q_circuit =
    "reconnect_wire
       circuit
       operation_node_id
       q
       ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q =
       wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_before
    by simp

  have predecessor_before:
    "has_unique_wire_predecessor
       ?before_circuit q node_id"
    using unique_predecessor before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have successor_before:
    "has_unique_wire_successor
       ?before_circuit q node_id"
    using unique_successor before_same_relation
    unfolding has_unique_wire_successor_def
    by simp

  have degrees_after_q:
    "has_unique_wire_predecessor
       ?q_circuit q node_id
     \<and>
     has_unique_wire_successor
       ?q_circuit q node_id"
    using
      before_same_relation
      predecessor
      predecessor_before
      predecessor_not_deleted
      predecessor_not_successor
      reconnect_wire_preserves_remaining_node_degrees
      remaining_node
      successor
      successor_before
      successor_not_deleted
    by simp
    
  have after_same_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
     =
     wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_after
    by simp
    
  have predecessor_after:
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
       node_id"
    using
      degrees_after_q
      after_same_relation
      has_unique_wire_predecessor_def
    by simp

  have successor_after:
    "has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
       node_id"
    using degrees_after_q after_same_relation
    unfolding has_unique_wire_successor_def
    by auto

  show ?thesis
    using
      predecessor_after
      successor_after
      qs_decomposition
    by simp

qed

lemma delete_operation_preserves_acyclicity:
  (* Deleting an operation from a valid quantum circuit preserves
     acyclicity.

     Assume, for contradiction, that the circuit obtained after deletion
     contains a directed cycle. Such a cycle gives a non-empty path from
     some node back to itself.

     By delete_operation_reachability_preserved, the same node was already
     reachable from itself in the original circuit. This contradicts the
     original circuit's acyclicity. Therefore, deleting the operation
     cannot create a directed cycle.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "is_acyclic_circuit
       (delete_operation circuit operation_node_id)"

proof -

  have original_acyclic:
    "acyclic (edge_relation circuit)"
    using valid_circuit
    unfolding is_valid_circuit_def
              is_acyclic_circuit_def
    by simp

  have reachability_preserved:
    "(edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+
       \<subseteq>
     (edge_relation circuit)\<^sup>+"
    using valid_circuit operation_exists
    by (rule delete_operation_reachability_preserved)

  show ?thesis
    unfolding is_acyclic_circuit_def acyclic_def
  proof
    fix node_id

    show
      "(node_id, node_id)
         \<notin> (edge_relation
              (delete_operation circuit operation_node_id))\<^sup>+"
    proof
      assume cycle_after_deletion:
        "(node_id, node_id)
           \<in> (edge_relation
                (delete_operation circuit operation_node_id))\<^sup>+"

      then have cycle_before_deletion:
        "(node_id, node_id) \<in> (edge_relation circuit)\<^sup>+"
        using reachability_preserved
        by auto

      moreover have
        "(node_id, node_id) \<notin> (edge_relation circuit)\<^sup>+"
        using original_acyclic
        unfolding acyclic_def
        by simp

      ultimately show False
        by simp
    qed
  qed

qed

lemma delete_operation_preserves_unused_wire_relation:
  (* If the deleted operation does not use q, delete_operation never invokes
     reconnect_wire on q.

     The final node-table update removes the operation node but does not
     modify the edge set. Therefore, the q-labelled edge relation is
     exactly the same before and after deletion.
  *)
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation circuit q"

proof -
  have folded_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
       q
     =
     wire_edge_relation circuit q"
    using unused_wire
    by (rule fold_reconnect_preserves_other_wire_relation)

  show ?thesis
    using
      operation_exists
      folded_relation 
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp
qed

lemma delete_operation_preserves_linear_unused_wire:
  (* If the deleted operation does not use q, deletion does not modify
     the q-labelled edge relation.

     reconnect_wire is applied only to qubits in op_qargs op. Since q is
     absent from that list, no q-edge is removed or inserted. The deleted
     operation node also does not use q, so removing that node does not
     remove a node belonging to the q-wire.

     Consequently, every component of wire_is_linear on q is unchanged:
       - comparability;
       - the input boundary conditions;
       - the output boundary conditions;
       - unique predecessors and successors of operation nodes using q.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_is_linear circuit q
     \<Longrightarrow>
     wire_is_linear
       (delete_operation circuit operation_node_id)
       q"

proof -
  assume original_linear:
    "wire_is_linear circuit q"

  let ?deleted =
    "delete_operation circuit operation_node_id"

  have same_wire_relation:
    "wire_edge_relation ?deleted q =
     wire_edge_relation circuit q"
    using operation_exists unused_wire
    by (rule delete_operation_preserves_unused_wire_relation)

  have deleted_node_does_not_use_q:
    "\<not> node_uses_qubit (OperationNode op) q"
    using unused_wire
    by simp

  have remaining_node_origin:
    "\<And>node_id node_value.
       nodes ?deleted node_id = Some node_value
       \<Longrightarrow>
       nodes circuit node_id = Some node_value"
  proof -
    fix node_id node_value

    assume node_after:
      "nodes ?deleted node_id = Some node_value"

    have node_id_not_deleted:
      "node_id \<noteq> operation_node_id"
    proof
      assume
        "node_id = operation_node_id"

      then have
        "nodes ?deleted node_id = None"
        using operation_exists
        by simp

      with node_after show False
        by simp
    qed

    show
      "nodes circuit node_id = Some node_value"
      using
        node_after
        node_id_not_deleted
        operation_exists
        fold_reconnect_wire_preserves_nodes
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed

  have original_q_node_survives:
    "\<And>node_id node_value.
       nodes circuit node_id = Some node_value
       \<Longrightarrow>
       node_uses_qubit node_value q
       \<Longrightarrow>
       nodes ?deleted node_id = Some node_value"
  proof -

    fix node_id node_value

    assume node_before:
      "nodes circuit node_id = Some node_value"

    assume uses_q:
      "node_uses_qubit node_value q"

    have node_id_not_deleted:
      "node_id \<noteq> operation_node_id"
    proof
      assume same_id:
        "node_id = operation_node_id"

      from node_before operation_exists same_id
      have
        "node_value = OperationNode op"
        by simp

      then have
        "node_uses_qubit (OperationNode op) q"
        using uses_q
        by simp

      with deleted_node_does_not_use_q
      show False
        by simp
    qed

    show
      "nodes ?deleted node_id = Some node_value"
      using
        node_before
        node_id_not_deleted
        operation_exists
        fold_reconnect_wire_preserves_nodes
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed

  have comparable_after:
    "nodes_comparable_on_wire ?deleted q"
  proof -
    have comparable_before:
      "nodes_comparable_on_wire circuit q"
      using original_linear
      unfolding wire_is_linear_def
      by simp

    show ?thesis
      unfolding nodes_comparable_on_wire_def

    proof (intro allI impI)

      fix node_a node_b node_a_value node_b_value

      assume node_a_after:
        "nodes ?deleted node_a = Some node_a_value"

      assume node_b_after:
        "nodes ?deleted node_b = Some node_b_value"

      assume node_a_uses_q:
        "node_uses_qubit node_a_value q"

      assume node_b_uses_q:
        "node_uses_qubit node_b_value q"

      have node_a_before:
        "nodes circuit node_a = Some node_a_value"
        using node_a_after
        by (rule remaining_node_origin)

      have node_b_before:
        "nodes circuit node_b = Some node_b_value"
        using node_b_after
        by (rule remaining_node_origin)

      have original_comparison:
        "node_a = node_b
         \<or> wire_reaches circuit q node_a node_b
         \<or> wire_reaches circuit q node_b node_a"
        using
          comparable_before
          node_a_before
          node_b_before
          node_a_uses_q
          node_b_uses_q
        unfolding nodes_comparable_on_wire_def
        by blast

      show
        "node_a = node_b
         \<or> wire_reaches ?deleted q node_a node_b
         \<or> wire_reaches ?deleted q node_b node_a"
        using original_comparison same_wire_relation
        unfolding wire_reaches_def
        by simp

    qed

  qed

  have operation_nodes_after:
    "\<forall>node_id remaining_op.
       nodes ?deleted node_id = Some (OperationNode remaining_op)
       \<longrightarrow>
       node_uses_qubit (OperationNode remaining_op) q
       \<longrightarrow>
       has_unique_wire_predecessor ?deleted q node_id
       \<and>
       has_unique_wire_successor ?deleted q node_id"
  proof (intro allI impI)

    fix node_id remaining_op

    assume node_after:
      "nodes ?deleted node_id =
         Some (OperationNode remaining_op)"

    assume uses_q:
      "node_uses_qubit (OperationNode remaining_op) q"

    have node_before:
      "nodes circuit node_id =
         Some (OperationNode remaining_op)"
      using node_after
      by (rule remaining_node_origin)

    have original_operation_condition:
      "has_unique_wire_predecessor circuit q node_id
       \<and>
       has_unique_wire_successor circuit q node_id"
      using original_linear node_before uses_q
      unfolding wire_is_linear_def
      by blast

    show
      "has_unique_wire_predecessor ?deleted q node_id
       \<and>
       has_unique_wire_successor ?deleted q node_id"
      using original_operation_condition same_wire_relation
      unfolding
        has_unique_wire_predecessor_def
        has_unique_wire_successor_def
      by simp

  qed

  show
    "wire_is_linear ?deleted q"
    using
      original_linear
      comparable_after
      operation_nodes_after
      same_wire_relation
    unfolding
      wire_is_linear_def
      has_unique_wire_predecessor_def
      has_unique_wire_successor_def
    by simp
qed

lemma reconnect_wire_preserves_surviving_reachability:
  (* Contracting

         predecessor_id -> operation_node_id -> successor_id

     into

         predecessor_id -> successor_id

     preserves q-reachability between endpoints other than the contracted
     operation node.

     The uniqueness assumptions ensure that any path entering the contracted
     node must enter through predecessor_id, and any path leaving it must
     leave through successor_id. Hence every occurrence of the two-edge
     segment can be replaced by the bypass edge.
  *)
  assumes
    same_relation:
      "wire_edge_relation current_circuit q =
       wire_edge_relation original_circuit q"
  and
    unique_operation_predecessor:
      "has_unique_wire_predecessor
         current_circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor
         current_circuit q operation_node_id"
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
  and
    old_reachability:
      "wire_reaches current_circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  shows
    "wire_reaches
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_a
       node_b"

proof -

  let ?old_relation =
    "wire_edge_relation current_circuit q"

  let ?new_relation =
    "wire_edge_relation
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q"

  have predecessor_edge_original:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have predecessor_edge_current:
    "(predecessor_id, operation_node_id)
       \<in> ?old_relation"
    using predecessor_edge_original same_relation
    by simp

  have successor_edge_original:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have successor_edge_current:
    "(operation_node_id, successor_id)
       \<in> ?old_relation"
    using successor_edge_original same_relation
    by simp

  have every_operation_predecessor:
    "\<And>source_id.
       (source_id, operation_node_id) \<in> ?old_relation
       \<Longrightarrow>
       source_id = predecessor_id"
    using
      unique_operation_predecessor
      predecessor_edge_current
    unfolding has_unique_wire_predecessor_def
    by blast

  have every_operation_successor:
    "\<And>target_id.
       (operation_node_id, target_id) \<in> ?old_relation
       \<Longrightarrow>
       target_id = successor_id"
    using
      unique_operation_successor
      successor_edge_current
    unfolding has_unique_wire_successor_def
    by blast

  have relation_after:
    "?new_relation =
       insert
         (predecessor_id, successor_id)
         (?old_relation
            -
            {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have bypass_edge:
    "(predecessor_id, successor_id) \<in> ?new_relation"
    using relation_after
    by simp

  have surviving_edge_preserved:
    "\<And>source_id target_id.
       (source_id, target_id) \<in> ?old_relation
       \<Longrightarrow>
       source_id \<noteq> operation_node_id
       \<Longrightarrow>
       target_id \<noteq> operation_node_id
       \<Longrightarrow>
       (source_id, target_id) \<in> ?new_relation"
    using relation_after
    by auto

  have old_path:
    "(node_a, node_b) \<in> ?old_relation\<^sup>+"
    using old_reachability
    unfolding wire_reaches_def
    .

  have strengthened_path:
    "\<And>target_id.
       (node_a, target_id) \<in> ?old_relation\<^sup>+
       \<Longrightarrow>
       (target_id = operation_node_id
        \<longrightarrow>
          node_a = predecessor_id
          \<or>
          (node_a, predecessor_id) \<in> ?new_relation\<^sup>+)
       \<and>
       (target_id \<noteq> operation_node_id
        \<longrightarrow>
          (node_a, target_id) \<in> ?new_relation\<^sup>+)"
  proof -

    fix target_id

    assume old_target_path:
      "(node_a, target_id) \<in> ?old_relation\<^sup>+"

    show
      "(target_id = operation_node_id
        \<longrightarrow>
          node_a = predecessor_id
          \<or>
          (node_a, predecessor_id) \<in> ?new_relation\<^sup>+)
       \<and>
       (target_id \<noteq> operation_node_id
        \<longrightarrow>
          (node_a, target_id) \<in> ?new_relation\<^sup>+)"

      using old_target_path
    proof (induction rule: trancl_induct)

      case (base target_id)
      
      show ?case
        using
          base
          every_operation_predecessor
          source_survives
          surviving_edge_preserved
        by auto

    next

      case (step middle_id target_id)

      show ?case
        by (metis
            bypass_edge
            every_operation_predecessor
            every_operation_successor
            step.IH
            step.hyps(2)
            surviving_edge_preserved
            trancl.simps)
    qed
  qed

  have new_path:
    "(node_a, node_b) \<in> ?new_relation\<^sup>+"
    using
      strengthened_path[OF old_path]
      target_survives
    by blast

  show ?thesis
    using new_path
    unfolding wire_reaches_def
    .
qed

lemma fold_reconnect_preserves_surviving_reachability:
  (* In a distinct list of affected wires containing q, reconnections on
     wires other than q leave q's relation unchanged. The single
     reconnection on q contracts the deleted operation while preserving
     reachability between surviving endpoints.
  *)
  assumes
    unique_operation_predecessor:
      "has_unique_wire_predecessor
         circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor
         circuit q operation_node_id"
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
    old_reachability:
      "wire_reaches circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "wire_reaches
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_a
       node_b"

proof -
  obtain before after where
    qs_decomposition:
      "qs = before @ q # after"
    using used_wire
    by (meson split_list)

  have q_not_in_before:
    "q \<notin> set before"
    using distinct_wires qs_decomposition
    by auto

  have q_not_in_after:
    "q \<notin> set after"
    using distinct_wires qs_decomposition
    by auto

  let ?before_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       before
       circuit"

  let ?q_circuit =
    "reconnect_wire
       circuit
       operation_node_id
       q
       ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q =
       wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_before
    by simp

  have predecessor_before:
    "has_unique_wire_predecessor
       ?before_circuit q operation_node_id"
    using
      unique_operation_predecessor
      before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have successor_before:
    "has_unique_wire_successor
       ?before_circuit q operation_node_id"
    using
      unique_operation_successor
      before_same_relation
    unfolding has_unique_wire_successor_def
    by auto

  have reachability_before:
    "wire_reaches ?before_circuit q node_a node_b"
    using
      old_reachability
      before_same_relation
    unfolding wire_reaches_def
    by simp

  have reachability_after_q:
    "wire_reaches ?q_circuit q node_a node_b"
    using
      before_same_relation
      predecessor
      predecessor_before
      reachability_before
      reconnect_wire_preserves_surviving_reachability
      source_survives
      successor
      successor_before
      target_survives
    by simp

  have after_same_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
     =
     wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_after
    by simp

  have reachability_after:
    "wire_reaches
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
       node_a
       node_b"
    using
      reachability_after_q
      after_same_relation
    unfolding wire_reaches_def
    by simp

  show ?thesis
    using
      reachability_after
      qs_decomposition
    by simp
qed

lemma delete_operation_preserves_surviving_wire_reachability:
  (* Deleting an operation preserves q-reachability between any two
     surviving endpoints on a wire used by that operation.

     The fold contracts the operation on every used wire. The final update
     removes only the operation from the node table and does not alter the
     already-reconnected edge relation.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  and
    old_reachability:
      "wire_reaches circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  shows
    "wire_reaches
       (delete_operation circuit operation_node_id)
       q
       node_a
       node_b"

proof -
  have unique_operation_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  have unique_operation_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_relation_id where
    predecessor_relation:
      "(predecessor_relation_id, operation_node_id)
         \<in> wire_edge_relation circuit q"
    using unique_operation_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_relation_id where
    successor_relation:
      "(operation_node_id, successor_relation_id)
         \<in> wire_edge_relation circuit q"
    using unique_operation_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire
       circuit operation_node_id q
     \<noteq> None"
    using predecessor_relation
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  obtain predecessor_id where
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
       Some predecessor_id"
    using predecessor_not_none
    by (cases
        "predecessor_on_wire
           circuit operation_node_id q")
       auto

  have successor_not_none:
    "successor_on_wire
       circuit operation_node_id q
     \<noteq> None"
    using successor_relation
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  obtain successor_id where
    successor:
      "successor_on_wire
         circuit operation_node_id q =
       Some successor_id"
    using successor_not_none
    by (cases
        "successor_on_wire
           circuit operation_node_id q")
       auto

  have valid_operation:
    "is_valid_operation op"
    using
      valid_circuit
      operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_wires:
    "distinct (op_qargs op)"
    using valid_operation
    unfolding is_valid_operation_def
    by auto

  let ?reconnected_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       (op_qargs op)
       circuit"

  have reachability_after_fold:
    "wire_reaches
       ?reconnected_circuit
       q
       node_a
       node_b"
    using
      fold_reconnect_preserves_surviving_reachability
      unique_operation_predecessor
      unique_operation_successor
      predecessor
      successor
      old_reachability
      source_survives
      target_survives
      distinct_wires
      used_wire
    by simp

  have relation_after_delete:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation
       ?reconnected_circuit
       q"
    using operation_exists
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp

  show ?thesis
    using
      reachability_after_fold
      relation_after_delete
    unfolding wire_reaches_def
    by simp
qed

lemma delete_operation_used_wire_preserves_comparability:
  (* Deleting an operation that uses q preserves comparability among all
     remaining nodes on q.

     In the original linear wire, every pair of q-nodes is ordered by
     q-reachability. Deletion contracts

         predecessor \<rightarrow> operation_node_id \<rightarrow> successor

     into

         predecessor \<rightarrow> successor.

     Any original path between two remaining q-nodes either avoids the
     deleted node and remains unchanged, or passes through the deleted
     node and is shortened through the new bypass edge.

     Therefore, every pair of remaining q-nodes remains comparable.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "nodes_comparable_on_wire
       (delete_operation circuit operation_node_id)
       q"

proof -
  have original_comparability:
    "nodes_comparable_on_wire circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  show ?thesis
    unfolding nodes_comparable_on_wire_def
  proof (intro allI impI)

    fix node_a node_b node_a_value node_b_value

    assume node_a_exists_after:
      "nodes
         (delete_operation circuit operation_node_id)
         node_a
       =
       Some node_a_value"

    assume node_b_exists_after:
      "nodes
         (delete_operation circuit operation_node_id)
         node_b
       =
       Some node_b_value"

    assume node_a_uses_q:
      "node_uses_qubit node_a_value q"

    assume node_b_uses_q:
      "node_uses_qubit node_b_value q"

    have node_a_survives:
      "node_a \<noteq> operation_node_id"
      using
        node_a_exists_after
        operation_exists
      by auto

    have node_b_survives:
      "node_b \<noteq> operation_node_id"
      using
        node_b_exists_after
        operation_exists
      by auto

    have node_a_exists_before:
      "nodes circuit node_a = Some node_a_value"
      using
        node_a_exists_after
        node_a_survives
        operation_exists
      by auto

    have node_b_exists_before:
      "nodes circuit node_b = Some node_b_value"
      using
        node_b_exists_after
        node_b_survives
        operation_exists
      by auto

    have comparable_before:
      "node_a = node_b
       \<or> wire_reaches circuit q node_a node_b
       \<or> wire_reaches circuit q node_b node_a"
      using
        original_comparability
        node_a_exists_before
        node_b_exists_before
        node_a_uses_q
        node_b_uses_q
      unfolding nodes_comparable_on_wire_def
      by blast

    show
      "node_a = node_b
       \<or>
       wire_reaches
         (delete_operation circuit operation_node_id)
         q
         node_a
         node_b
       \<or>
       wire_reaches
         (delete_operation circuit operation_node_id)
         q
         node_b
         node_a"
      using
        comparable_before
        delete_operation_preserves_surviving_wire_reachability
        node_a_survives
        node_b_survives
        operation_exists
        original_linear
        used_wire
        valid_circuit
      by blast
  qed
qed

lemma delete_operation_used_wire_preserves_input_boundary:
  (* Deleting an operation preserves the input boundary on every wire used
     by that operation.

     Since the original wire is linear, the operation node has exactly one
     predecessor and one successor on q. The operation is valid, so its
     qubit list is distinct. Therefore, the fold reconnects q exactly once,
     preserving the input boundary, while reconnections on the other wires
     do not affect q. Removing the operation from the node table afterward
     does not change the edge relation.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)
     \<and>
     has_unique_wire_successor
       (delete_operation circuit operation_node_id)
       q
       (get_input_node_id q)"

proof -

  have no_input_predecessor:
    "\<nexists>predecessor_id.
       (predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have unique_input_successor:
    "has_unique_wire_successor
       circuit q (get_input_node_id q)"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have operation_has_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have operation_has_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_id where predecessor_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation circuit q"
    using operation_has_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_id where successor_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation circuit q"
    using operation_has_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire circuit operation_node_id q \<noteq> None"
    using predecessor_edge
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_predecessor where predecessor:
    "predecessor_on_wire circuit operation_node_id q =
       Some selected_predecessor"
    by (cases "predecessor_on_wire circuit operation_node_id q") auto

  have successor_not_none:
    "successor_on_wire circuit operation_node_id q \<noteq> None"
    using successor_edge
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_successor where successor:
    "successor_on_wire circuit operation_node_id q =
       Some selected_successor"
    by (cases "successor_on_wire circuit operation_node_id q") auto

  have valid_operation:
    "is_valid_operation op"
    using valid_circuit operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_wires:
    "distinct (op_qargs op)"
    using
      valid_operation
      are_well_formed_operation_nodes_def
      is_valid_circuit_def
      is_valid_operation_def
      is_well_formed_circuit_def
      operation_exists
      operation_in_circuit_def
      valid_circuit
    by blast

  let ?reconnected_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       (op_qargs op)
       circuit"

  have boundary_after_reconnection:
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation ?reconnected_circuit q)
     \<and>
     has_unique_wire_successor
       ?reconnected_circuit
       q
       (get_input_node_id q)"
    using
      fold_reconnect_preserves_input_boundary[
        OF
          no_input_predecessor
          unique_input_successor
          predecessor
          successor
          distinct_wires
          used_wire]
    by simp

  have deleted_wire_relation:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation ?reconnected_circuit q"
    
    using operation_exists
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp

  show ?thesis
    using boundary_after_reconnection deleted_wire_relation
    unfolding has_unique_wire_successor_def
    by auto

qed

lemma reconnect_wire_preserves_output_boundary:
  (* Reconnecting predecessor -> operation_node_id -> successor into
     predecessor -> successor preserves the output boundary of wire q.

     The original output node has exactly one incoming q-edge and no
     outgoing q-edge. The bypass edge cannot leave the output node. If the
     output node is the successor, its old incoming edge from
     operation_node_id is replaced by exactly one incoming edge from
     predecessor_id. Otherwise, its incoming edge is unaffected.
  *)
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (reconnect_wire
                  circuit
                  operation_node_id
                  q
                  circuit)
               q)"

proof -
  have incoming_operation_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have operation_not_output:
    "operation_node_id \<noteq> get_output_node_id q"
  proof
    assume
      "operation_node_id = get_output_node_id q"

    then have
      "(get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have predecessor_not_output:
    "predecessor_id \<noteq> get_output_node_id q"
  proof
    assume
      "predecessor_id = get_output_node_id q"

    then have
      "(get_output_node_id q, operation_node_id)
         \<in> wire_edge_relation circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have relation_after:
    "wire_edge_relation
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
     =
     insert
       (predecessor_id, successor_id)
       (wire_edge_relation circuit q
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  show ?thesis
    using
      unique_output_predecessor
      no_output_successor
      outgoing_operation_edge
      operation_not_output
      predecessor_not_output
      relation_after
    unfolding has_unique_wire_predecessor_def
    by auto

qed

lemma reconnect_wire_preserves_output_boundary_from_same_relation:
  (* During a fold, predecessor and successor are looked up in the fixed
     original circuit, while the edge rewrite is applied to the current
     accumulator.

     If the q-edge relation of the accumulator is the same as that of the
     original circuit, reconnecting q preserves the output boundary.
  *)
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         current_circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation current_circuit q"
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
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (reconnect_wire
                  original_circuit
                  operation_node_id
                  q
                  current_circuit)
               q)"

proof -
  have incoming_operation_edge_original:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have incoming_operation_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation current_circuit q"
    using incoming_operation_edge_original same_relation
    by simp

  have outgoing_operation_edge_original:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation current_circuit q"
    using outgoing_operation_edge_original same_relation
    by simp

  have operation_not_output:
    "operation_node_id \<noteq> get_output_node_id q"
  proof
    assume
      operation_is_output:
        "operation_node_id = get_output_node_id q"

    then have
      "(get_output_node_id q, successor_id)
         \<in> wire_edge_relation current_circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have predecessor_not_output:
    "predecessor_id \<noteq> get_output_node_id q"
  proof
    assume
      predecessor_is_output:
        "predecessor_id = get_output_node_id q"

    then have
      "(get_output_node_id q, operation_node_id)
         \<in> wire_edge_relation current_circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have relation_after:
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
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  show ?thesis
    using
      unique_output_predecessor
      no_output_successor
      outgoing_operation_edge
      operation_not_output
      predecessor_not_output
      relation_after
    unfolding has_unique_wire_predecessor_def
    by auto
qed

lemma fold_reconnect_preserves_output_boundary:
  (* In a distinct list of affected wires containing q, reconnections on
     wires before and after q leave q's edge relation unchanged. The single
     reconnection of q preserves its output boundary. *)
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
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
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (fold
                  (reconnect_wire circuit operation_node_id)
                  qs
                  circuit)
               q)"

proof -
  obtain before after where
    qs_decomposition:
      "qs = before @ q # after"
    using used_wire
    by (meson split_list)

  have q_not_in_before:
    "q \<notin> set before"
    using distinct_wires qs_decomposition
    by auto

  have q_not_in_after:
    "q \<notin> set after"
    using distinct_wires qs_decomposition
    by auto

  let ?before_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       before
       circuit"

  let ?q_circuit =
    "reconnect_wire
       circuit
       operation_node_id
       q
       ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q =
       wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation[
        where original_circuit = circuit
          and operation_node_id = operation_node_id
          and qs = before
          and current_circuit = circuit
          and r = q,
        OF q_not_in_before]
    by simp

  have unique_output_predecessor_before:
    "has_unique_wire_predecessor
       ?before_circuit q (get_output_node_id q)"
    using
      unique_output_predecessor
      before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have no_output_successor_before:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation ?before_circuit q"
    using
      no_output_successor
      before_same_relation
    by simp

  have boundary_after_q:
    "has_unique_wire_predecessor
       ?q_circuit
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation ?q_circuit q)"
    using
      reconnect_wire_preserves_output_boundary_from_same_relation[
        OF
          unique_output_predecessor_before
          no_output_successor_before
          before_same_relation
          predecessor
          successor]
    by simp

  have after_same_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
     =
     wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation[
        where original_circuit = circuit
          and operation_node_id = operation_node_id
          and qs = after
          and current_circuit = ?q_circuit
          and r = q,
        OF q_not_in_after]
    by simp

  show ?thesis
    using
      boundary_after_q
      after_same_relation
      qs_decomposition
    unfolding has_unique_wire_predecessor_def
    by auto
qed

lemma delete_operation_used_wire_preserves_output_boundary:
  (* Deleting an operation on wire q preserves the output boundary of q.

     The fold reconnects every affected wire. Since reconnections on other
     wires do not affect q, and reconnecting q preserves its output
     boundary, the final removal of the operation node from the node table
     leaves the output boundary unchanged.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "has_unique_wire_predecessor
       (delete_operation circuit operation_node_id)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)"

proof -
  have unique_output_predecessor:
    "has_unique_wire_predecessor
       circuit q (get_output_node_id q)"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have no_output_successor:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have operation_has_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have operation_has_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have predecessor_exists:
    "\<exists>predecessor_id.
       predecessor_on_wire
         circuit
         operation_node_id
         q
       =
       Some predecessor_id"
  
  proof -
    obtain predecessor_id where
      predecessor_relation:
        "(predecessor_id, operation_node_id)
           \<in> wire_edge_relation circuit q"
      using operation_has_predecessor
      unfolding has_unique_wire_predecessor_def
      by blast

    have incoming_edge_exists:
      "make_edge predecessor_id operation_node_id q
         \<in> edges circuit"
      using predecessor_relation
      unfolding wire_edge_relation_def
      by simp

    have incoming_exists:
      "\<exists>incoming \<in> edges circuit.
         edge_target incoming = operation_node_id
         \<and>
         edge_wire incoming = q"
    proof
      show
        "make_edge predecessor_id operation_node_id q
           \<in> edges circuit"
        using incoming_edge_exists .

      show
        "edge_target
           (make_edge predecessor_id operation_node_id q)
           =
           operation_node_id
         \<and>
         edge_wire
           (make_edge predecessor_id operation_node_id q)
           =
           q"
        unfolding make_edge_def
        by simp
    qed

    show ?thesis
      using incoming_exists
      unfolding
        predecessor_on_wire_def
        incoming_edge_def
      by simp
  qed

  obtain predecessor_id where
    predecessor:
      "predecessor_on_wire
         circuit
         operation_node_id
         q
       =
       Some predecessor_id"
    using predecessor_exists
    by blast

  have successor_exists:
    "\<exists>successor_id.
       successor_on_wire
         circuit
         operation_node_id
         q
       =
       Some successor_id"
  proof -

    obtain successor_id where
      successor_relation:
        "(operation_node_id, successor_id)
           \<in> wire_edge_relation circuit q"
      using operation_has_successor
      unfolding has_unique_wire_successor_def
      by blast

    have outgoing_edge_exists:
      "make_edge operation_node_id successor_id q
         \<in> edges circuit"
      using successor_relation
      unfolding wire_edge_relation_def
      by simp

    have outgoing_exists:
      "\<exists>outgoing \<in> edges circuit.
         edge_source outgoing = operation_node_id
         \<and>
         edge_wire outgoing = q"
    proof
      show
        "make_edge operation_node_id successor_id q
           \<in> edges circuit"
        using outgoing_edge_exists .

      show
        "edge_source
           (make_edge operation_node_id successor_id q)
           =
           operation_node_id
         \<and>
         edge_wire
           (make_edge operation_node_id successor_id q)
           =
           q"
        unfolding make_edge_def
        by simp
    qed

    show ?thesis
      using outgoing_exists
      unfolding
        successor_on_wire_def
        outgoing_edge_def
      by simp
  qed

  obtain successor_id where
    successor:
      "successor_on_wire
         circuit
         operation_node_id
         q
       =
       Some successor_id"
    using successor_exists
    by blast


  have valid_operation:
    "is_valid_operation op"
    using
      valid_circuit
      operation_exists
      are_well_formed_operation_nodes_def
      is_valid_operation_def
      is_well_formed_circuit_def
      operation_in_circuit_def
    unfolding
      is_valid_circuit_def
      is_valid_operation_def
    by simp

  then have distinct_wires:
    "distinct (op_qargs op)"
    unfolding is_valid_operation_def
    by auto

  have boundary_after_fold:
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (fold
                  (reconnect_wire circuit operation_node_id)
                  (op_qargs op)
                  circuit)
               q)"
    using
      fold_reconnect_preserves_output_boundary[
        OF
          unique_output_predecessor
          no_output_successor
          predecessor
          successor
          distinct_wires
          used_wire]
    by simp

  have relation_preserved:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q =
     wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
       q"
    unfolding
      delete_operation_def
    using operation_exists
    by (simp add: Let_def wire_edge_relation_def)

  show ?thesis
    using
      boundary_after_fold
      relation_preserved
    unfolding has_unique_wire_predecessor_def
    by auto

qed

lemma delete_operation_used_wire_preserves_operation_degrees:
  (* Every remaining operation node using q retains exactly one immediate
     predecessor and exactly one immediate successor on q.

     Nodes not adjacent to the deleted operation keep their incident
     q-edges unchanged.

     The deleted operation's predecessor loses its edge to the deleted
     node but gains the new bypass edge to the deleted node's successor.

     Similarly, the deleted operation's successor loses its incoming edge
     from the deleted node but gains the new bypass edge from the deleted
     node's predecessor.

     Since the original q-wire was linear, these rewrites preserve degree
     one and introduce no branching.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "\<forall>node_id remaining_op.
       nodes
         (delete_operation circuit operation_node_id)
         node_id
       =
       Some (OperationNode remaining_op)
       \<longrightarrow>
       node_uses_qubit (OperationNode remaining_op) q
       \<longrightarrow>
       has_unique_wire_predecessor
         (delete_operation circuit operation_node_id)
         q
         node_id
       \<and>
       has_unique_wire_successor
         (delete_operation circuit operation_node_id)
         q
         node_id"

proof (intro allI impI)

  fix node_id remaining_op

  assume remaining_operation_exists:
    "nodes
       (delete_operation circuit operation_node_id)
       node_id
     =
     Some (OperationNode remaining_op)"

  assume remaining_operation_uses_q:
    "node_uses_qubit (OperationNode remaining_op) q"

  have remaining_node:
    "node_id \<noteq> operation_node_id"
    using
      operation_exists
      remaining_operation_exists
    by auto

  have remaining_operation_exists_originally:
    "nodes circuit node_id =
       Some (OperationNode remaining_op)"
    using
      operation_exists
      remaining_node
      remaining_operation_exists
    by simp

  have remaining_unique_predecessor:
    "has_unique_wire_predecessor
       circuit q node_id"
    using
      original_linear
      remaining_operation_exists_originally
      remaining_operation_uses_q
    unfolding wire_is_linear_def
    by blast

  have remaining_unique_successor:
    "has_unique_wire_successor
       circuit q node_id"
    using
      original_linear
      remaining_operation_exists_originally
      remaining_operation_uses_q
    unfolding wire_is_linear_def
    by blast

  have deleted_operation_has_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  have deleted_operation_has_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_id where predecessor_relation:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation circuit q"
    using deleted_operation_has_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_id where successor_relation:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation circuit q"
    using deleted_operation_has_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire
       circuit operation_node_id q
     \<noteq>
     None"
    using predecessor_relation
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_predecessor where predecessor:
    "predecessor_on_wire
       circuit operation_node_id q
     =
     Some selected_predecessor"
    by (cases
        "predecessor_on_wire
           circuit operation_node_id q")
       auto

  have successor_not_none:
    "successor_on_wire
       circuit operation_node_id q
     \<noteq>
     None"
    using successor_relation
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_successor where successor:
    "successor_on_wire
       circuit operation_node_id q
     =
     Some selected_successor"
    by (cases
        "successor_on_wire
           circuit operation_node_id q")
       auto

  have original_acyclic:
    "is_acyclic_circuit circuit"
    using valid_circuit
    unfolding is_valid_circuit_def
    by simp

  have predecessor_not_deleted:
    "selected_predecessor \<noteq> operation_node_id"
  proof
    assume predecessor_is_deleted:
      "selected_predecessor = operation_node_id"

    have self_loop_edge:
      "make_edge
         operation_node_id
         operation_node_id
         q
       \<in>
       edges circuit"
      using
        predecessor_on_wire_correct[OF predecessor]
        predecessor_is_deleted
      by simp

    have self_loop_relation:
      "(operation_node_id, operation_node_id)
       \<in>
       edge_relation circuit"
      using self_loop_edge
      unfolding edge_relation_def make_edge_def
      by force

    have self_reachable:
      "(operation_node_id, operation_node_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using self_loop_relation
      by (rule r_into_trancl)

    show False
      using original_acyclic self_reachable
      unfolding is_acyclic_circuit_def acyclic_def
      by simp
  qed

  have successor_not_deleted:
    "selected_successor \<noteq> operation_node_id"
  proof
    assume successor_is_deleted:
      "selected_successor = operation_node_id"

    have self_loop_edge:
      "make_edge
         operation_node_id
         operation_node_id
         q
       \<in>
       edges circuit"
      using
        successor_on_wire_correct[OF successor]
        successor_is_deleted
      by simp

    have self_loop_relation:
      "(operation_node_id, operation_node_id)
       \<in>
       edge_relation circuit"
      using self_loop_edge
      unfolding edge_relation_def make_edge_def
      by force

    have self_reachable:
      "(operation_node_id, operation_node_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using self_loop_relation
      by (rule r_into_trancl)

    show False
      using original_acyclic self_reachable
      unfolding is_acyclic_circuit_def acyclic_def
      by simp
  qed

  have predecessor_not_successor:
    "selected_predecessor \<noteq> selected_successor"
  proof
    assume endpoints_equal:
      "selected_predecessor = selected_successor"

    have incoming_edge:
      "make_edge
         selected_predecessor
         operation_node_id
         q
       \<in>
       edges circuit"
      using predecessor_on_wire_correct[OF predecessor]
      .

    have outgoing_edge:
      "make_edge
         operation_node_id
         selected_successor
         q
       \<in>
       edges circuit"
      using successor_on_wire_correct[OF successor]
      .

    have incoming_relation:
      "(selected_predecessor, operation_node_id)
       \<in>
       edge_relation circuit"
      using incoming_edge
      unfolding edge_relation_def make_edge_def
      by force

    have outgoing_relation:
      "(operation_node_id, selected_successor)
       \<in>
       edge_relation circuit"
      using outgoing_edge
      unfolding edge_relation_def make_edge_def
      by force

    have incoming_path:
      "(selected_predecessor, operation_node_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using incoming_relation
      by (rule r_into_trancl)

    have outgoing_path:
      "(operation_node_id, selected_successor)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using outgoing_relation
      by (rule r_into_trancl)

    have endpoint_cycle:
      "(selected_predecessor, selected_successor)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using incoming_path outgoing_path
      by (rule trancl_trans)

    then have self_reachable:
      "(selected_predecessor, selected_predecessor)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using endpoints_equal
      by simp

    show False
      using
        original_acyclic
        self_reachable
      unfolding
        is_acyclic_circuit_def
        acyclic_def
      by simp
  qed

  have valid_operation:
    "is_valid_operation op"
    using
      valid_circuit
      operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_wires:
    "distinct (op_qargs op)"
    using valid_operation
    unfolding is_valid_operation_def
    by auto

  let ?reconnected_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       (op_qargs op)
       circuit"

  have degrees_after_reconnection:
    "has_unique_wire_predecessor
       ?reconnected_circuit
       q
       node_id
     \<and>
     has_unique_wire_successor
       ?reconnected_circuit
       q
       node_id"
    using
      distinct_wires
      fold_reconnect_preserves_operation_degrees
      predecessor
      predecessor_not_deleted
      predecessor_not_successor
      remaining_node
      remaining_unique_predecessor
      remaining_unique_successor
      successor
      successor_not_deleted
      used_wire
    by simp

  have deleted_wire_relation:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation
       ?reconnected_circuit
       q"
    using operation_exists
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp

  show
    "has_unique_wire_predecessor
       (delete_operation circuit operation_node_id)
       q
       node_id
     \<and>
     has_unique_wire_successor
       (delete_operation circuit operation_node_id)
       q
       node_id"
    using
      degrees_after_reconnection
      deleted_wire_relation
    unfolding
      has_unique_wire_predecessor_def
      has_unique_wire_successor_def
    by auto

qed

lemma delete_operation_preserves_linear_used_wire:
  (* If the deleted operation uses q, deletion contracts one internal node
     of the linear q-wire.

     In the original circuit, wire linearity gives the deleted node a
     unique predecessor and a unique successor on q:

         predecessor \<rightarrow> operation_node_id \<rightarrow> successor.

     reconnect_wire removes those two edges and inserts:

         predecessor \<rightarrow> successor.

     Thus:
       - the input still has no predecessor and one successor;
       - the output still has one predecessor and no successor;
       - every remaining operation node has one predecessor and one
         successor;
       - no branch is introduced;
       - comparability of all remaining q-nodes is preserved.

     Hence the contracted q-wire remains linear.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  shows
    "wire_is_linear circuit q
     \<Longrightarrow>
     wire_is_linear
       (delete_operation circuit operation_node_id)
       q"

proof -
  assume original_linear:
    "wire_is_linear circuit q"

  have comparability_after:
    "nodes_comparable_on_wire
       (delete_operation circuit operation_node_id)
       q"
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_comparability)

  have input_boundary_after:
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)
     \<and>
     has_unique_wire_successor
       (delete_operation circuit operation_node_id)
       q
       (get_input_node_id q)"
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_input_boundary)

  have output_boundary_after:
    "has_unique_wire_predecessor
       (delete_operation circuit operation_node_id)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)"
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_output_boundary)

  have operation_degrees_after:
    "\<forall>node_id remaining_op.
       nodes
         (delete_operation circuit operation_node_id)
         node_id
       =
       Some (OperationNode remaining_op)
       \<longrightarrow>
       node_uses_qubit (OperationNode remaining_op) q
       \<longrightarrow>
       has_unique_wire_predecessor
         (delete_operation circuit operation_node_id)
         q
         node_id
       \<and>
       has_unique_wire_successor
         (delete_operation circuit operation_node_id)
         q
         node_id"
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_operation_degrees)

  show
    "wire_is_linear
       (delete_operation circuit operation_node_id)
       q"
    using
      comparability_after
      input_boundary_after
      output_boundary_after
      operation_degrees_after
    unfolding wire_is_linear_def
    by simp
qed

lemma delete_operation_preserves_wire_is_linear:
  (* Deleting an operation preserves the linear structure of one valid wire.

     There are two cases for wire q:

       1. The deleted operation does not use q.

          In this case, delete_operation does not reconnect q. The edges
          on q remain unchanged, and removing an operation that does not
          use q does not remove any node belonging to q. Therefore, the
          original linear chain on q is preserved.

       2. The deleted operation uses q.

          Since the original wire is linear, operation_node_id has exactly
          one predecessor and exactly one successor on q. Deletion removes

              predecessor \<rightarrow> operation_node_id
              operation_node_id \<rightarrow> successor

          and replaces them with

              predecessor \<rightarrow> successor.

          This contracts one internal node of the wire chain. It does not
          introduce branching, disconnect the wire, alter the boundary-node
          conditions, or destroy comparability among the remaining nodes.

     Therefore, every valid wire remains linear after deletion.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    valid_wire_after:
      "qubit_in_circuit
         (delete_operation circuit operation_node_id)
         q"
  shows
    "wire_is_linear
       (delete_operation circuit operation_node_id)
       q"
  by (metis
      all_wires_linear_def
      delete_operation_preserves_linear_unused_wire
      delete_operation_preserves_linear_used_wire
      delete_operation_preserves_num_qubits
      is_valid_circuit_def
      operation_exists
      qubit_in_circuit_def
      valid_circuit
      valid_wire_after)

lemma delete_operation_preserves_wire_linearity:
  (* Deleting an operation preserves linearity of every circuit wire.

     The number of qubits is unchanged by deletion. Hence, any qubit that
     is valid after deletion was also valid before deletion.

     The original circuit satisfies all_wires_linear because it is a valid
     circuit. For an arbitrary valid wire q, the preceding helper theorem
     shows that deleting operation_node_id preserves wire_is_linear on q.

     Since q was arbitrary, every valid wire in the resulting circuit is
     linear.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "all_wires_linear
       (delete_operation circuit operation_node_id)"

proof -
  show ?thesis
    unfolding all_wires_linear_def

  proof (intro allI impI)

    fix q

    assume valid_wire_after:
      "qubit_in_circuit
         (delete_operation circuit operation_node_id)
         q"

    show
      "wire_is_linear
         (delete_operation circuit operation_node_id)
         q"
      using
        valid_circuit
        operation_exists
        valid_wire_after
      by (rule delete_operation_preserves_wire_is_linear)
  qed
qed

lemma delete_operation_preserves_valid_circuit:
  (* Deleting an operation preserves every structural invariant of a
     valid circuit: well-formedness, acyclicity, and wire linearity.
  *)
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
    "is_valid_circuit
       (delete_operation circuit operation_node_id)"

proof -
  have well_formed:
    "is_well_formed_circuit
       (delete_operation circuit operation_node_id)"
    using
      valid_state
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_well_formed_circuit)

  have acyclic:
    "is_acyclic_circuit
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_acyclicity)

  have linear:
    "all_wires_linear
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_wire_linearity)

  show ?thesis
    unfolding is_valid_circuit_def
    using well_formed acyclic linear
    by simp
qed

end
