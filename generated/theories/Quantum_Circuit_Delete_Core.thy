theory Quantum_Circuit_Delete_Core
  imports Quantum_Circuit_Navigation

begin

definition reconnect_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
where
  (* Reconnect one wire around the operation node being deleted.

     The first circuit is the original circuit used to determine the
     predecessor and successor. The final circuit is the accumulating
     circuit whose edge set is modified by the fold.
  *)
  "reconnect_wire original_circuit node_id q current_circuit =
     (case
        (predecessor_on_wire original_circuit node_id q,
         successor_on_wire original_circuit node_id q)
      of
        (Some predecessor, Some successor) \<Rightarrow>
          insert_edge
            (make_edge predecessor successor q)
            (delete_edge
              (make_edge node_id successor q)
              (delete_edge
                (make_edge predecessor node_id q)
                current_circuit))
      | _ \<Rightarrow> current_circuit)"

definition delete_operation ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> quantum_circuit"
where
  (* Delete an operation node while reconnecting every wire used by it.

     Suppose the node contains operation op and, on an affected wire q,
     the local structure is

         predecessor \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> node_id \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> successor.

     Deletion performs the following rewrite:

         1. remove predecessor \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> node_id;
         2. remove node_id \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> successor;
         3. insert predecessor \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> successor.

     This rewrite is repeated for every qubit in op_qargs op. After all
     affected wires have been reconnected, the operation node is removed
     from the node table by mapping node_id to None.

     next_id is deliberately left unchanged. Deleted node IDs are not
     reused, so the monotonic node-allocation invariant remains compatible
     with later insertions.

     If node_id does not contain an OperationNode, the circuit is returned
     unchanged. If either adjacent node cannot be found on some affected
     wire, that wire is also left unchanged.
  *)
  "delete_operation circuit node_id =
     (case nodes circuit node_id of
        Some (OperationNode op) \<Rightarrow>
          (let
             reconnected_circuit =
               fold
                 (reconnect_wire circuit node_id)
                 (op_qargs op)
                 circuit
           in
             reconnected_circuit
               \<lparr>nodes :=
                  (nodes reconnected_circuit)
                    (node_id := None)\<rparr>)
      | _ \<Rightarrow> circuit)"

lemma reconnect_wire_preserves_nodes[simp]:
  (* Reconnecting one wire changes only the edge set. It does not change
     the node table. *)
  "nodes
     (reconnect_wire original_circuit operation_node_id q circuit)
     node_id
   =
   nodes circuit node_id"

  unfolding reconnect_wire_def
  apply (auto split: option.splits)
  by (simp add: delete_edge_def insert_edge_def)

lemma fold_reconnect_wire_preserves_nodes[simp]:
  (* Reconnecting any list of wires preserves the complete node table. *)
  "nodes
     (fold
        (reconnect_wire original_circuit operation_node_id)
        qs
        circuit)
     node_id
   =
   nodes circuit node_id"

proof (induction qs arbitrary: circuit)

  case Nil

  show ?case
    by simp

next

  case (Cons q qs)

  show ?case
    using Cons.IH
    by simp

qed

lemma delete_operation_nodes:
  (* When operation_node_id stores an OperationNode, deletion preserves
     every node-table entry except operation_node_id, which is mapped to
     None. *)
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "nodes
       (delete_operation circuit operation_node_id)
     =
     (nodes circuit)(operation_node_id := None)"

proof -

  have reconnected_nodes:
    "nodes
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
     =
     nodes circuit"

  proof (rule ext)

    fix node_id

    show
      "nodes
         (fold
            (reconnect_wire circuit operation_node_id)
            (op_qargs op)
            circuit)
         node_id
       =
       nodes circuit node_id"
      by simp

  qed

  show ?thesis
    unfolding delete_operation_def
    using operation_exists reconnected_nodes
    by simp

qed

lemma delete_operation_other_node[simp]:
  (* Deleting one operation does not change any other node-table entry. *)
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    different_node:
      "other_node_id \<noteq> operation_node_id"
  shows
    "nodes
       (delete_operation circuit operation_node_id)
       other_node_id
     =
     nodes circuit other_node_id"

  using
    delete_operation_nodes[OF operation_exists]
    different_node
  by simp

lemma reconnect_wire_edges_characterisation:
  (* Reconnecting a wire removes the two edges incident on the deleted
     operation node and inserts the corresponding bypass edge. *)
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q =
         Some successor_id"
  shows
    "edges
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
     =
     insert
       (make_edge predecessor_id successor_id q)
       (edges current_circuit
          - { make_edge predecessor_id operation_node_id q,
              make_edge operation_node_id successor_id q })"

  unfolding
    reconnect_wire_def
    insert_edge_def
    delete_edge_def
    make_edge_def
  using predecessor successor
  by auto

lemma reconnect_wire_successor_predecessor_characterisation:
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q =
         Some successor_id"
  shows
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
          - {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"

proof -

  have
    "edges
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
     =
     insert
       (make_edge predecessor_id successor_id q)
       (edges current_circuit
          -
          { make_edge predecessor_id operation_node_id q,
            make_edge operation_node_id successor_id q })"
    using assms
    by (rule reconnect_wire_edges_characterisation)

  then show ?thesis
    unfolding wire_edge_relation_def make_edge_def
    by auto

qed

lemma reconnect_wire_preserves_input_boundary:
  (* Reconnecting predecessor -> operation_node_id -> successor into
     predecessor -> successor preserves the input boundary of wire q.

     The original input node has no incoming q-edge and exactly one outgoing
     q-edge. The bypass edge cannot enter the input node. If the input node
     is the predecessor, its old edge to operation_node_id is replaced by
     exactly one edge to successor_id. Otherwise, its outgoing edge is
     unaffected.
  *)
  assumes
    no_input_predecessor:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_id"
  shows
    "(\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation
                (reconnect_wire
                   circuit
                   operation_node_id
                   q
                   circuit)
                q)
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
       (get_input_node_id q)"

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

  have operation_not_input:
    "operation_node_id \<noteq> get_input_node_id q"
  proof
    assume
      "operation_node_id = get_input_node_id q"

    then have
      "(predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_input_predecessor
      by blast
  qed

  have successor_not_input:
    "successor_id \<noteq> get_input_node_id q"
  proof
    assume
      "successor_id = get_input_node_id q"

    then have
      "(operation_node_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_input_predecessor
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
    unfolding has_unique_wire_successor_def
    using
      no_input_predecessor
      unique_input_successor
      incoming_operation_edge
      operation_not_input
      successor_not_input
      relation_after
    unfolding has_unique_wire_successor_def
    by auto
qed

lemma reconnect_wire_preserves_input_boundary_from_same_relation:
  (* During a fold, predecessor and successor are always looked up in the
     fixed original circuit, while the edge rewrite is applied to the
     current accumulator.

     If the current accumulator still has the same q-edge relation as the
     original circuit, then reconnecting q preserves the input boundary
     on q.
  *)
  assumes
    no_input_predecessor:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation current_circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         current_circuit q (get_input_node_id q)"
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
    "(\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation
                (reconnect_wire
                   original_circuit
                   operation_node_id
                   q
                   current_circuit)
                q)
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       (get_input_node_id q)"

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

  have operation_not_input:
    "operation_node_id \<noteq> get_input_node_id q"
  proof
    assume
      "operation_node_id = get_input_node_id q"

    then have
      "(predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation current_circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_input_predecessor
      by blast
  qed

  have successor_not_input:
    "successor_id \<noteq> get_input_node_id q"
  proof
    assume
      "successor_id = get_input_node_id q"

    then have
      "(operation_node_id, get_input_node_id q)
         \<in> wire_edge_relation current_circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_input_predecessor
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
      no_input_predecessor
      unique_input_successor
      incoming_operation_edge
      operation_not_input
      successor_not_input
      relation_after
    unfolding has_unique_wire_successor_def
    by auto

qed

lemma reconnect_wire_preserves_other_wire_relation:
  (* Reconnecting the deleted node on wire q changes only q-labelled
     edges. Therefore, the immediate-edge relation of every different
     wire r remains unchanged. *)
  assumes
    different_wire:
      "r \<noteq> q"
  shows
    "wire_edge_relation
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       r
     =
     wire_edge_relation current_circuit r"

  unfolding
    reconnect_wire_def
    wire_edge_relation_def
    insert_edge_def
    delete_edge_def
    make_edge_def
  using different_wire
  by (auto split: option.splits)

lemma fold_reconnect_preserves_other_wire_relation:
  (* Reconnecting an entire list of wires different from r never changes
     the immediate edge relation on wire r. *)
  fixes r
  assumes other_wire:
    "r \<notin> set qs"
  shows
    "wire_edge_relation
       (fold
          (reconnect_wire
             original_circuit
             operation_node_id)
          qs
          current_circuit)
       r
     =
     wire_edge_relation current_circuit r"
  using other_wire

proof (induction qs arbitrary: current_circuit)

  case Nil

  show ?case
    by simp

next

  case (Cons q qs)
  
  have q_neq:
    "r \<noteq> q"
    using Cons.prems
    by simp

  have qs_not_contains:
    "r \<notin> set qs"
    using Cons.prems
    by simp

  show ?case
    using
      reconnect_wire_preserves_other_wire_relation[OF q_neq]
      Cons.IH[OF qs_not_contains]
    by simp

qed

lemma fold_reconnect_preserves_input_boundary:
  (* In a distinct list of affected wires containing q, all wires before
     and after q leave q's relation unchanged. The single reconnection of
     q preserves its input boundary. *)
  assumes
    no_input_predecessor:
      "\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
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
    "(\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation
                (fold
                   (reconnect_wire circuit operation_node_id)
                   qs
                   circuit)
                q)
     \<and>
     has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       (get_input_node_id q)"

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

  have no_input_predecessor_before:
    "\<nexists>pred.
       (pred, get_input_node_id q)
         \<in> wire_edge_relation ?before_circuit q"
    using
      no_input_predecessor
      before_same_relation
    by simp

  have unique_input_successor_before:
    "has_unique_wire_successor
       ?before_circuit q (get_input_node_id q)"
    using
      unique_input_successor
      before_same_relation
    unfolding has_unique_wire_successor_def
    by auto

  have boundary_after_q:
    "(\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation ?q_circuit q)
     \<and>
     has_unique_wire_successor
       ?q_circuit q (get_input_node_id q)"
    using
      reconnect_wire_preserves_input_boundary_from_same_relation[
        OF
          no_input_predecessor_before
          unique_input_successor_before
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
    unfolding has_unique_wire_successor_def
    by auto

qed

lemma delete_operation_removes_operation_node[simp]:
  (* If node_id stores an OperationNode, then deleting that operation
     removes it from the circuit. *)

  assumes operation_node:
    "nodes circuit node_id = Some (OperationNode op)"

  shows
    "nodes (delete_operation circuit node_id) node_id = None"

proof -

  have delete_case:
    "delete_operation circuit node_id =
      (let
         reconnect_wire =
           (\<lambda>q current_circuit.
              case
                (predecessor_on_wire circuit node_id q,
                 successor_on_wire circuit node_id q)
              of

                (Some predecessor, Some successor) \<Rightarrow>
                  insert_edge
                    (make_edge predecessor successor q)
                    (delete_edge
                      (make_edge node_id successor q)
                      (delete_edge
                        (make_edge predecessor node_id q)
                        current_circuit))

              | _ \<Rightarrow> current_circuit);

         reconnected_circuit =
           fold
             reconnect_wire
             (op_qargs op)
             circuit;

         circuit_without_node =
           reconnected_circuit
             \<lparr>nodes :=
                (nodes reconnected_circuit)
                  (node_id := None)\<rparr>

       in
         circuit_without_node)"
    using operation_node 
    unfolding
      delete_operation_def
      Let_def
      reconnect_wire_def
    by simp

  show ?thesis
    unfolding
      delete_case
      Let_def
    by simp
qed

lemma reconnect_wire_preserves_num_qubits:
  (* Reconnecting a single wire only updates the circuit's edge set.
     It does not change the number of qubits in the circuit. *)
  "num_qubits
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   num_qubits current_circuit"
  
  unfolding
    reconnect_wire_def
    delete_edge_def 
    insert_edge_def

  by (auto split:
        option.splits
        prod.splits)

lemma reconnect_wire_edge_cases:
  (* Every edge present after reconnecting one wire is either:

       1. an edge that was already present in the accumulating circuit; or
       2. the new direct predecessor-to-successor edge inserted on q.

     This lemma deliberately over-approximates the old-edge case: some old
     incident edges may have been deleted, but every surviving old edge
     certainly belonged to current_circuit.
  *)
  assumes
    edge_after:
      "e \<in>
       edges
         (reconnect_wire
           original_circuit
           operation_node_id
           q
           current_circuit)"
  shows
    "e \<in> edges current_circuit
     \<or>
     (\<exists>predecessor successor. predecessor_on_wire original_circuit operation_node_id q
        = Some predecessor
      \<and>
        successor_on_wire original_circuit operation_node_id q
        = Some successor
      \<and>
        e = make_edge predecessor successor q)"
proof -
  show ?thesis
    using edge_after
    unfolding reconnect_wire_def
    by (auto
          split:
            option.splits
            prod.splits)
qed

lemma fold_reconnect_wire_edge_cases:
  (*
    Every edge present after reconnecting a list of wires is either an
    original edge or a bypass edge introduced while processing one wire
    from that list.
  *)
  assumes
    edge_after:
      "e \<in>
       edges
         (fold
           (reconnect_wire original_circuit operation_node_id)
           qs
           current_circuit)"
  shows
    "e \<in> edges current_circuit
     \<or>
     (\<exists>q \<in> set qs.
        \<exists>predecessor successor.
          predecessor_on_wire
            original_circuit operation_node_id q
            = Some predecessor
        \<and>
          successor_on_wire
            original_circuit operation_node_id q
            = Some successor
        \<and>
          e = make_edge predecessor successor q)"
  
  using edge_after

proof (induction qs arbitrary: current_circuit)

  case Nil

  (*
    Folding over an empty wire list leaves the accumulating circuit
    unchanged. Therefore, every resulting edge is already an edge of
    current_circuit.
  *)
  then show ?case
    by simp

next

  case (Cons q qs)

  (*
    The first fold step reconnects q. The remaining wires qs are then
    processed using that updated circuit as the new accumulator.
  *)
  let ?updated_circuit =
    "reconnect_wire
       original_circuit
       operation_node_id
       q
       current_circuit"

  have edge_after_remaining_wires:
    "e \<in>
     edges
       (fold
         (reconnect_wire original_circuit operation_node_id)
         qs
         ?updated_circuit)"
    using Cons.prems
    by simp

  (*
    Apply the induction hypothesis to the remaining fold. The edge is
    either already present immediately after reconnecting q, or it is a
    bypass edge introduced while processing one of the later wires in qs.
  *)
  have remaining_wire_cases:
    "e \<in> edges ?updated_circuit
     \<or>
     (\<exists>q' \<in> set qs.
        \<exists>predecessor successor.
          predecessor_on_wire
            original_circuit operation_node_id q'
            = Some predecessor
        \<and>
          successor_on_wire
            original_circuit operation_node_id q'
            = Some successor
        \<and>
          e = make_edge predecessor successor q')"
    using Cons.IH[of ?updated_circuit]
          edge_after_remaining_wires
    by blast

    from remaining_wire_cases show ?case
  proof

    assume edge_after_first_reconnection:
      "e \<in> edges ?updated_circuit"

    have first_wire_cases:
      "e \<in> edges current_circuit
       \<or>
       (\<exists>predecessor successor.
          predecessor_on_wire
            original_circuit operation_node_id q
            = Some predecessor
        \<and>
          successor_on_wire
            original_circuit operation_node_id q
            = Some successor
        \<and>
          e = make_edge predecessor successor q)"
      using edge_after_first_reconnection
      by (rule reconnect_wire_edge_cases)

    then show ?thesis
      by auto

  next

    assume bypass_on_remaining_wire:
      "\<exists>q' \<in> set qs.
         \<exists>predecessor successor.
           predecessor_on_wire
             original_circuit operation_node_id q'
             = Some predecessor
         \<and>
           successor_on_wire
             original_circuit operation_node_id q'
             = Some successor
         \<and>
           e = make_edge predecessor successor q'"

    then show ?thesis
      by simp
  qed
qed

lemma reconnect_wire_inserted_edge_well_formed:
  (*
    Whenever reconnect_wire inserts a bypass edge, that edge is
    well formed in the resulting circuit.

    reconnect_wire modifies only the edge set. Therefore the node table
    and qubit count remain unchanged, while the predecessor and successor
    already satisfy the endpoint conditions inherited from the original
    well-formed edges.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_node_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_node_id"
  shows
    "is_well_formed_edge
       (reconnect_wire circuit operation_node_id q circuit)
       (make_edge predecessor_node_id successor_node_id q)"

proof -

  (*
    Structural validity of the original circuit guarantees that every
    edge already present in it is well formed.
  *)
  have original_edges_well_formed:
    "are_well_formed_edges circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  (*
    predecessor_on_wire identifies an existing edge entering
    operation_node_id from predecessor_node_id on q.
  *)
  have predecessor_edge:
    "make_edge predecessor_node_id operation_node_id q
       \<in> edges circuit"
    using predecessor
    by (rule predecessor_on_wire_correct)

  (*
    successor_on_wire identifies an existing edge leaving
    operation_node_id toward successor_node_id on q.
  *)
  have successor_edge:
    "make_edge operation_node_id successor_node_id q
       \<in> edges circuit"
    using successor
    by (rule successor_on_wire_correct)

  (* Both incident edges are well formed in the original valid circuit. *)
  have predecessor_edge_well_formed:
    "is_well_formed_edge
       circuit
       (make_edge predecessor_node_id operation_node_id q)"
    using original_edges_well_formed predecessor_edge
    unfolding are_well_formed_edges_def
    by blast

  have successor_edge_well_formed:
    "is_well_formed_edge
       circuit
       (make_edge operation_node_id successor_node_id q)"
    using original_edges_well_formed successor_edge
    unfolding are_well_formed_edges_def
    by blast

  (*
    From the incoming edge, obtain everything needed about the new bypass
    edge's source:

      • predecessor_node_id exists;
      • q is a valid circuit qubit;
      • the predecessor node lies on q.
  *)
  have predecessor_properties:
    "node_exists circuit predecessor_node_id
     \<and> qubit_in_circuit circuit q
     \<and>
       (case nodes circuit predecessor_node_id of
          None \<Rightarrow> False
        | Some predecessor_node \<Rightarrow>
            node_uses_qubit predecessor_node q)"
    using
      predecessor_edge_well_formed
      is_well_formed_edge_def
    unfolding
      make_edge_def
    by (metis edge.select_convs(1,3))

  (*
    From the outgoing edge, obtain the corresponding properties of the
    new bypass edge's target.
  *)
  have successor_properties:
    "node_exists circuit successor_node_id
     \<and>
       (case nodes circuit successor_node_id of
          None \<Rightarrow> False
        | Some successor_node \<Rightarrow>
            node_uses_qubit successor_node q)"
    using successor_edge_well_formed
    unfolding
      is_well_formed_edge_def
      make_edge_def
    by (metis edge.select_convs(2,3))

  (*
    reconnect_wire changes only the edge set. Hence the predecessor and
    successor node entries, together with the circuit's qubit count, are
    identical before and after reconnection.
  *)
  have predecessor_node_preserved:
    "nodes
       (reconnect_wire circuit operation_node_id q circuit)
       predecessor_node_id
     =
     nodes circuit predecessor_node_id"
    by (rule reconnect_wire_preserves_nodes)

  have successor_node_preserved:
    "nodes
       (reconnect_wire circuit operation_node_id q circuit)
       successor_node_id
     =
     nodes circuit successor_node_id"
    by (rule reconnect_wire_preserves_nodes)

  have num_qubits_preserved:
    "num_qubits
       (reconnect_wire circuit operation_node_id q circuit)
     =
     num_qubits circuit"
    by (rule reconnect_wire_preserves_num_qubits)

  (*
    The bypass edge therefore has two existing endpoints that both use q,
    and q remains valid in the reconnected circuit.
  *)
  show ?thesis
    using
      predecessor_properties
      successor_properties
      predecessor_node_preserved
      successor_node_preserved
      num_qubits_preserved
    unfolding
      is_well_formed_edge_def
      node_exists_def
      qubit_in_circuit_def
      make_edge_def
    by (simp add: option.case_eq_if)
qed

lemma fold_reconnect_wire_preserves_num_qubits:
  (* Reconnecting every wire in a list preserves the circuit's qubit count.
     This lifts the single-wire preservation result across the fold. *)
  "num_qubits
     (fold
       (reconnect_wire original_circuit node_id)
       qs
       current_circuit)
   =
   num_qubits current_circuit"

proof (induction qs arbitrary: current_circuit)
  case Nil

  then show ?case
    by simp

next
  case (Cons q qs)

  have first_reconnection:
    "num_qubits
       (reconnect_wire
         original_circuit
         node_id
         q
         current_circuit)
     =
     num_qubits current_circuit"
    by (rule reconnect_wire_preserves_num_qubits)

  have remaining_reconnections:
    "num_qubits
       (fold
         (reconnect_wire original_circuit node_id)
         qs
         (reconnect_wire
           original_circuit
           node_id
           q
           current_circuit))
     =
     num_qubits
       (reconnect_wire
         original_circuit
         node_id
         q
         current_circuit)"
    using Cons
    by simp

  show ?case
    using first_reconnection remaining_reconnections
    by simp
qed

lemma operation_incident_edge_on_wire_cases:
  (*
    In a valid circuit, every edge on q that is incident to an operation
    node is exactly the unique incoming edge selected by
    predecessor_on_wire or the unique outgoing edge selected by
    successor_on_wire.

    This connects the abstract wire-linearity invariant with the concrete
    edges removed by reconnect_wire.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    operation_uses_wire:
      "q \<in> set (op_qargs op)"
  and
    incident_edge:
      "e \<in> edges circuit"
  and
    edge_on_wire:
      "edge_wire e = q"
  and
    incident:
      "edge_source e = operation_node_id
       \<or> edge_target e = operation_node_id"
  shows
    "(\<exists>predecessor.
        predecessor_on_wire circuit operation_node_id q =
          Some predecessor
      \<and>
        e = make_edge predecessor operation_node_id q)
     \<or>
     (\<exists>successor.
        successor_on_wire circuit operation_node_id q =
          Some successor
      \<and>
        e = make_edge operation_node_id successor q)"
proof -

  (* The stored operation is well formed, so every qubit it uses is a
     valid circuit qubit. *)
  have operation_in_circuit:
    "operation_in_circuit circuit op"
    using valid_circuit operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
    by blast

  have valid_q:
    "qubit_in_circuit circuit q"
    using operation_in_circuit operation_uses_wire
    unfolding operation_in_circuit_def
    by blast

  (* Validity also guarantees that q forms a linear wire. *)
  have linear_q:
    "wire_is_linear circuit q"
    using valid_circuit valid_q
    unfolding
      is_valid_circuit_def
      all_wires_linear_def
    by blast

  (* Since OperationNode op uses q, wire linearity gives a unique
     predecessor and a unique successor on that wire. *)
  have unique_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using
      linear_q
      operation_exists
      operation_uses_wire
    unfolding wire_is_linear_def
    by simp

  have unique_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using
      linear_q
      operation_exists
      operation_uses_wire
    unfolding wire_is_linear_def
    by simp

  from incident show ?thesis
  proof

    assume source_is_operation:
      "edge_source e = operation_node_id"

    (* The given edge itself witnesses an outgoing q-edge from the
       operation node. *)
    have given_successor_relation:
      "(operation_node_id, edge_target e)
       \<in> wire_edge_relation circuit q"
      using
        incident_edge
        source_is_operation
        edge_on_wire
      unfolding wire_edge_relation_def
      by (cases e) (simp add: make_edge_def)

    (* Obtain the unique successor promised by wire linearity. *)
    obtain unique_successor_id where
      successor_relation:
        "(operation_node_id, unique_successor_id)
         \<in> wire_edge_relation circuit q"
    and
      successor_unique:
        "\<And>candidate.
           (operation_node_id, candidate)
           \<in> wire_edge_relation circuit q
           \<Longrightarrow>
           candidate = unique_successor_id"
      using unique_successor
      unfolding has_unique_wire_successor_def
      by blast

    (* The concrete given edge must target that unique successor. *)
    have target_is_unique_successor:
      "edge_target e = unique_successor_id"
      using successor_unique given_successor_relation
      by blast

    (* successor_on_wire returns some outgoing q-edge. Its target must
       therefore equal the same unique successor. *)
    have outgoing_exists:
      "\<exists>outgoing.
         outgoing_edge circuit operation_node_id q =
           Some outgoing"
    proof -
      have
        "\<exists>outgoing \<in> edges circuit.
           edge_source outgoing = operation_node_id
         \<and> edge_wire outgoing = q"
        using
          incident_edge
          source_is_operation
          edge_on_wire
        by blast

      then show ?thesis
        unfolding outgoing_edge_def
        by (auto intro: someI_ex)
    qed

    then obtain outgoing where
      outgoing:
        "outgoing_edge circuit operation_node_id q =
           Some outgoing"
      by blast

    have outgoing_properties:
      "outgoing \<in> edges circuit
       \<and> edge_source outgoing = operation_node_id
       \<and> edge_wire outgoing = q"
      using outgoing
      by (rule outgoing_edge_correct)

    have selected_successor_relation:
      "(operation_node_id, edge_target outgoing)
       \<in> wire_edge_relation circuit q"
      using outgoing_properties
      unfolding wire_edge_relation_def
      by (cases outgoing) (simp add: make_edge_def)

    have selected_target:
      "edge_target outgoing = unique_successor_id"
      using successor_unique selected_successor_relation
      by blast

    have successor_lookup:
      "successor_on_wire circuit operation_node_id q =
         Some unique_successor_id"
      using outgoing selected_target
      unfolding successor_on_wire_def
      by simp

    (* The record fields determine e completely. *)
    have edge_shape:
      "e =
       make_edge
         operation_node_id
         unique_successor_id
         q"
      using
        source_is_operation
        target_is_unique_successor
        edge_on_wire
      by (cases e) (simp add: make_edge_def)

    show ?thesis
      using successor_lookup edge_shape
      by blast

  next

    assume target_is_operation:
      "edge_target e = operation_node_id"

    (* The given edge itself witnesses an incoming q-edge to the
       operation node. *)
    have given_predecessor_relation:
      "(edge_source e, operation_node_id)
       \<in> wire_edge_relation circuit q"
      using
        incident_edge
        target_is_operation
        edge_on_wire
      unfolding wire_edge_relation_def
      by (cases e) (simp add: make_edge_def)

    (* Obtain the unique predecessor promised by wire linearity. *)
    obtain unique_predecessor_id where
      predecessor_relation:
        "(unique_predecessor_id, operation_node_id)
         \<in> wire_edge_relation circuit q"
    and
      predecessor_unique:
        "\<And>candidate.
           (candidate, operation_node_id)
           \<in> wire_edge_relation circuit q
           \<Longrightarrow>
           candidate = unique_predecessor_id"
      using unique_predecessor
      unfolding has_unique_wire_predecessor_def
      by blast

    (* The concrete given edge must originate at that unique predecessor. *)
    have source_is_unique_predecessor:
      "edge_source e = unique_predecessor_id"
      using predecessor_unique given_predecessor_relation
      by blast

    (* predecessor_on_wire returns some incoming q-edge. Its source must
       therefore equal the same unique predecessor. *)
    have incoming_exists:
      "\<exists>incoming.
         incoming_edge circuit operation_node_id q =
           Some incoming"
    proof -
      have
        "\<exists>incoming \<in> edges circuit.
           edge_target incoming = operation_node_id
         \<and> edge_wire incoming = q"
        using
          incident_edge
          target_is_operation
          edge_on_wire
        by blast

      then show ?thesis
        unfolding incoming_edge_def
        by (auto intro: someI_ex)
    qed

    then obtain incoming where
      incoming:
        "incoming_edge circuit operation_node_id q =
           Some incoming"
      by blast

    have incoming_properties:
      "incoming \<in> edges circuit
       \<and> edge_target incoming = operation_node_id
       \<and> edge_wire incoming = q"
      using incoming
      by (rule incoming_edge_correct)

    have selected_predecessor_relation:
      "(edge_source incoming, operation_node_id)
       \<in> wire_edge_relation circuit q"
      using incoming_properties
      unfolding wire_edge_relation_def
      by (cases incoming) (simp add: make_edge_def)

    have selected_source:
      "edge_source incoming = unique_predecessor_id"
      using predecessor_unique selected_predecessor_relation
      by blast

    have predecessor_lookup:
      "predecessor_on_wire circuit operation_node_id q =
         Some unique_predecessor_id"
      using incoming selected_source
      unfolding predecessor_on_wire_def
      by simp

    (* The record fields determine e completely. *)
    have edge_shape:
      "e =
       make_edge
         unique_predecessor_id
         operation_node_id
         q"
      using
        source_is_unique_predecessor
        target_is_operation
        edge_on_wire
      by (cases e) (simp add: make_edge_def)

    show ?thesis
      using
        predecessor_lookup
        edge_shape
      by blast
  qed
qed

lemma fold_reconnect_wire_removes_incident_edges:
  (*
    After reconnecting every wire used by the deleted operation, no edge
    remaining in the accumulated circuit is incident to that operation
    node.

    Every edge incident to operation_node_id lies on a wire in op_qargs op.
    Processing that wire removes the corresponding incoming or outgoing
    edge. Later reconnection steps cannot recreate an edge incident to the
    operation node, because they insert only predecessor-to-successor
    bypass edges.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in>
       edges
         (fold
           (reconnect_wire circuit operation_node_id)
           (op_qargs op)
           circuit)"
  shows
    "edge_source e \<noteq> operation_node_id
     \<and> edge_target e \<noteq> operation_node_id"
proof -

  (* The operation stored at operation_node_id is valid. In particular,
     its qubit arguments are pairwise distinct. *)
  have operation_valid:
    "is_valid_operation op"
    using valid_circuit operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_operation_wires:
    "distinct (op_qargs op)"
    using operation_valid
    unfolding is_valid_operation_def
    by simp

  (* Every original edge is well formed. This will let us infer that an
     edge incident to OperationNode op lies on one of op_qargs op. *)
  have original_edges_well_formed:
    "are_well_formed_edges circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  (* The original circuit is acyclic, so neither a predecessor nor a
     successor selected around operation_node_id can equal that node. *)
  have original_acyclic:
    "is_acyclic_circuit circuit"
    using valid_circuit
    unfolding is_valid_circuit_def
    by simp

  show ?thesis
  proof (rule ccontr)

    assume not_non_incident:
      "\<not>
        (edge_source e \<noteq> operation_node_id
         \<and> edge_target e \<noteq> operation_node_id)"

    then have incident:
      "edge_source e = operation_node_id
       \<or> edge_target e = operation_node_id"
      by simp

    (* Every edge produced by the fold is either inherited from the
       original circuit or is a newly inserted bypass edge. *)
    have edge_origin:
      "e \<in> edges circuit
       \<or>
       (\<exists>q \<in> set (op_qargs op).
          \<exists>predecessor successor.
            predecessor_on_wire
              circuit operation_node_id q
              = Some predecessor
          \<and>
            successor_on_wire
              circuit operation_node_id q
              = Some successor
          \<and>
            e = make_edge predecessor successor q)"
      using remaining_edge
      by (rule fold_reconnect_wire_edge_cases)

    from edge_origin show False
    proof

      assume original_edge:
        "e \<in> edges circuit"

      (* Since e is well formed and touches OperationNode op, its wire must
         be one of the operation's qubit arguments. *)
      have original_edge_well_formed:
        "is_well_formed_edge circuit e"
        using original_edges_well_formed original_edge
        unfolding are_well_formed_edges_def
        by simp

      have edge_wire_used_by_operation:
        "edge_wire e \<in> set (op_qargs op)"
        using
          original_edge_well_formed
          operation_exists
          incident
        unfolding
          is_well_formed_edge_def
          node_exists_def
        by (auto split: option.splits)

      let ?q = "edge_wire e"

      (* The helper identifies e as exactly the incoming or outgoing edge
         selected by reconnect_wire on its wire. *)
      have selected_edge_cases:
        "(\<exists>predecessor.
            predecessor_on_wire
              circuit operation_node_id ?q
              = Some predecessor
          \<and>
            e = make_edge predecessor operation_node_id ?q)
         \<or>
         (\<exists>successor.
            successor_on_wire
              circuit operation_node_id ?q
              = Some successor
          \<and>
            e = make_edge operation_node_id successor ?q)"
        using
          valid_circuit
          operation_exists
          edge_wire_used_by_operation
          original_edge
          incident
          operation_incident_edge_on_wire_cases
        by simp

      (*
        Reconnecting a different wire cannot insert e, because every edge
        inserted on that step carries that different wire. Since the
        operation's wire list is distinct, e is removed when ?q is
        processed and cannot be recreated later.
      *)
      have selected_edge_removed:
        "e \<notin>
         edges
           (fold
             (reconnect_wire circuit operation_node_id)
             (op_qargs op)
             circuit)"
      proof -
        obtain before after where
          operation_wires_split:
            "op_qargs op = before @ ?q # after"
          using edge_wire_used_by_operation
          by (metis split_list)

        have q_not_in_before:
          "?q \<notin> set before"
        and
          q_not_in_after:
          "?q \<notin> set after"
          using
            distinct_operation_wires
            operation_wires_split
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
             ?q
             ?before_circuit"

        (* Both adjacent lookups exist. Whichever side of the operation e
           occupies, wire linearity supplies the other side as well. *)
                have predecessor_exists:
          "\<exists>predecessor.
             predecessor_on_wire
               circuit operation_node_id ?q
             = Some predecessor"
        proof -

          (* Wire linearity guarantees that the operation has an incoming
             neighbour on ?q. *)
          obtain predecessor where
            predecessor_relation:
              "(predecessor, operation_node_id)
               \<in> wire_edge_relation circuit ?q"
            using
              valid_circuit
              operation_exists
              edge_wire_used_by_operation
              are_well_formed_operation_nodes_def
              is_well_formed_circuit_def
              node_uses_qubit.simps(3)
              operation_in_circuit_def
            unfolding
              is_valid_circuit_def
              all_wires_linear_def
              wire_is_linear_def
              has_unique_wire_predecessor_def
            by blast

          have incoming_edge_exists:
            "make_edge predecessor operation_node_id ?q
             \<in> edges circuit"
            using predecessor_relation
            unfolding wire_edge_relation_def
            by simp

          have incoming_exists:
            "\<exists>incoming \<in> edges circuit.
               edge_target incoming = operation_node_id
             \<and> edge_wire incoming = ?q"
            proof
            show
              "make_edge predecessor operation_node_id ?q
               \<in> edges circuit"
              using incoming_edge_exists .

            show
              "edge_target
                 (make_edge predecessor operation_node_id ?q)
               = operation_node_id
               \<and>
               edge_wire
                 (make_edge predecessor operation_node_id ?q)
               = ?q"
              unfolding make_edge_def
              by simp
          qed

          (* Therefore incoming_edge returns Some edge, and mapping its
             source produces Some predecessor node. *)
          show ?thesis
            using incoming_exists
            unfolding
              predecessor_on_wire_def
              incoming_edge_def
            by simp
        qed

        have successor_exists:
          "\<exists>successor.
             successor_on_wire
               circuit operation_node_id ?q
             = Some successor"
        proof -

          (* Wire linearity guarantees an outgoing neighbour of the
             operation node on ?q. *)
          obtain successor where
            successor_relation:
              "(operation_node_id, successor)
               \<in> wire_edge_relation circuit ?q"
            using
              valid_circuit
              operation_exists
              edge_wire_used_by_operation
              are_well_formed_operation_nodes_def
              is_well_formed_circuit_def
              node_uses_qubit.simps(3)
              operation_in_circuit_def
            unfolding
              is_valid_circuit_def
              all_wires_linear_def
              wire_is_linear_def
              has_unique_wire_successor_def
            by blast

                  let ?outgoing =
            "make_edge operation_node_id successor ?q"

          have outgoing_in_edges:
            "?outgoing \<in> edges circuit"
            using successor_relation
            unfolding wire_edge_relation_def
            by simp

          have outgoing_source:
            "edge_source ?outgoing = operation_node_id"
            unfolding make_edge_def
            by simp

          have outgoing_wire:
            "edge_wire ?outgoing = ?q"
            unfolding make_edge_def
            by simp

          have outgoing_exists:
            "\<exists>outgoing \<in> edges circuit.
               edge_source outgoing = operation_node_id
             \<and> edge_wire outgoing = ?q"
            using
              outgoing_in_edges
              outgoing_source
              outgoing_wire
            by auto

          (* Hence at least one concrete edge leaves operation_node_id
             on wire ?q. *)
          have outgoing_exists:
            "\<exists>outgoing \<in> edges circuit.
               edge_source outgoing = operation_node_id
             \<and> edge_wire outgoing = ?q"
            using
              outgoing_in_edges
              outgoing_source
              outgoing_wire
            by auto

          (* Therefore outgoing_edge returns Some edge, and mapping its
             target produces Some successor node. *)
          show ?thesis
            using outgoing_exists
            unfolding
              successor_on_wire_def
              outgoing_edge_def
            by simp
        qed

        obtain predecessor where
          predecessor_lookup:
            "predecessor_on_wire
               circuit operation_node_id ?q
             = Some predecessor"
          using predecessor_exists
          by auto

        obtain successor where
          successor_lookup:
            "successor_on_wire
               circuit operation_node_id ?q
             = Some successor"
          using successor_exists
          by blast

        (* The selected predecessor cannot be operation_node_id. Otherwise,
           the original incoming edge would be a self-loop. *)
        have predecessor_not_operation:
          "predecessor \<noteq> operation_node_id"
        proof
          assume predecessor_eq:
            "predecessor = operation_node_id"

          have self_loop_edge:
            "make_edge operation_node_id operation_node_id ?q
             \<in> edges circuit"
            using
              predecessor_on_wire_correct[OF predecessor_lookup]
              predecessor_eq
            by simp

          have self_loop_relation:
            "(operation_node_id, operation_node_id)
             \<in> edge_relation circuit"
            using self_loop_edge
            unfolding edge_relation_def make_edge_def
            by force

          have self_reachable:
            "(operation_node_id, operation_node_id)
             \<in> (edge_relation circuit)\<^sup>+"
            using self_loop_relation
            by (rule r_into_trancl)

          show False
            using original_acyclic self_reachable
            unfolding is_acyclic_circuit_def
            by (simp add: acyclic_def)
        qed

        (* The selected successor cannot be operation_node_id. Otherwise,
           the original outgoing edge would be a self-loop. *)
        have successor_not_operation:
          "successor \<noteq> operation_node_id"
        proof
          assume successor_eq:
            "successor = operation_node_id"

          have self_loop_edge:
            "make_edge operation_node_id operation_node_id ?q
             \<in> edges circuit"
            using
              successor_on_wire_correct[OF successor_lookup]
              successor_eq
            by simp

          have self_loop_relation:
            "(operation_node_id, operation_node_id)
             \<in> edge_relation circuit"
            using self_loop_edge
            unfolding edge_relation_def make_edge_def
            by force

          have self_reachable:
            "(operation_node_id, operation_node_id)
             \<in> (edge_relation circuit)\<^sup>+"
            using self_loop_relation
            by (rule r_into_trancl)

          show False
            using original_acyclic self_reachable 
            unfolding is_acyclic_circuit_def
            by (simp add: acyclic_def)
        qed

        (* The q-step removes both incident edges. The inserted bypass edge
           cannot equal either removed edge because neither bypass endpoint
           is operation_node_id. *)
               
        have q_step_edges:
          "edges ?q_circuit =
             insert
               (make_edge predecessor successor ?q)
               ((edges ?before_circuit
                 - {make_edge predecessor operation_node_id ?q})
                - {make_edge operation_node_id successor ?q})"
          using
            predecessor_lookup
            successor_lookup
          unfolding
            reconnect_wire_def
            insert_edge_def
            delete_edge_def
          by simp

        (* The selected incident edge is absent immediately after the
           reconnection step on its own wire. *)
        have absent_after_q:
          "e \<notin> edges ?q_circuit"
        proof -

          from selected_edge_cases show ?thesis
          proof

            assume incoming_case:
              "\<exists>selected_predecessor.
                 predecessor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_predecessor
               \<and>
                 e =
                   make_edge
                     selected_predecessor
                     operation_node_id
                     ?q"

            then obtain selected_predecessor where
              selected_predecessor_lookup:
                "predecessor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_predecessor"
            and
              e_shape:
                "e =
                   make_edge
                     selected_predecessor
                     operation_node_id
                     ?q"
              by blast

            (* Both lookup equations return Some, so their predecessor
               values must coincide. *)
            have selected_predecessor_eq:
              "selected_predecessor = predecessor"
              using
                selected_predecessor_lookup
                predecessor_lookup
              by simp

            have e_is_removed_incoming:
              "e =
               make_edge predecessor operation_node_id ?q"
              using e_shape selected_predecessor_eq
              by simp

            (* The bypass edge cannot equal the incoming edge because its
               target is successor rather than operation_node_id. *)
            have e_not_bypass:
              "e \<noteq> make_edge predecessor successor ?q"
              using
                e_is_removed_incoming
                successor_not_operation
              apply (auto simp: make_edge_def)
              by (metis edge.ext_inject)

            show ?thesis
              using
                q_step_edges
                e_is_removed_incoming
                e_not_bypass
              by simp

          next

            assume outgoing_case:
              "\<exists>selected_successor.
                 successor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_successor
               \<and>
                 e =
                   make_edge
                     operation_node_id
                     selected_successor
                     ?q"

            then obtain selected_successor where
              selected_successor_lookup:
                "successor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_successor"
            and
              e_shape:
                "e =
                   make_edge
                     operation_node_id
                     selected_successor
                     ?q"
              by blast

            (* Both lookup equations return Some, so their successor
               values must coincide. *)
            have selected_successor_eq:
              "selected_successor = successor"
              using
                selected_successor_lookup
                successor_lookup
              by simp

            have e_is_removed_outgoing:
              "e =
               make_edge operation_node_id successor ?q"
              using e_shape selected_successor_eq
              by simp

            (* The bypass edge cannot equal the outgoing edge because its
               source is predecessor rather than operation_node_id. *)
            have e_not_bypass:
              "e \<noteq> make_edge predecessor successor ?q"
              using
                e_is_removed_outgoing
                predecessor_not_operation
              apply (auto simp: make_edge_def)
              by (metis edge.ext_inject)

            show ?thesis
              using
                q_step_edges
                e_is_removed_outgoing
                e_not_bypass
              by simp
          qed
        qed
        
        have absent_after_later_wires:
          "\<And>current.
             e \<notin> edges current
             \<Longrightarrow>
             e \<notin>
               edges
                 (fold
                   (reconnect_wire circuit operation_node_id)
                   after
                   current)"
          by (metis fold_reconnect_wire_edge_cases make_edges_on_different_wires_unequal q_not_in_after
              selected_edge_cases)


        (* After the q-step, processing the remaining suffix preserves the
           absence of e. Rewriting the original fold using the before/q/after
           decomposition therefore proves that e is absent from the complete
           fold. *)
        have absent_after_suffix:
          "e \<notin>
           edges
             (fold
               (reconnect_wire circuit operation_node_id)
               after
               ?q_circuit)"
          using absent_after_q
          by (rule absent_after_later_wires)

        show ?thesis
          using
            operation_wires_split
            absent_after_suffix
          by simp
      qed

      (* This contradicts the assumption that e remains after the complete
         reconnection fold. *)
      show False
        using remaining_edge selected_edge_removed
        by simp
    next

      assume bypass_edge:
        "\<exists>q \<in> set (op_qargs op).
           \<exists>predecessor successor.
             predecessor_on_wire
               circuit operation_node_id q
               = Some predecessor
           \<and>
             successor_on_wire
               circuit operation_node_id q
               = Some successor
           \<and>
             e = make_edge predecessor successor q"

      then obtain q predecessor successor where
        predecessor_lookup:
          "predecessor_on_wire
             circuit operation_node_id q
           = Some predecessor"
      and
        successor_lookup:
          "successor_on_wire
             circuit operation_node_id q
           = Some successor"
      and
        edge_eq:
          "e = make_edge predecessor successor q"
        by blast

      (* If either bypass endpoint equalled operation_node_id, the
         corresponding original incident edge would be a self-loop,
         contradicting acyclicity. *)
      have predecessor_not_operation:
        "predecessor \<noteq> operation_node_id"
      proof
        assume predecessor_eq:
          "predecessor = operation_node_id"

        have self_loop:
          "make_edge operation_node_id operation_node_id q
           \<in> edges circuit"
          using
            predecessor_on_wire_correct[OF predecessor_lookup]
            predecessor_eq
          by simp

        have self_relation:
          "(operation_node_id, operation_node_id)
           \<in> edge_relation circuit"
          using self_loop
          unfolding edge_relation_def make_edge_def
          by force

        have
          "(operation_node_id, operation_node_id)
           \<in> (edge_relation circuit)\<^sup>+"
          using self_relation
          by (rule r_into_trancl)

        with original_acyclic show False
          unfolding is_acyclic_circuit_def
          by (simp add: acyclic_def)

      qed

      have successor_not_operation:
        "successor \<noteq> operation_node_id"
      proof
        assume successor_eq:
          "successor = operation_node_id"

        have self_loop:
          "make_edge operation_node_id operation_node_id q
           \<in> edges circuit"
          using
            successor_on_wire_correct[OF successor_lookup]
            successor_eq
          by simp

        have self_relation:
          "(operation_node_id, operation_node_id)
           \<in> edge_relation circuit"
          using self_loop
          unfolding edge_relation_def make_edge_def
          by force

        have
          "(operation_node_id, operation_node_id)
           \<in> (edge_relation circuit)\<^sup>+"
          using self_relation
          by (rule r_into_trancl)

        with original_acyclic show False
          unfolding is_acyclic_circuit_def

          by (simp add: acyclic_def)
      qed

      (* A bypass edge connects the predecessor directly to the successor,
         neither of which is the deleted operation node. *)
      have bypass_not_incident:
        "edge_source e \<noteq> operation_node_id
         \<and> edge_target e \<noteq> operation_node_id"
        using
          edge_eq
          predecessor_not_operation
          successor_not_operation
        unfolding make_edge_def
        by simp

      show False
        using incident bypass_not_incident
        by auto
    qed
  qed
qed

lemma delete_operation_preserves_num_qubits:
  (* Deleting an operation only modifies the graph structure. The number
     of qubits in the circuit remains unchanged. *)

  shows
    "num_qubits (delete_operation circuit node_id) = num_qubits circuit"

proof (cases "nodes circuit node_id")
  case None
  then show ?thesis
    unfolding delete_operation_def
    by simp

next
  case (Some node)

  then show ?thesis
  proof (cases node)

    case (InputNode q)

    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OutputNode q)

    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OperationNode op)

    have fold_preserves_num_qubits:
      "num_qubits
         (fold
           (reconnect_wire circuit node_id)
           (op_qargs op)
           circuit)
       =
       num_qubits circuit"

      by (rule fold_reconnect_wire_preserves_num_qubits)

    show ?thesis
      using
        Some
        OperationNode
        fold_preserves_num_qubits
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed
qed

lemma reconnect_wire_preserves_next_id:
  (* Reconnecting a single wire does not allocate or remove node identifiers.
     Therefore, the next unused node identifier remains unchanged. *)
  "next_id
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   next_id current_circuit"

  using
    delete_edge_def
    insert_edge_def
  unfolding reconnect_wire_def
  by (simp split: option.splits)

lemma fold_reconnect_wire_preserves_next_id:
  (* Reconnecting every wire in a list preserves next_id.
     Each individual reconnection leaves next_id unchanged, so the entire
     fold leaves it unchanged as well. *)
  "next_id
     (fold
        (reconnect_wire original_circuit node_id)
        qs
        current_circuit)
   =
   next_id current_circuit"

proof (induction qs arbitrary: current_circuit)
  case Nil
  then show ?case
    by simp

next
  case (Cons q qs)

  have first_reconnection:
    "next_id
       (reconnect_wire
          original_circuit
          node_id
          q
          current_circuit)
     =
     next_id current_circuit"
    by (rule reconnect_wire_preserves_next_id)

  have remaining_reconnections:
    "next_id
       (fold
          (reconnect_wire original_circuit node_id)
          qs
          (reconnect_wire
             original_circuit
             node_id
             q
             current_circuit))
     =
     next_id
       (reconnect_wire
          original_circuit
          node_id
          q
          current_circuit)"
    using Cons
    by simp

  show ?case
    using first_reconnection remaining_reconnections
    by simp
qed

lemma delete_operation_preserves_next_id:
  (* Deleting an operation removes its node and reconnects its incident wires,
     but it does not reuse the deleted node identifier or allocate a new one.
     Therefore, next_id remains unchanged. *)
  "next_id (delete_operation circuit node_id) = next_id circuit"

proof (cases "nodes circuit node_id")
  case None
  then show ?thesis
    unfolding delete_operation_def
    by simp

next
  case (Some node)

  show ?thesis
  proof (cases node)

    case (InputNode q)
    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OutputNode q)
    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OperationNode op)

    have
      "next_id
         (fold
            (reconnect_wire circuit node_id)
            (op_qargs op)
            circuit)
       =
       next_id circuit"
      by (rule fold_reconnect_wire_preserves_next_id)

    then show ?thesis
      using Some OperationNode
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed
qed

lemma delete_operation_preserves_boundary_nodes:
  (* Deleting an operation preserves all canonical input and output nodes.

     reconnect_wire modifies only the edge set. After all affected wires
     have been reconnected, delete_operation changes the node table only
     at operation_node_id, mapping that ID to None.

     Since operation_node_id stores an OperationNode, it cannot be one of
     the canonical input or output node IDs. Therefore, every required
     boundary-node lookup remains unchanged.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_boundary_nodes
       (delete_operation circuit operation_node_id)"

proof -
  have wf:
    "are_well_formed_boundary_nodes circuit"
    using
      valid_circuit
      is_well_formed_circuit_def
    unfolding is_valid_circuit_def
    by simp

  show ?thesis
    using
      wf
      operation_exists
      fold_reconnect_wire_preserves_nodes
      fold_reconnect_wire_preserves_num_qubits
    unfolding
      delete_operation_def
      are_well_formed_boundary_nodes_def
      Let_def
    by auto
qed

lemma delete_operation_preserves_operation_nodes:
  (* Deleting one operation preserves the validity of every remaining
     operation node.

     Wire reconnection changes only edges. The final node-table update
     maps operation_node_id to None and leaves every other node unchanged.

     Hence, any OperationNode found after deletion was already present in
     the original circuit. Since the original circuit is valid, that
     remaining operation is still valid for the circuit. The qubit count
     is unchanged by deletion.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_operation_nodes
       (delete_operation circuit operation_node_id)"

proof -
  have original_operation_nodes:
    "are_well_formed_operation_nodes circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  show ?thesis
    unfolding are_well_formed_operation_nodes_def

  proof (intro allI impI)

    fix remaining_node_id remaining_op

    assume remaining_node:
      "nodes
         (delete_operation circuit operation_node_id)
         remaining_node_id
       =
       Some (OperationNode remaining_op)"

    have remaining_node_id_not_deleted:
      "remaining_node_id \<noteq> operation_node_id"
    proof
      assume
        "remaining_node_id = operation_node_id"

      then have
        "nodes
           (delete_operation circuit operation_node_id)
           remaining_node_id
         =
         None"
        using operation_exists
              delete_operation_removes_operation_node
        by simp

      with remaining_node show False
        by simp
    qed

    have remaining_node_original:
      "nodes circuit remaining_node_id =
         Some (OperationNode remaining_op)"
      using
        remaining_node
        remaining_node_id_not_deleted
        operation_exists
        fold_reconnect_wire_preserves_nodes
      unfolding
        delete_operation_def
        Let_def
      by simp

    have operation_valid_original:
      "operation_in_circuit circuit remaining_op"
      using original_operation_nodes remaining_node_original
      unfolding are_well_formed_operation_nodes_def
      by simp

    show
      "operation_in_circuit
         (delete_operation circuit operation_node_id)
         remaining_op"
      using
        operation_valid_original
        delete_operation_preserves_num_qubits
      unfolding
        operation_in_circuit_def
        qubit_in_circuit_def
      by simp
  qed
qed

lemma delete_operation_edge_preserves_reachability:
  (*
    Every single directed edge remaining after deleting an operation
    represents non-empty reachability in the original circuit.

    An edge in the deleted circuit is either:

      1. an original edge that survived deletion; or
      2. a newly inserted bypass edge from a predecessor to a successor.

    In the bypass case, the original circuit contains the two-edge path

        predecessor \<rightarrow> operation_node_id \<rightarrow> successor.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    edge_after:
      "(source_id, target_id)
       \<in>
       edge_relation
         (delete_operation circuit operation_node_id)"
  shows
    "(source_id, target_id)
     \<in>
     (edge_relation circuit)\<^sup>+"
proof -

  (*
    Membership in edge_relation provides a concrete wire-labelled edge
    whose source and target are source_id and target_id.
  *)
  obtain e where
    edge_in_deleted_circuit:
      "e \<in> edges
         (delete_operation circuit operation_node_id)"
  and
    edge_source:
      "edge_source e = source_id"
  and
    edge_target:
      "edge_target e = target_id"
    using edge_after
    unfolding edge_relation_def
    by blast

  (*
    The final step of delete_operation changes only the node table.
    Therefore, every edge in the deleted circuit is already present after
    folding reconnect_wire over the operation's qubit arguments.
  *)
  have edge_after_reconnection:
    "e \<in>
     edges
       (fold
         (reconnect_wire circuit operation_node_id)
         (op_qargs op)
         circuit)"
    using
      edge_in_deleted_circuit
      operation_exists
    unfolding
      delete_operation_def
      Let_def
    by simp

  (*
    Characterize the origin of e. It is either an edge inherited from the
    original circuit or a bypass edge introduced on one of the deleted
    operation's wires.
  *)
  have edge_cases:
    "e \<in> edges circuit
     \<or>
     (\<exists>q \<in> set (op_qargs op).
        \<exists>predecessor successor.
          predecessor_on_wire
            circuit operation_node_id q
            = Some predecessor
        \<and>
          successor_on_wire
            circuit operation_node_id q
            = Some successor
        \<and>
          e = make_edge predecessor successor q)"
    using edge_after_reconnection
    by (rule fold_reconnect_wire_edge_cases)

  from edge_cases show ?thesis
  proof

    assume original_edge:
      "e \<in> edges circuit"

    (*
      An inherited edge directly gives one step in the original circuit's
      edge relation.
    *)
    have original_relation_edge:
      "(source_id, target_id) \<in> edge_relation circuit"
      using
        original_edge
        edge_source
        edge_target
      unfolding edge_relation_def
      by blast

    (* Every relation edge belongs to its non-empty transitive closure. *)
    show ?thesis
      using original_relation_edge
      by (rule r_into_trancl)

  next

    assume bypass_edge:
      "\<exists>q \<in> set (op_qargs op).
         \<exists>predecessor successor.
           predecessor_on_wire
             circuit operation_node_id q
             = Some predecessor
         \<and>
           successor_on_wire
             circuit operation_node_id q
             = Some successor
         \<and>
           e = make_edge predecessor successor q"

    then obtain q predecessor successor where
      predecessor:
        "predecessor_on_wire
           circuit operation_node_id q
         =
         Some predecessor"
    and
      successor:
        "successor_on_wire
           circuit operation_node_id q
         =
         Some successor"
    and
      bypass_edge_eq:
        "e = make_edge predecessor successor q"
      by blast

    (*
      The source and target of the concrete bypass edge are respectively
      predecessor and successor.
    *)
    have source_id_eq:
      "source_id = predecessor"
      using edge_source bypass_edge_eq
      unfolding make_edge_def
      by simp

    have target_id_eq:
      "target_id = successor"
      using edge_target bypass_edge_eq
      unfolding make_edge_def
      by simp

    (*
      predecessor_on_wire and successor_on_wire identify the two original
      edges incident to operation_node_id.
    *)
    have incoming_edge:
      "make_edge predecessor operation_node_id q
       \<in> edges circuit"
      using predecessor
      by (rule predecessor_on_wire_correct)

    have outgoing_edge:
      "make_edge operation_node_id successor q
       \<in> edges circuit"
      using successor
      by (rule successor_on_wire_correct)

    (* The incoming wire-labelled edge gives the first relation step. *)
    have incoming_relation:
      "(predecessor, operation_node_id)
       \<in> edge_relation circuit"
      using incoming_edge
      unfolding
        make_edge_def
        edge_relation_def
      by force

    (* The outgoing wire-labelled edge gives the second relation step. *)
    have outgoing_relation:
      "(operation_node_id, successor)
       \<in> edge_relation circuit"
      using outgoing_edge
      unfolding
        edge_relation_def
        make_edge_def
      by force

    (*
      Convert the first edge to a non-empty path and append the second
      edge. This reconstructs the original two-edge path represented by
      the bypass edge.
    *)
    have bypass_reachable:
      "(predecessor, successor)
       \<in> (edge_relation circuit)\<^sup>+"
    proof -
      have
        "(predecessor, operation_node_id)
         \<in> (edge_relation circuit)\<^sup>+"
        using incoming_relation
        by (rule r_into_trancl)

      then show ?thesis
        using outgoing_relation
        by (rule trancl_into_trancl)
    qed

    show ?thesis
      using
        bypass_reachable
        source_id_eq
        target_id_eq
      by simp
  qed
qed

lemma delete_operation_remaining_edges_not_incident:
  (*
    After deleting an operation, no remaining edge has the deleted
    operation node as either its source or its target.

    Every edge incident to operation_node_id lies on a qubit used by op,
    because the original edge is well formed and the node stored at
    operation_node_id is OperationNode op.

    delete_operation reconnects every qubit in op_qargs op. On each such
    wire, reconnect_wire removes the unique incoming and outgoing edges
    incident to operation_node_id. Therefore, after the complete fold,
    no incident edge remains.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in> edges
         (delete_operation circuit operation_node_id)"
  shows
    "edge_source e \<noteq> operation_node_id
     \<and> edge_target e \<noteq> operation_node_id"

proof -
  (* The final update performed by delete_operation modifies only nodes,
     so the remaining edge already exists after the reconnection fold. *)
  have edge_after_fold:
    "e \<in>
     edges
       (fold
         (reconnect_wire circuit operation_node_id)
         (op_qargs op)
         circuit)"
    using
      remaining_edge
      operation_exists
    unfolding
      delete_operation_def
      Let_def
    by simp

  (* Apply the structural fold invariant proved independently of edge
     well-formedness preservation. *)
  show ?thesis
    using
      valid_circuit
      operation_exists
      edge_after_fold
    by (rule fold_reconnect_wire_removes_incident_edges)
qed

lemma delete_operation_preserves_well_formed_edges:
  (* Deleting an operation preserves the well-formedness of every edge.

     For each qubit used by the deleted operation, deletion removes the
     incoming and outgoing edges incident to operation_node_id and inserts
     a direct edge from the predecessor to the successor.

     Wire linearity guarantees that these adjacent nodes and edges exist.
     The original edge well-formedness guarantees that the predecessor and
     successor both exist, use the same valid qubit, and therefore form a
     well-formed replacement edge.

     Every unaffected edge remains an original well-formed edge, while no
     remaining edge is incident to the removed operation node.
  *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_edges
       (delete_operation circuit operation_node_id)"


proof -
  have original_edges_well_formed:
    "are_well_formed_edges circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  show ?thesis
    unfolding are_well_formed_edges_def
  proof (intro ballI)

    fix e

    assume edge_after:
      "e \<in> edges
         (delete_operation circuit operation_node_id)"

    have endpoints_not_deleted:
      "edge_source e \<noteq> operation_node_id
       \<and> edge_target e \<noteq> operation_node_id"
      using
        valid_circuit
        operation_exists
        edge_after
      by (rule delete_operation_remaining_edges_not_incident)

    obtain reconnected_circuit where
      reconnected_circuit:
        "reconnected_circuit =
           fold
             (reconnect_wire circuit operation_node_id)
             (op_qargs op)
             circuit"
      by simp

    have edge_in_reconnected:
      "e \<in> edges reconnected_circuit"
      using
        edge_after
        operation_exists
        reconnected_circuit
        delete_operation_def
      unfolding Let_def
      by simp

    have edge_origin:
      "e \<in> edges circuit
       \<or>
       (\<exists> q \<in> set (op_qargs op).
          \<exists>predecessor successor.
            predecessor_on_wire
              circuit operation_node_id q
              = Some predecessor
          \<and>
            successor_on_wire
              circuit operation_node_id q
              = Some successor
          \<and>
            e = make_edge predecessor successor q)"
      using
        edge_in_reconnected
        reconnected_circuit
        fold_reconnect_wire_edge_cases

      by simp

    then consider
        (original) "e \<in> edges circuit"
      | (bypass)
          q predecessor successor where
          "q \<in> set (op_qargs op)"
          "predecessor_on_wire
             circuit operation_node_id q
             = Some predecessor"
          "successor_on_wire
             circuit operation_node_id q
             = Some successor"
          "e = make_edge predecessor successor q"
      by auto

    then show
      "is_well_formed_edge
         (delete_operation circuit operation_node_id)
         e"
    proof cases

      case original

      have original_edge_well_formed:
        "is_well_formed_edge circuit e"
        using
          original_edges_well_formed
          original
        unfolding are_well_formed_edges_def
        by simp

      (*
        The edge existed originally and neither endpoint is the removed
        operation node. The deletion therefore preserves both endpoint
        nodes. It also preserves num_qubits, so the edge wire remains a
        valid circuit qubit.
      *)
      show ?thesis
        using
          original_edge_well_formed
          endpoints_not_deleted
          operation_exists
          delete_operation_preserves_num_qubits[of
            circuit operation_node_id]
          fold_reconnect_wire_preserves_nodes[of
            circuit operation_node_id
            "op_qargs op" circuit]
        unfolding
          is_well_formed_edge_def
          node_exists_def
          qubit_in_circuit_def
          delete_operation_def
          Let_def
        by (simp split: option.splits)
    next

      case (bypass q predecessor successor)

      (*
        This edge is exactly a bypass edge created between the original
        predecessor and successor on q. Its well-formedness after the
        complete deletion follows from the dedicated local helper.
      *)
      case (bypass q predecessor successor)

      (* The predecessor-to-operation edge exists in the original circuit. *)
      have predecessor_edge:
        "make_edge predecessor operation_node_id q
         \<in> edges circuit"
        using bypass(2)
        by (rule predecessor_on_wire_correct)

      (* The operation-to-successor edge also exists in the original circuit. *)
      have successor_edge:
        "make_edge operation_node_id successor q
         \<in> edges circuit"
        using bypass(3)
        by (rule successor_on_wire_correct)

      (* Since the original circuit is valid, both incident edges are
         well formed. Their outer endpoints therefore exist, lie on q,
         and q is a valid circuit qubit. *)
      have predecessor_edge_well_formed:
        "is_well_formed_edge
           circuit
           (make_edge predecessor operation_node_id q)"
        using original_edges_well_formed predecessor_edge
        unfolding are_well_formed_edges_def
        by blast

      have successor_edge_well_formed:
        "is_well_formed_edge
           circuit
           (make_edge operation_node_id successor q)"
        using original_edges_well_formed successor_edge
        unfolding are_well_formed_edges_def
        by blast

      (* The bypass edge remains after deletion, so neither of its endpoints
         can be the removed operation node. *)
      have bypass_edge_after:
        "make_edge predecessor successor q
         \<in> edges
             (delete_operation circuit operation_node_id)"
        using edge_after bypass(4)
        by simp

      have bypass_endpoints_not_deleted:
        "predecessor \<noteq> operation_node_id
         \<and> successor \<noteq> operation_node_id"
        using
          delete_operation_remaining_edges_not_incident[
            OF valid_circuit operation_exists bypass_edge_after]
        unfolding make_edge_def
        by simp

      (* Reconnection preserves the node table, and the final deletion changes
         only operation_node_id. Since predecessor and successor are different
         from that node, their node entries are unchanged. The qubit count is
         also preserved. *)
      show ?thesis
        using
          predecessor_edge_well_formed
          successor_edge_well_formed
          bypass_endpoints_not_deleted
          operation_exists
          bypass(4)
          delete_operation_preserves_num_qubits[
            of circuit operation_node_id]
          fold_reconnect_wire_preserves_nodes[
            of circuit operation_node_id
               "op_qargs op" circuit predecessor]
          fold_reconnect_wire_preserves_nodes[
            of circuit operation_node_id
               "op_qargs op" circuit successor]
        unfolding
          is_well_formed_edge_def
          node_exists_def
          qubit_in_circuit_def
          delete_operation_def
          make_edge_def
          Let_def
        by auto
    qed
  qed
qed

lemma delete_operation_preserves_well_formed_circuit:
  (* Deleting an operation preserves the local structural validity of the
     circuit.

     Deletion performs three conceptual steps:

       1. Remove the operation node.
       2. Remove all incident wire edges.
       3. Reconnect each predecessor directly to its corresponding successor.

     Since the deleted operation belongs to a valid quantum circuit,
     every newly created edge reconnects nodes that already lie on the
     same valid qubit wire. Boundary nodes are unchanged, and every
     remaining operation node is unchanged. Consequently, deleting an
     operation preserves the well-formedness of the circuit.
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
    "is_well_formed_circuit
       (delete_operation circuit operation_node_id)"

proof -

  have boundary_nodes:
    "are_well_formed_boundary_nodes
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
      delete_operation_preserves_boundary_nodes
    by simp

  have operation_nodes:
    "are_well_formed_operation_nodes
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
      delete_operation_preserves_operation_nodes
    by simp

  have edges:
    "are_well_formed_edges
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
      delete_operation_preserves_well_formed_edges
    by simp

  show ?thesis
    unfolding is_well_formed_circuit_def
    using
      boundary_nodes
      operation_nodes
      edges
    by simp
qed

end
