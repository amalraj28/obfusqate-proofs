theory Quantum_Circuit_Deletion
  imports Quantum_Circuit_State

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
        (predecessor_on_wire original_circuit node_id q, successor_on_wire original_circuit node_id q)
      of
        (Some predecessor, Some successor) \<Rightarrow>
          insert_edge
            (make_edge predecessor successor q) 
            (delete_edge
              (make_edge node_id successor q) (delete_edge (make_edge predecessor node_id q) current_circuit))
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
  "delete_operation circuit node_id = (case nodes circuit node_id of Some (OperationNode op) \<Rightarrow> (let reconnected_circuit = fold (reconnect_wire circuit node_id) (op_qargs op) circuit in reconnected_circuit \<lparr>nodes := (nodes reconnected_circuit) (node_id := None)\<rparr>) | _ \<Rightarrow> circuit)"
lemma reconnect_wire_preserves_nodes[simp]:
  (* Reconnecting one wire changes only the edge set. It does not change
     the node table. *)
  "nodes (reconnect_wire original_circuit operation_node_id q circuit) node_id = nodes circuit node_id"

  unfolding reconnect_wire_def
  apply (auto split: option.splits)
  by (simp add: delete_edge_def insert_edge_def)
lemma fold_reconnect_wire_preserves_nodes[simp]:
  (* Reconnecting any list of wires preserves the complete node table. *)
  "nodes (fold (reconnect_wire original_circuit operation_node_id) qs circuit) node_id = nodes circuit node_id"

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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "nodes (delete_operation circuit operation_node_id) = (nodes circuit)(operation_node_id := None)"

proof -
  have reconnected_nodes:
    "nodes (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit) = nodes circuit"
    by auto

  show ?thesis
    unfolding delete_operation_def
    using
      operation_exists
      reconnected_nodes
    by simp
qed

lemma delete_operation_other_node[simp]:
  (* Deleting one operation does not change any other node-table entry. *)
  assumes
    operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    different_node:
      "other_node_id \<noteq> operation_node_id"
  shows
    "nodes (delete_operation circuit operation_node_id) other_node_id = nodes circuit other_node_id"

  using
    delete_operation_nodes[OF operation_exists]
    different_node
  by simp

lemma reconnect_wire_edges_characterisation:
  (* Reconnecting a wire removes the two edges incident on the deleted
     operation node and inserts the corresponding bypass edge. *)
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  shows
    "edges (reconnect_wire original_circuit operation_node_id q current_circuit)
     = insert (make_edge predecessor_id successor_id q)
         (edges current_circuit - { make_edge predecessor_id operation_node_id q, make_edge operation_node_id successor_id q })"

  unfolding
    reconnect_wire_def
    insert_edge_def
    delete_edge_def
    make_edge_def
  using
    predecessor
    successor
  by auto

lemma reconnect_wire_successor_predecessor_characterisation:
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  shows
    "wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q
     = insert (predecessor_id, successor_id) (wire_edge_relation current_circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"

proof -
  have
    "edges (reconnect_wire original_circuit operation_node_id q current_circuit)
     = insert (make_edge predecessor_id successor_id q) (edges current_circuit - { make_edge predecessor_id operation_node_id q, make_edge operation_node_id successor_id q })"
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
      "\<nexists>predecessor_id. (predecessor_id, get_input_node_id q) \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor circuit q (get_input_node_id q)"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
  shows
    "(\<nexists>predecessor_id.
       (predecessor_id, get_input_node_id q) \<in> wire_edge_relation (reconnect_wire circuit operation_node_id q circuit) q)
      \<and> has_unique_wire_successor (reconnect_wire circuit operation_node_id q circuit) q (get_input_node_id q)"

proof -
  have incoming_operation_edge:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id) \<in> wire_edge_relation circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have operation_not_input:
    "operation_node_id \<noteq> get_input_node_id q"
  proof
    assume
      "operation_node_id = get_input_node_id q"

    then have
      "(predecessor_id, get_input_node_id q) \<in> wire_edge_relation circuit q"
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
      "(operation_node_id, get_input_node_id q) \<in> wire_edge_relation circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_input_predecessor
      by blast
  qed

  have relation_after:
    "wire_edge_relation (reconnect_wire circuit operation_node_id q circuit) q
       = insert (predecessor_id, successor_id) (wire_edge_relation circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
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
      "\<nexists>predecessor_id. (predecessor_id, get_input_node_id q) \<in> wire_edge_relation current_circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor current_circuit q (get_input_node_id q)"
  and
    same_relation:
      "wire_edge_relation current_circuit q = wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  shows
    "(\<nexists>predecessor_id. (predecessor_id, get_input_node_id q)
       \<in> wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q)
         \<and> has_unique_wire_successor (reconnect_wire original_circuit operation_node_id q current_circuit) q (get_input_node_id q)"
  using
    has_unique_wire_successor_def
    no_input_predecessor
    predecessor
    reconnect_wire_preserves_input_boundary
    reconnect_wire_successor_predecessor_characterisation
    same_relation
    successor
    unique_input_successor
  by auto


lemma reconnect_wire_preserves_other_wire_relation:
  (* Reconnecting the deleted node on wire q changes only q-labelled
     edges. Therefore, the immediate-edge relation of every different
     wire r remains unchanged. *)
  assumes
    different_wire:
      "r \<noteq> q"
  shows
    "wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) r
     = wire_edge_relation current_circuit r"

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
    "wire_edge_relation (fold (reconnect_wire original_circuit operation_node_id) qs current_circuit) r
      = wire_edge_relation current_circuit r"
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
      "\<nexists>pred. (pred, get_input_node_id q) \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor circuit q (get_input_node_id q)"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "(\<nexists>pred.
     (pred, get_input_node_id q) \<in> wire_edge_relation (fold (reconnect_wire circuit operation_node_id) qs circuit) q)
    \<and> has_unique_wire_successor (fold (reconnect_wire circuit operation_node_id) qs circuit) q (get_input_node_id q)"

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

  let ?before_circuit = "fold (reconnect_wire circuit operation_node_id) before circuit"

  let ?q_circuit = "reconnect_wire circuit operation_node_id q ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q = wire_edge_relation circuit q"
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
    "\<nexists>pred. (pred, get_input_node_id q) \<in> wire_edge_relation ?before_circuit q"
    using
      no_input_predecessor
      before_same_relation
    by simp

  have unique_input_successor_before:
    "has_unique_wire_successor ?before_circuit q (get_input_node_id q)"
    using
      unique_input_successor
      before_same_relation
    unfolding has_unique_wire_successor_def
    by auto

  have boundary_after_q:
    "(\<nexists>pred.
       (pred, get_input_node_id q) \<in> wire_edge_relation ?q_circuit q)
       \<and> has_unique_wire_successor ?q_circuit q (get_input_node_id q)"
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
    "wire_edge_relation (fold (reconnect_wire circuit operation_node_id) after ?q_circuit) q = wire_edge_relation ?q_circuit q"
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
  (* If node_id stores an OperationNode, then deleting that operation removes it from the circuit. *)
  assumes operation_node:
    "nodes circuit node_id = Some (OperationNode op)"

  shows
    "nodes (delete_operation circuit node_id) node_id = None"
  
  using
    delete_operation_nodes
    operation_node
  by simp

lemma reconnect_wire_preserves_num_qubits:
  (* Reconnecting a single wire only updates the circuit's edge set. It does not change the number of qubits in the circuit. *)
  "num_qubits (reconnect_wire original_circuit node_id q current_circuit) = num_qubits current_circuit"
  
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
      "e \<in> edges (reconnect_wire original_circuit operation_node_id q current_circuit)"
  shows
    "e \<in> edges current_circuit
   \<or> (\<exists>predecessor successor. predecessor_on_wire original_circuit operation_node_id q = Some predecessor
       \<and> successor_on_wire original_circuit operation_node_id q = Some successor
       \<and> e = make_edge predecessor successor q)"
  
  using edge_after
  unfolding reconnect_wire_def
  by (auto split: option.splits prod.splits)


lemma fold_reconnect_wire_edge_cases:
  (*
    Every edge present after reconnecting a list of wires is either an
    original edge or a bypass edge introduced while processing one wire
    from that list.
  *)
  assumes
    edge_after:
      "e \<in> edges (fold (reconnect_wire original_circuit operation_node_id) qs current_circuit)"
  shows
    "e \<in> edges current_circuit
    \<or> (\<exists>q \<in> set qs. \<exists>predecessor successor. predecessor_on_wire original_circuit operation_node_id q = Some predecessor
       \<and> successor_on_wire original_circuit operation_node_id q = Some successor
       \<and> e = make_edge predecessor successor q)"
  
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
  let ?updated_circuit = "reconnect_wire original_circuit operation_node_id q current_circuit"

  have edge_after_remaining_wires:
    "e \<in> edges (fold (reconnect_wire original_circuit operation_node_id) qs ?updated_circuit)"
    using Cons.prems
    by simp

  (*
    Apply the induction hypothesis to the remaining fold. The edge is
    either already present immediately after reconnecting q, or it is a
    bypass edge introduced while processing one of the later wires in qs.
  *)
  have remaining_wire_cases:
    "e \<in> edges ?updated_circuit
   \<or> (\<exists>q' \<in> set qs. \<exists>predecessor successor. predecessor_on_wire original_circuit operation_node_id q' = Some predecessor
       \<and> successor_on_wire original_circuit operation_node_id q' = Some successor
       \<and> e = make_edge predecessor successor q')"
    using Cons.IH[of ?updated_circuit]
          edge_after_remaining_wires
    by blast

    from remaining_wire_cases show ?case
      by (meson list.set_intros(1,2) reconnect_wire_edge_cases)
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
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_node_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_node_id"
  shows
    "is_well_formed_edge (reconnect_wire circuit operation_node_id q circuit) (make_edge predecessor_node_id successor_node_id q)"

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
    "make_edge predecessor_node_id operation_node_id q \<in> edges circuit"
    using predecessor
    by (rule predecessor_on_wire_correct)

  (*
    successor_on_wire identifies an existing edge leaving
    operation_node_id toward successor_node_id on q.
  *)
  have successor_edge:
    "make_edge operation_node_id successor_node_id q \<in> edges circuit"
    using successor
    by (rule successor_on_wire_correct)

  (* Both incident edges are well formed in the original valid circuit. *)
  have predecessor_edge_well_formed:
    "is_well_formed_edge circuit (make_edge predecessor_node_id operation_node_id q)"
    using original_edges_well_formed predecessor_edge
    unfolding are_well_formed_edges_def
    by blast

  have successor_edge_well_formed:
    "is_well_formed_edge circuit (make_edge operation_node_id successor_node_id q)"
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
     \<and> (case nodes circuit predecessor_node_id
       of None \<Rightarrow> False
       | Some predecessor_node \<Rightarrow> node_uses_qubit predecessor_node q)"
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
   \<and> (case nodes circuit successor_node_id
     of None \<Rightarrow> False
     | Some successor_node \<Rightarrow> node_uses_qubit successor_node q)"
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
    "nodes (reconnect_wire circuit operation_node_id q circuit) predecessor_node_id = nodes circuit predecessor_node_id"
    by (rule reconnect_wire_preserves_nodes)

  have successor_node_preserved:
    "nodes (reconnect_wire circuit operation_node_id q circuit) successor_node_id = nodes circuit successor_node_id"
    by (rule reconnect_wire_preserves_nodes)

  have num_qubits_preserved:
    "num_qubits (reconnect_wire circuit operation_node_id q circuit) = num_qubits circuit"
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
  "num_qubits (fold (reconnect_wire original_circuit node_id) qs current_circuit) = num_qubits current_circuit"

proof (induction qs arbitrary: current_circuit)
  case Nil

  then show ?case
    by simp

next
  case (Cons q qs)

  have first_reconnection:
    "num_qubits (reconnect_wire original_circuit node_id q current_circuit) = num_qubits current_circuit"
    by (rule reconnect_wire_preserves_num_qubits)

  have remaining_reconnections:
    "num_qubits (fold (reconnect_wire original_circuit node_id) qs (reconnect_wire original_circuit node_id q current_circuit))
     = num_qubits (reconnect_wire original_circuit node_id q current_circuit)"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
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
      "edge_source e = operation_node_id \<or> edge_target e = operation_node_id"
  shows
    "(\<exists>predecessor. predecessor_on_wire circuit operation_node_id q = Some predecessor \<and> e = make_edge predecessor operation_node_id q)
     \<or> (\<exists>successor. successor_on_wire circuit operation_node_id q = Some successor \<and> e = make_edge operation_node_id successor q)"

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
    "has_unique_wire_predecessor circuit q operation_node_id"
    using
      linear_q
      operation_exists
      operation_uses_wire
    unfolding wire_is_linear_def
    by simp

  have unique_successor:
    "has_unique_wire_successor circuit q operation_node_id"
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
      "(operation_node_id, edge_target e) \<in> wire_edge_relation circuit q"
      using
        incident_edge
        source_is_operation
        edge_on_wire
      unfolding wire_edge_relation_def
      by (cases e) (simp add: make_edge_def)

    (* Obtain the unique successor promised by wire linearity. *)
    obtain unique_successor_id where
      successor_relation:
        "(operation_node_id, unique_successor_id) \<in> wire_edge_relation circuit q"
    and
      successor_unique:
        "\<And>candidate.
         (operation_node_id, candidate) \<in> wire_edge_relation circuit q \<Longrightarrow> candidate = unique_successor_id"
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
      "\<exists>outgoing. outgoing_edge circuit operation_node_id q = Some outgoing"
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
        "outgoing_edge circuit operation_node_id q = Some outgoing"
      by blast

    have outgoing_properties:
      "outgoing \<in> edges circuit
       \<and> edge_source outgoing = operation_node_id
       \<and> edge_wire outgoing = q"
      using outgoing
      by (rule outgoing_edge_correct)

    have selected_successor_relation:
      "(operation_node_id, edge_target outgoing) \<in> wire_edge_relation circuit q"
      using outgoing_properties
      unfolding wire_edge_relation_def
      by (cases outgoing) (simp add: make_edge_def)

    have selected_target:
      "edge_target outgoing = unique_successor_id"
      using successor_unique selected_successor_relation
      by blast

    have successor_lookup:
      "successor_on_wire circuit operation_node_id q = Some unique_successor_id"
      using outgoing selected_target
      unfolding successor_on_wire_def
      by simp

    (* The record fields determine e completely. *)
    have edge_shape:
      "e = make_edge operation_node_id unique_successor_id q"
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
      "(edge_source e, operation_node_id) \<in> wire_edge_relation circuit q"
      using
        incident_edge
        target_is_operation
        edge_on_wire
      unfolding wire_edge_relation_def
      by (cases e) (simp add: make_edge_def)

    (* Obtain the unique predecessor promised by wire linearity. *)
    obtain unique_predecessor_id where
      predecessor_relation:
        "(unique_predecessor_id, operation_node_id) \<in> wire_edge_relation circuit q"
    and
      predecessor_unique:
        "\<And>candidate. (candidate, operation_node_id) \<in> wire_edge_relation circuit q \<Longrightarrow> candidate = unique_predecessor_id"
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
      "\<exists>incoming. incoming_edge circuit operation_node_id q = Some incoming"
      using
        edge_on_wire
        incident_edge
        incoming_edge_def
        target_is_operation
      by auto

    then obtain incoming where
      incoming:
        "incoming_edge circuit operation_node_id q = Some incoming"
      by blast

    have incoming_properties:
      "incoming \<in> edges circuit
     \<and> edge_target incoming = operation_node_id
     \<and> edge_wire incoming = q"
      using incoming
      by (rule incoming_edge_correct)

    have selected_predecessor_relation:
      "(edge_source incoming, operation_node_id) \<in> wire_edge_relation circuit q"
      using incoming_properties
      unfolding wire_edge_relation_def
      by (cases incoming) (simp add: make_edge_def)

    have selected_source:
      "edge_source incoming = unique_predecessor_id"
      using predecessor_unique selected_predecessor_relation
      by blast

    have predecessor_lookup:
      "predecessor_on_wire circuit operation_node_id q = Some unique_predecessor_id"
      using incoming selected_source
      unfolding predecessor_on_wire_def
      by simp

    (* The record fields determine e completely. *)
    have edge_shape:
      "e = make_edge unique_predecessor_id operation_node_id q"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in> edges (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit)"
  shows
    "edge_source e \<noteq> operation_node_id \<and> edge_target e \<noteq> operation_node_id"

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
      "\<not> (edge_source e \<noteq> operation_node_id \<and> edge_target e \<noteq> operation_node_id)"

    then have incident:
      "edge_source e = operation_node_id
     \<or> edge_target e = operation_node_id"
      by simp

    (* Every edge produced by the fold is either inherited from the
       original circuit or is a newly inserted bypass edge. *)
    have edge_origin:
      "e \<in> edges circuit
     \<or> (\<exists>q \<in> set (op_qargs op). \<exists>predecessor successor. predecessor_on_wire circuit operation_node_id q = Some predecessor
           \<and> successor_on_wire circuit operation_node_id q = Some successor
           \<and> e = make_edge predecessor successor q)"
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
             predecessor_on_wire circuit operation_node_id ?q = Some predecessor
             \<and> e = make_edge predecessor operation_node_id ?q)
       \<or> (\<exists>successor.
             successor_on_wire circuit operation_node_id ?q = Some successor
           \<and> e = make_edge operation_node_id successor ?q)"
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
        "e \<notin> edges (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit)"
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
          "fold (reconnect_wire circuit operation_node_id) before circuit"

        let ?q_circuit =
          "reconnect_wire circuit operation_node_id ?q ?before_circuit"

        (* Both adjacent lookups exist. Whichever side of the operation e
           occupies, wire linearity supplies the other side as well. *)
                have predecessor_exists:
          "\<exists>predecessor. predecessor_on_wire circuit operation_node_id ?q = Some predecessor"
        proof -
          (* Wire linearity guarantees that the operation has an incoming
             neighbour on ?q. *)
          obtain predecessor where
            predecessor_relation:
              "(predecessor, operation_node_id) \<in> wire_edge_relation circuit ?q"
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
            "make_edge predecessor operation_node_id ?q \<in> edges circuit"
            using predecessor_relation
            unfolding wire_edge_relation_def
            by simp

          have incoming_exists:
            "\<exists>incoming \<in> edges circuit.
                 edge_target incoming = operation_node_id
               \<and> edge_wire incoming = ?q"
            proof
            show
              "make_edge predecessor operation_node_id ?q \<in> edges circuit"
              using incoming_edge_exists .

            show
              "edge_target (make_edge predecessor operation_node_id ?q) = operation_node_id
             \<and> edge_wire (make_edge predecessor operation_node_id ?q) = ?q"
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
          "\<exists>successor. successor_on_wire circuit operation_node_id ?q = Some successor"
        proof -
          (* Wire linearity guarantees an outgoing neighbour of the
             operation node on ?q. *)
          obtain successor where
            successor_relation:
              "(operation_node_id, successor) \<in> wire_edge_relation circuit ?q"
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

          let ?outgoing = "make_edge operation_node_id successor ?q"

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
            "predecessor_on_wire circuit operation_node_id ?q = Some predecessor"
          using predecessor_exists
          by auto

        obtain successor where
          successor_lookup:
            "successor_on_wire circuit operation_node_id ?q = Some successor"
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
            "make_edge operation_node_id operation_node_id ?q \<in> edges circuit"
            using
              predecessor_on_wire_correct[OF predecessor_lookup]
              predecessor_eq
            by simp

          have self_loop_relation:
            "(operation_node_id, operation_node_id) \<in> edge_relation circuit"
            using self_loop_edge
            unfolding edge_relation_def make_edge_def
            by force

          have self_reachable:
            "(operation_node_id, operation_node_id) \<in> (edge_relation circuit)\<^sup>+"
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
            "make_edge operation_node_id operation_node_id ?q \<in> edges circuit"
            using
              successor_on_wire_correct[OF successor_lookup]
              successor_eq
            by simp

          have self_loop_relation:
            "(operation_node_id, operation_node_id) \<in> edge_relation circuit"
            using self_loop_edge
            unfolding edge_relation_def make_edge_def
            by force

          have self_reachable:
            "(operation_node_id, operation_node_id) \<in> (edge_relation circuit)\<^sup>+"
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
          "edges ?q_circuit = insert (make_edge predecessor successor ?q) ((edges ?before_circuit - {make_edge predecessor operation_node_id ?q}) - {make_edge operation_node_id successor ?q})"
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
              "\<exists>selected_predecessor. predecessor_on_wire circuit operation_node_id ?q = Some selected_predecessor
                 \<and> e = make_edge selected_predecessor operation_node_id ?q"

            then obtain selected_predecessor where
              selected_predecessor_lookup:
                "predecessor_on_wire circuit operation_node_id ?q = Some selected_predecessor"
            and
              e_shape:
                "e = make_edge selected_predecessor operation_node_id ?q"
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
              "e = make_edge predecessor operation_node_id ?q"
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
              "\<exists>selected_successor. successor_on_wire circuit operation_node_id ?q = Some selected_successor
                 \<and> e = make_edge operation_node_id selected_successor ?q"

            then obtain selected_successor where
              selected_successor_lookup:
                "successor_on_wire circuit operation_node_id ?q = Some selected_successor"
            and
              e_shape:
                "e = make_edge operation_node_id selected_successor ?q"
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
              "e = make_edge operation_node_id successor ?q"
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
          "\<And>current. e \<notin> edges current \<Longrightarrow> e \<notin> edges (fold (reconnect_wire circuit operation_node_id) after current)"
          by (metis
              fold_reconnect_wire_edge_cases
              make_edges_on_different_wires_unequal
              q_not_in_after
              selected_edge_cases)

        (* After the q-step, processing the remaining suffix preserves the
           absence of e. Rewriting the original fold using the before/q/after
           decomposition therefore proves that e is absent from the complete
           fold. *)
        have absent_after_suffix:
          "e \<notin> edges (fold (reconnect_wire circuit operation_node_id) after ?q_circuit)"
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
        "\<exists>q \<in> set (op_qargs op). \<exists>predecessor successor.
         predecessor_on_wire circuit operation_node_id q = Some predecessor
       \<and> successor_on_wire circuit operation_node_id q = Some successor
       \<and> e = make_edge predecessor successor q"

      then obtain q predecessor successor where
        predecessor_lookup:
          "predecessor_on_wire circuit operation_node_id q = Some predecessor"
      and
        successor_lookup:
          "successor_on_wire circuit operation_node_id q = Some successor"
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
          "make_edge operation_node_id operation_node_id q \<in> edges circuit"
          using
            predecessor_on_wire_correct[OF predecessor_lookup]
            predecessor_eq
          by simp

        have self_relation:
          "(operation_node_id, operation_node_id) \<in> edge_relation circuit"
          using self_loop
          unfolding edge_relation_def make_edge_def
          by force

        have
          "(operation_node_id, operation_node_id) \<in> (edge_relation circuit)\<^sup>+"
          using self_relation
          by (rule r_into_trancl)

        with original_acyclic show False
          unfolding is_acyclic_circuit_def
          by (simp add: acyclic_def)

      qed

      have successor_not_operation:
        "successor \<noteq> operation_node_id"
        using
          original_acyclic
          successor_lookup
          successor_on_wire_not_self
        by auto

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
      "num_qubits (fold (reconnect_wire circuit node_id) (op_qargs op) circuit) = num_qubits circuit"

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
  "next_id (reconnect_wire original_circuit node_id q current_circuit) = next_id current_circuit"

  using
    delete_edge_def
    insert_edge_def
  unfolding reconnect_wire_def
  by (simp split: option.splits)

lemma fold_reconnect_wire_preserves_next_id:
  (* Reconnecting every wire in a list preserves next_id.
     Each individual reconnection leaves next_id unchanged, so the entire
     fold leaves it unchanged as well. *)
  "next_id (fold (reconnect_wire original_circuit node_id) qs current_circuit) = next_id current_circuit"

proof (induction qs arbitrary: current_circuit)
  case Nil
  then show ?case
    by simp

next
  case (Cons q qs)

  have first_reconnection:
    "next_id (reconnect_wire original_circuit node_id q current_circuit) = next_id current_circuit"
    by (rule reconnect_wire_preserves_next_id)

  have remaining_reconnections:
    "next_id (fold (reconnect_wire original_circuit node_id) qs (reconnect_wire original_circuit node_id q current_circuit))
     = next_id (reconnect_wire original_circuit node_id q current_circuit)"
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
      "next_id (fold (reconnect_wire circuit node_id) (op_qargs op) circuit) = next_id circuit"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "are_well_formed_boundary_nodes (delete_operation circuit operation_node_id)"
  using
    are_well_formed_boundary_nodes_def
    delete_operation_nodes
    delete_operation_preserves_num_qubits
    is_valid_circuit_def
    is_well_formed_circuit_def
    operation_exists
    valid_circuit
  by auto

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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "are_well_formed_operation_nodes (delete_operation circuit operation_node_id)"

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
      "nodes (delete_operation circuit operation_node_id) remaining_node_id = Some (OperationNode remaining_op)"

    have remaining_node_id_not_deleted:
      "remaining_node_id \<noteq> operation_node_id"
      using
        operation_exists
        remaining_node
      by auto

    have remaining_node_original:
      "nodes circuit remaining_node_id = Some (OperationNode remaining_op)"
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
      "operation_in_circuit (delete_operation circuit operation_node_id) remaining_op"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    edge_after:
      "(source_id, target_id) \<in> edge_relation (delete_operation circuit operation_node_id)"
  shows
    "(source_id, target_id) \<in> (edge_relation circuit)\<^sup>+"

proof -
  (*
    Membership in edge_relation provides a concrete wire-labelled edge
    whose source and target are source_id and target_id.
  *)
  obtain e where
    edge_in_deleted_circuit:
      "e \<in> edges (delete_operation circuit operation_node_id)"
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
    "e \<in> edges (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit)"
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
     \<or> (\<exists>q \<in> set (op_qargs op). \<exists>predecessor successor.
           predecessor_on_wire circuit operation_node_id q = Some predecessor
         \<and> successor_on_wire circuit operation_node_id q = Some successor
         \<and> e = make_edge predecessor successor q)"
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
      "\<exists>q \<in> set (op_qargs op). \<exists>predecessor successor.
         predecessor_on_wire circuit operation_node_id q = Some predecessor
       \<and> successor_on_wire circuit operation_node_id q = Some successor
       \<and> e = make_edge predecessor successor q"

    then obtain q predecessor successor where
      predecessor:
        "predecessor_on_wire circuit operation_node_id q = Some predecessor"
    and
      successor:
        "successor_on_wire circuit operation_node_id q = Some successor"
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
      "make_edge predecessor operation_node_id q \<in> edges circuit"
      using predecessor
      by (rule predecessor_on_wire_correct)

    have outgoing_edge:
      "make_edge operation_node_id successor q \<in> edges circuit"
      using successor
      by (rule successor_on_wire_correct)

    (* The incoming wire-labelled edge gives the first relation step. *)
    have incoming_relation:
      "(predecessor, operation_node_id) \<in> edge_relation circuit"
      using incoming_edge
      unfolding
        make_edge_def
        edge_relation_def
      by force

    (* The outgoing wire-labelled edge gives the second relation step. *)
    have outgoing_relation:
      "(operation_node_id, successor) \<in> edge_relation circuit"
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
      "(predecessor, successor) \<in> (edge_relation circuit)\<^sup>+"
      using
        incoming_relation
        outgoing_relation
      by auto

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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in> edges (delete_operation circuit operation_node_id)"
  shows
    "edge_source e \<noteq> operation_node_id
   \<and> edge_target e \<noteq> operation_node_id"

proof -
  (* The final update performed by delete_operation modifies only nodes,
     so the remaining edge already exists after the reconnection fold. *)
  have edge_after_fold:
    "e \<in> edges (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit)"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "are_well_formed_edges (delete_operation circuit operation_node_id)"

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
      "e \<in> edges (delete_operation circuit operation_node_id)"

    have endpoints_not_deleted:
      "edge_source e \<noteq> operation_node_id \<and> edge_target e \<noteq> operation_node_id"
      using
        valid_circuit
        operation_exists
        edge_after
      by (rule delete_operation_remaining_edges_not_incident)

    obtain reconnected_circuit where
      reconnected_circuit:
        "reconnected_circuit = fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit"
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
    \<or> (\<exists> q \<in> set (op_qargs op). \<exists>predecessor successor.
         predecessor_on_wire circuit operation_node_id q = Some predecessor
       \<and> successor_on_wire circuit operation_node_id q = Some successor
       \<and> e = make_edge predecessor successor q)"
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
          "predecessor_on_wire circuit operation_node_id q = Some predecessor"
          "successor_on_wire circuit operation_node_id q = Some successor"
          "e = make_edge predecessor successor q"
      by auto

    then show
      "is_well_formed_edge (delete_operation circuit operation_node_id) e"
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
        "make_edge predecessor operation_node_id q \<in> edges circuit"
        using bypass(2)
        by (rule predecessor_on_wire_correct)

      (* The operation-to-successor edge also exists in the original circuit. *)
      have successor_edge:
        "make_edge operation_node_id successor q \<in> edges circuit"
        using bypass(3)
        by (rule successor_on_wire_correct)

      (* Since the original circuit is valid, both incident edges are
         well formed. Their outer endpoints therefore exist, lie on q,
         and q is a valid circuit qubit. *)
      have predecessor_edge_well_formed:
        "is_well_formed_edge circuit (make_edge predecessor operation_node_id q)"
        using original_edges_well_formed predecessor_edge
        unfolding are_well_formed_edges_def
        by blast

      have successor_edge_well_formed:
        "is_well_formed_edge circuit (make_edge operation_node_id successor q)"
        using original_edges_well_formed successor_edge
        unfolding are_well_formed_edges_def
        by blast

      (* The bypass edge remains after deletion, so neither of its endpoints
         can be the removed operation node. *)
      have bypass_edge_after:
        "make_edge predecessor successor q \<in> edges (delete_operation circuit operation_node_id)"
        using edge_after bypass(4)
        by simp

      have bypass_endpoints_not_deleted:
        "predecessor \<noteq> operation_node_id \<and> successor \<noteq> operation_node_id"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "is_well_formed_circuit (delete_operation circuit operation_node_id)"
  using
    delete_operation_preserves_boundary_nodes
    delete_operation_preserves_operation_nodes
    delete_operation_preserves_well_formed_edges
    is_well_formed_circuit_def
    operation_exists
    valid_circuit
  by simp

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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "(edge_relation (delete_operation circuit operation_node_id))\<^sup>+ \<subseteq> (edge_relation circuit)\<^sup>+"

proof
  fix node_pair

  assume reachable_after_deletion:
    "node_pair \<in> (edge_relation (delete_operation circuit operation_node_id))\<^sup>+"

  (*
    Expose the source and target components of the pair so that the
    transitive-closure induction can reason about the path endpoints.
  *)
  obtain source_id target_id where
    node_pair:
      "node_pair = (source_id, target_id)"
    by (cases node_pair)

  have source_reaches_target_after_deletion:
    "(source_id, target_id) \<in> (edge_relation (delete_operation circuit operation_node_id))\<^sup>+"
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
    "(source_id, target_id) \<in> (edge_relation circuit)\<^sup>+"
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
      "(source_id, intermediate_id) \<in> (edge_relation circuit)\<^sup>+"
      using step.IH
      by simp

    (*
      Map the final edge of the deleted-circuit path to a non-empty path
      from intermediate_id to final_id in the original circuit.
    *)
    have final_segment_reachable_original:
      "(intermediate_id, final_id) \<in> (edge_relation circuit)\<^sup>+"
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
      "has_unique_wire_predecessor current_circuit q successor_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q = wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  shows
    "has_unique_wire_predecessor (reconnect_wire original_circuit operation_node_id q current_circuit) q successor_id"

proof -
  have old_incoming_original:
    "(operation_node_id, successor_id) \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have old_incoming_current:
    "(operation_node_id, successor_id) \<in> wire_edge_relation current_circuit q"
    using old_incoming_original same_relation
    by simp

  have every_old_predecessor_is_operation:
    "\<And>source_id. (source_id, successor_id) \<in> wire_edge_relation current_circuit q \<Longrightarrow> source_id = operation_node_id"
    using unique_predecessor old_incoming_current
    unfolding has_unique_wire_predecessor_def
    by blast

  have relation_after:
    "wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q
     = insert (predecessor_id, successor_id) (wire_edge_relation current_circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  have bypass_exists:
    "(predecessor_id, successor_id) \<in> wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q"
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
      "has_unique_wire_successor current_circuit q predecessor_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q = wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  shows
    "has_unique_wire_successor (reconnect_wire original_circuit operation_node_id q current_circuit) q predecessor_id"

proof -
  have old_outgoing_original:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have old_outgoing_current:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation current_circuit q"
    using old_outgoing_original same_relation
    by simp

  have every_old_successor_is_operation:
    "\<And>target_id. (predecessor_id, target_id) \<in> wire_edge_relation current_circuit q \<Longrightarrow> target_id = operation_node_id"
    using unique_successor old_outgoing_current
    unfolding has_unique_wire_successor_def
    by blast

  have relation_after:
    "wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q
      = insert (predecessor_id, successor_id) (wire_edge_relation current_circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  have bypass_exists:
    "(predecessor_id, successor_id) \<in> wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q"
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
      "has_unique_wire_predecessor current_circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_successor:
      "node_id \<noteq> successor_id"
  shows
    "has_unique_wire_predecessor (reconnect_wire original_circuit operation_node_id q current_circuit) q node_id"

proof -
  let ?updated_circuit =
    "reconnect_wire original_circuit operation_node_id q current_circuit"

  have relation_after:
    "wire_edge_relation ?updated_circuit q
     = insert (predecessor_id, successor_id) (wire_edge_relation current_circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  have incoming_relation_iff:
    "\<And>source_id. 
      (source_id, node_id) \<in> wire_edge_relation ?updated_circuit q
     \<longleftrightarrow> (source_id, node_id) \<in> wire_edge_relation current_circuit q"
    using not_deleted not_successor relation_after by auto

  show ?thesis
    using has_unique_wire_predecessor_def incoming_relation_iff unique_predecessor
    by simp
qed

lemma reconnect_wire_other_node_has_unique_successor:
  (* A node that is neither the deleted operation nor its predecessor keeps
     exactly the same outgoing q-edges after reconnection. Therefore, its
     unique-successor property is preserved. *)
  assumes
    unique_successor:
      "has_unique_wire_successor current_circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_predecessor:
      "node_id \<noteq> predecessor_id"
  shows
    "has_unique_wire_successor (reconnect_wire original_circuit operation_node_id q current_circuit) q node_id"

proof -
  let ?updated_circuit = "reconnect_wire original_circuit operation_node_id q current_circuit"

  have relation_after:
    "wire_edge_relation ?updated_circuit q
       = insert (predecessor_id, successor_id) (wire_edge_relation current_circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  have outgoing_relation_iff:
    "\<And>target_id.
       (node_id, target_id) \<in> wire_edge_relation ?updated_circuit q
   \<longleftrightarrow> (node_id, target_id) \<in> wire_edge_relation current_circuit q"
    using
      not_deleted
      not_predecessor
      relation_after
    by auto

  have old_exists:
    "\<exists>target_id. (node_id, target_id) \<in> wire_edge_relation current_circuit q"
    using unique_successor
    unfolding has_unique_wire_successor_def
    by blast

  have old_unique:
    "\<And>target_id target_id'.
       (node_id, target_id) \<in> wire_edge_relation current_circuit q \<Longrightarrow>
         (node_id, target_id') \<in> wire_edge_relation current_circuit q \<Longrightarrow>
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
      "wire_edge_relation current_circuit q = wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
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
    "has_unique_wire_predecessor (reconnect_wire original_circuit operation_node_id q current_circuit) q node_id
     \<and> has_unique_wire_successor (reconnect_wire original_circuit operation_node_id q current_circuit) q node_id"
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
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
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
    "has_unique_wire_predecessor (fold (reconnect_wire circuit operation_node_id) qs circuit) q node_id
   \<and> has_unique_wire_successor (fold (reconnect_wire circuit operation_node_id) qs circuit) q node_id"

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

  let ?before_circuit = "fold (reconnect_wire circuit operation_node_id) before circuit"

  let ?q_circuit = "reconnect_wire circuit operation_node_id q ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q = wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_before
    by simp

  have predecessor_before:
    "has_unique_wire_predecessor ?before_circuit q node_id"
    using unique_predecessor before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have successor_before:
    "has_unique_wire_successor ?before_circuit q node_id"
    using unique_successor before_same_relation
    unfolding has_unique_wire_successor_def
    by simp

  have degrees_after_q:
    "has_unique_wire_predecessor ?q_circuit q node_id
   \<and> has_unique_wire_successor ?q_circuit q node_id"
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
    "wire_edge_relation (fold (reconnect_wire circuit operation_node_id) after ?q_circuit) q
   = wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_after
    by simp
    
  have predecessor_after:
    "has_unique_wire_predecessor (fold (reconnect_wire circuit operation_node_id) after ?q_circuit) q node_id"
    using
      degrees_after_q
      after_same_relation
      has_unique_wire_predecessor_def
    by simp

  have successor_after:
    "has_unique_wire_successor (fold (reconnect_wire circuit operation_node_id) after ?q_circuit) q node_id"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "is_acyclic_circuit (delete_operation circuit operation_node_id)"
  by (meson
      acyclic_def
      delete_operation_reachability_preserved
      is_acyclic_circuit_def
      is_valid_circuit_def
      operation_exists
      subset_iff valid_circuit)

lemma delete_operation_preserves_unused_wire_relation:
  (* If the deleted operation does not use q, delete_operation never invokes
     reconnect_wire on q.

     The final node-table update removes the operation node but does not
     modify the edge set. Therefore, the q-labelled edge relation is
     exactly the same before and after deletion.
  *)
  assumes
    operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_edge_relation (delete_operation circuit operation_node_id) q = wire_edge_relation circuit q"

proof -
  have folded_relation:
    "wire_edge_relation (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit) q
   = wire_edge_relation circuit q"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_is_linear circuit q \<Longrightarrow> wire_is_linear (delete_operation circuit operation_node_id) q"

proof -
  assume original_linear:
    "wire_is_linear circuit q"

  let ?deleted = "delete_operation circuit operation_node_id"

  have same_wire_relation:
    "wire_edge_relation ?deleted q = wire_edge_relation circuit q"
    using operation_exists unused_wire
    by (rule delete_operation_preserves_unused_wire_relation)

  have deleted_node_does_not_use_q:
    "\<not> node_uses_qubit (OperationNode op) q"
    using unused_wire
    by simp

  have remaining_node_origin:
    "\<And>node_id node_value. nodes ?deleted node_id = Some node_value
         \<Longrightarrow> nodes circuit node_id = Some node_value"
    by (metis delete_operation_nodes fun_upd_apply operation_exists option.distinct(1))

  have original_q_node_survives:
    "\<And>node_id node_value. nodes circuit node_id = Some node_value
     \<Longrightarrow> node_uses_qubit node_value q
     \<Longrightarrow> nodes ?deleted node_id = Some node_value"
    using delete_operation_nodes deleted_node_does_not_use_q operation_exists by force

  have comparable_after:
    "nodes_comparable_on_wire ?deleted q"
    using
      delete_operation_nodes
      nodes_comparable_on_wire_def
      operation_exists
      original_linear
      same_wire_relation
      wire_is_linear_def
      wire_reaches_def
    by auto

  have operation_nodes_after:
    "\<forall>node_id remaining_op.
       nodes ?deleted node_id = Some (OperationNode remaining_op)
   \<longrightarrow> node_uses_qubit (OperationNode remaining_op) q
   \<longrightarrow> has_unique_wire_predecessor ?deleted q node_id
       \<and> has_unique_wire_successor ?deleted q node_id"
    by (metis
        has_unique_wire_predecessor_def
        has_unique_wire_successor_def
        original_linear
        remaining_node_origin
        same_wire_relation
        wire_is_linear_def)

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
      "wire_edge_relation current_circuit q = wire_edge_relation original_circuit q"
  and
    unique_operation_predecessor:
      "has_unique_wire_predecessor current_circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor current_circuit q operation_node_id"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
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
    "wire_reaches (reconnect_wire original_circuit operation_node_id q current_circuit) q node_a node_b"

proof -
  let ?old_relation = "wire_edge_relation current_circuit q"

  let ?new_relation = "wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q"

  have predecessor_edge_original:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have predecessor_edge_current:
    "(predecessor_id, operation_node_id) \<in> ?old_relation"
    using predecessor_edge_original same_relation
    by simp

  have successor_edge_original:
    "(operation_node_id, successor_id) \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have successor_edge_current:
    "(operation_node_id, successor_id) \<in> ?old_relation"
    using successor_edge_original same_relation
    by simp

  have every_operation_predecessor:
    "\<And>source_id. (source_id, operation_node_id) \<in> ?old_relation \<Longrightarrow> source_id = predecessor_id"
    using
      unique_operation_predecessor
      predecessor_edge_current
    unfolding has_unique_wire_predecessor_def
    by blast

  have every_operation_successor:
    "\<And>target_id. (operation_node_id, target_id) \<in> ?old_relation \<Longrightarrow> target_id = successor_id"
    using
      unique_operation_successor
      successor_edge_current
    unfolding has_unique_wire_successor_def
    by blast

  have relation_after:
    "?new_relation = insert (predecessor_id, successor_id) (?old_relation - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have bypass_edge:
    "(predecessor_id, successor_id) \<in> ?new_relation"
    using relation_after
    by simp

  have surviving_edge_preserved:
    "\<And>source_id target_id. (source_id, target_id) \<in> ?old_relation \<Longrightarrow> source_id \<noteq> operation_node_id \<Longrightarrow> target_id \<noteq> operation_node_id \<Longrightarrow> (source_id, target_id) \<in> ?new_relation"
    using relation_after
    by auto

  have old_path:
    "(node_a, node_b) \<in> ?old_relation\<^sup>+"
    using old_reachability
    unfolding wire_reaches_def
    by simp

  have strengthened_path:
    "\<And>target_id.
       (node_a, target_id) \<in> ?old_relation\<^sup>+ \<Longrightarrow> 
          (target_id = operation_node_id \<longrightarrow>
                 node_a = predecessor_id \<or> (node_a, predecessor_id) \<in> ?new_relation\<^sup>+)
         \<and> (target_id \<noteq> operation_node_id \<longrightarrow> (node_a, target_id) \<in> ?new_relation\<^sup>+)"
  proof -
    fix target_id

    assume old_target_path:
      "(node_a, target_id) \<in> ?old_relation\<^sup>+"

    show
      "(target_id = operation_node_id \<longrightarrow> 
            node_a = predecessor_id \<or> (node_a, predecessor_id) \<in> ?new_relation\<^sup>+)
     \<and> (target_id \<noteq> operation_node_id \<longrightarrow> (node_a, target_id) \<in> ?new_relation\<^sup>+)"

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
    by simp
qed

lemma fold_reconnect_preserves_surviving_reachability:
  (* In a distinct list of affected wires containing q, reconnections on
     wires other than q leave q's relation unchanged. The single
     reconnection on q contracts the deleted operation while preserving
     reachability between surviving endpoints.
  *)
  assumes
    unique_operation_predecessor:
      "has_unique_wire_predecessor circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor circuit q operation_node_id"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
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
    "wire_reaches (fold (reconnect_wire circuit operation_node_id) qs circuit) q node_a node_b"

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

  let ?before_circuit = "fold (reconnect_wire circuit operation_node_id) before circuit"

  let ?q_circuit = "reconnect_wire circuit operation_node_id q ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q = wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_before
    by simp

  have predecessor_before:
    "has_unique_wire_predecessor ?before_circuit q operation_node_id"
    using
      unique_operation_predecessor
      before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have successor_before:
    "has_unique_wire_successor ?before_circuit q operation_node_id"
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
    "wire_edge_relation (fold (reconnect_wire circuit operation_node_id) after ?q_circuit) q = wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_after
    by simp

  have reachability_after:
    "wire_reaches (fold (reconnect_wire circuit operation_node_id) after ?q_circuit) q node_a node_b"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
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
    "wire_reaches (delete_operation circuit operation_node_id) q node_a node_b"

proof -
  have unique_operation_predecessor:
    "has_unique_wire_predecessor circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  have unique_operation_successor:
    "has_unique_wire_successor circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_relation_id where
    predecessor_relation:
      "(predecessor_relation_id, operation_node_id) \<in> wire_edge_relation circuit q"
    using unique_operation_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_relation_id where
    successor_relation:
      "(operation_node_id, successor_relation_id) \<in> wire_edge_relation circuit q"
    using unique_operation_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire circuit operation_node_id q \<noteq> None"
    using predecessor_relation
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  obtain predecessor_id where
    predecessor:
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
    using predecessor_not_none
    by (cases
        "predecessor_on_wire circuit operation_node_id q")
       auto

  have successor_not_none:
    "successor_on_wire circuit operation_node_id q \<noteq> None"
    using successor_relation
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  obtain successor_id where
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
    using successor_not_none
    by (cases
        "successor_on_wire circuit operation_node_id q")
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

  let ?reconnected_circuit = "fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit"

  have reachability_after_fold:
    "wire_reaches ?reconnected_circuit q node_a node_b"
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
    "wire_edge_relation (delete_operation circuit operation_node_id) q
   = wire_edge_relation ?reconnected_circuit q"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "nodes_comparable_on_wire (delete_operation circuit operation_node_id) q"

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
      "nodes (delete_operation circuit operation_node_id) node_a = Some node_a_value"

    assume node_b_exists_after:
      "nodes (delete_operation circuit operation_node_id) node_b = Some node_b_value"

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
     \<or> wire_reaches (delete_operation circuit operation_node_id) q node_a node_b
     \<or> wire_reaches (delete_operation circuit operation_node_id) q node_b node_a"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "(\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q) \<in> wire_edge_relation (delete_operation circuit operation_node_id) q)
         \<and> has_unique_wire_successor (delete_operation circuit operation_node_id) q (get_input_node_id q)"

proof -
  have no_input_predecessor:
    "\<nexists>predecessor_id. (predecessor_id, get_input_node_id q) \<in> wire_edge_relation circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have unique_input_successor:
    "has_unique_wire_successor circuit q (get_input_node_id q)"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have operation_has_predecessor:
    "has_unique_wire_predecessor circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have operation_has_successor:
    "has_unique_wire_successor circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_id where predecessor_edge:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation circuit q"
    using operation_has_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_id where successor_edge:
    "(operation_node_id, successor_id) \<in> wire_edge_relation circuit q"
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
    "predecessor_on_wire circuit operation_node_id q = Some selected_predecessor"
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
    "successor_on_wire circuit operation_node_id q = Some selected_successor"
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
    "fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit"

  have boundary_after_reconnection:
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q) \<in> wire_edge_relation ?reconnected_circuit q)
       \<and> has_unique_wire_successor ?reconnected_circuit q (get_input_node_id q)"
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
    "wire_edge_relation (delete_operation circuit operation_node_id) q = wire_edge_relation ?reconnected_circuit q"
    
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
      "has_unique_wire_predecessor circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation circuit q"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
  shows
    "has_unique_wire_predecessor (reconnect_wire circuit operation_node_id q circuit) q (get_output_node_id q) \<and> (\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation (reconnect_wire circuit operation_node_id q circuit) q)"

proof -
  have incoming_operation_edge:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id) \<in> wire_edge_relation circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have operation_not_output:
    "operation_node_id \<noteq> get_output_node_id q"
  proof
    assume
      "operation_node_id = get_output_node_id q"

    then have
      "(get_output_node_id q, successor_id) \<in> wire_edge_relation circuit q"
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
      "(get_output_node_id q, operation_node_id) \<in> wire_edge_relation circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have relation_after:
    "wire_edge_relation (reconnect_wire circuit operation_node_id q circuit) q = insert (predecessor_id, successor_id) (wire_edge_relation circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
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
      "has_unique_wire_predecessor current_circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation current_circuit q"
  and
    same_relation:
      "wire_edge_relation current_circuit q = wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q = Some successor_id"
  shows
    "has_unique_wire_predecessor
         (reconnect_wire original_circuit operation_node_id q current_circuit) q (get_output_node_id q)
       \<and> (\<nexists>successor_id.
         (get_output_node_id q, successor_id) \<in> wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q)"

proof -
  have incoming_operation_edge_original:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have incoming_operation_edge:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation current_circuit q"
    using incoming_operation_edge_original same_relation
    by simp

  have outgoing_operation_edge_original:
    "(operation_node_id, successor_id) \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id) \<in> wire_edge_relation current_circuit q"
    using outgoing_operation_edge_original same_relation
    by simp

  have operation_not_output:
    "operation_node_id \<noteq> get_output_node_id q"
  proof
    assume
      operation_is_output:
        "operation_node_id = get_output_node_id q"

    then have
      "(get_output_node_id q, successor_id) \<in> wire_edge_relation current_circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have predecessor_not_output:
    "predecessor_id \<noteq> get_output_node_id q"
    using
      incoming_operation_edge
      no_output_successor
    by auto

  have relation_after:
    "wire_edge_relation (reconnect_wire original_circuit operation_node_id q current_circuit) q
     = insert (predecessor_id, successor_id) (wire_edge_relation current_circuit q - {(predecessor_id, operation_node_id), (operation_node_id, successor_id)})"
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
      "has_unique_wire_predecessor circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation circuit q"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "has_unique_wire_predecessor (fold (reconnect_wire circuit operation_node_id) qs circuit) q (get_output_node_id q)
   \<and> (\<nexists>successor_id.
         (get_output_node_id q, successor_id) \<in> wire_edge_relation (fold (reconnect_wire circuit operation_node_id) qs circuit) q)"

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

  let ?before_circuit = "fold (reconnect_wire circuit operation_node_id) before circuit"

  let ?q_circuit = "reconnect_wire circuit operation_node_id q ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q = wire_edge_relation circuit q"
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
    "has_unique_wire_predecessor ?before_circuit q (get_output_node_id q)"
    using
      unique_output_predecessor
      before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have no_output_successor_before:
    "\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation ?before_circuit q"
    using
      no_output_successor
      before_same_relation
    by simp

  have boundary_after_q:
    "has_unique_wire_predecessor ?q_circuit q (get_output_node_id q)
   \<and> (\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation ?q_circuit q)"
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
    "wire_edge_relation (fold (reconnect_wire circuit operation_node_id) after ?q_circuit) q = wire_edge_relation ?q_circuit q"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "has_unique_wire_predecessor (delete_operation circuit operation_node_id) q (get_output_node_id q)
   \<and> (\<nexists>successor_id.
     (get_output_node_id q, successor_id) \<in> wire_edge_relation (delete_operation circuit operation_node_id) q)"

proof -
  have unique_output_predecessor:
    "has_unique_wire_predecessor circuit q (get_output_node_id q)"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have no_output_successor:
    "\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have operation_has_predecessor:
    "has_unique_wire_predecessor circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have operation_has_successor:
    "has_unique_wire_successor circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have predecessor_exists:
    "\<exists>predecessor_id. predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
  
  proof -
    obtain predecessor_id where
      predecessor_relation:
        "(predecessor_id, operation_node_id) \<in> wire_edge_relation circuit q"
      using operation_has_predecessor
      unfolding has_unique_wire_predecessor_def
      by blast

    have incoming_edge_exists:
      "make_edge predecessor_id operation_node_id q \<in> edges circuit"
      using predecessor_relation
      unfolding wire_edge_relation_def
      by simp

    have incoming_exists:
      "\<exists>incoming \<in> edges circuit.
         edge_target incoming = operation_node_id
       \<and> edge_wire incoming = q"
    proof
      show
        "make_edge predecessor_id operation_node_id q \<in> edges circuit"
        using incoming_edge_exists
        by simp

      show
        "edge_target (make_edge predecessor_id operation_node_id q) = operation_node_id
       \<and> edge_wire (make_edge predecessor_id operation_node_id q) = q"
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
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_id"
    using predecessor_exists
    by blast

  have successor_exists:
    "\<exists>successor_id. successor_on_wire circuit operation_node_id q = Some successor_id"
  proof -
    obtain successor_id where
      successor_relation:
        "(operation_node_id, successor_id) \<in> wire_edge_relation circuit q"
      using operation_has_successor
      unfolding has_unique_wire_successor_def
      by blast

    have outgoing_edge_exists:
      "make_edge operation_node_id successor_id q \<in> edges circuit"
      using successor_relation
      unfolding wire_edge_relation_def
      by simp

    have outgoing_exists:
      "\<exists>outgoing \<in> edges circuit.
         edge_source outgoing = operation_node_id \<and> edge_wire outgoing = q"
      using
        make_edge_def
        outgoing_edge_exists
      by force

    show ?thesis
      using outgoing_exists
      unfolding
        successor_on_wire_def
        outgoing_edge_def
      by simp
  qed

  obtain successor_id where
    successor:
      "successor_on_wire circuit operation_node_id q = Some successor_id"
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
    "has_unique_wire_predecessor (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit) q (get_output_node_id q)
   \<and> (\<nexists>successor_id. (get_output_node_id q, successor_id)
       \<in> wire_edge_relation (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit) q)"
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
    "wire_edge_relation (delete_operation circuit operation_node_id) q
     = wire_edge_relation (fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit) q"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "\<forall>node_id remaining_op. nodes (delete_operation circuit operation_node_id) node_id = Some (OperationNode remaining_op)
     \<longrightarrow> node_uses_qubit (OperationNode remaining_op) q
     \<longrightarrow> has_unique_wire_predecessor (delete_operation circuit operation_node_id) q node_id
         \<and> has_unique_wire_successor (delete_operation circuit operation_node_id) q node_id"

proof (intro allI impI)
  fix node_id remaining_op

  assume remaining_operation_exists:
    "nodes (delete_operation circuit operation_node_id) node_id = Some (OperationNode remaining_op)"

  assume remaining_operation_uses_q:
    "node_uses_qubit (OperationNode remaining_op) q"

  have remaining_node:
    "node_id \<noteq> operation_node_id"
    using
      operation_exists
      remaining_operation_exists
    by auto

  have remaining_operation_exists_originally:
    "nodes circuit node_id = Some (OperationNode remaining_op)"
    using
      operation_exists
      remaining_node
      remaining_operation_exists
    by simp

  have remaining_unique_predecessor:
    "has_unique_wire_predecessor circuit q node_id"
    using
      original_linear
      remaining_operation_exists_originally
      remaining_operation_uses_q
    unfolding wire_is_linear_def
    by blast

  have remaining_unique_successor:
    "has_unique_wire_successor circuit q node_id"
    using
      original_linear
      remaining_operation_exists_originally
      remaining_operation_uses_q
    unfolding wire_is_linear_def
    by blast

  have deleted_operation_has_predecessor:
    "has_unique_wire_predecessor circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  have deleted_operation_has_successor:
    "has_unique_wire_successor circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_id where predecessor_relation:
    "(predecessor_id, operation_node_id) \<in> wire_edge_relation circuit q"
    using deleted_operation_has_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_id where successor_relation:
    "(operation_node_id, successor_id) \<in> wire_edge_relation circuit q"
    using deleted_operation_has_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire circuit operation_node_id q \<noteq> None"
    using predecessor_relation
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_predecessor where predecessor:
    "predecessor_on_wire circuit operation_node_id q = Some selected_predecessor"
    by (cases "predecessor_on_wire circuit operation_node_id q") auto

  have successor_not_none:
    "successor_on_wire circuit operation_node_id q \<noteq> None"
    using successor_relation
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_successor where successor:
    "successor_on_wire circuit operation_node_id q = Some selected_successor"
    by (cases "successor_on_wire circuit operation_node_id q") auto

  have original_acyclic:
    "is_acyclic_circuit circuit"
    using valid_circuit
    unfolding is_valid_circuit_def
    by simp

  have predecessor_not_deleted:
    "selected_predecessor \<noteq> operation_node_id"
    using
      original_acyclic
      predecessor
      predecessor_on_wire_not_self
    by auto

  have successor_not_deleted:
    "selected_successor \<noteq> operation_node_id"
    using
      original_acyclic
      successor
      successor_on_wire_not_self
    by auto

  have predecessor_not_successor:
    "selected_predecessor \<noteq> selected_successor"
  proof
    assume endpoints_equal:
      "selected_predecessor = selected_successor"

    have incoming_edge:
      "make_edge selected_predecessor operation_node_id q \<in> edges circuit"
      using predecessor_on_wire_correct[OF predecessor]
      by simp

    have outgoing_edge:
      "make_edge operation_node_id selected_successor q \<in> edges circuit"
      using successor_on_wire_correct[OF successor]
      by simp

    have incoming_relation:
      "(selected_predecessor, operation_node_id) \<in> edge_relation circuit"
      using incoming_edge
      unfolding edge_relation_def make_edge_def
      by force

    have outgoing_relation:
      "(operation_node_id, selected_successor) \<in> edge_relation circuit"
      using outgoing_edge
      unfolding edge_relation_def make_edge_def
      by force

    have incoming_path:
      "(selected_predecessor, operation_node_id) \<in> (edge_relation circuit)\<^sup>+"
      using incoming_relation
      by (rule r_into_trancl)

    have outgoing_path:
      "(operation_node_id, selected_successor) \<in> (edge_relation circuit)\<^sup>+"
      using outgoing_relation
      by (rule r_into_trancl)

    have endpoint_cycle:
      "(selected_predecessor, selected_successor) \<in> (edge_relation circuit)\<^sup>+"
      using incoming_path outgoing_path
      by (rule trancl_trans)

    then have self_reachable:
      "(selected_predecessor, selected_predecessor) \<in> (edge_relation circuit)\<^sup>+"
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
    "fold (reconnect_wire circuit operation_node_id) (op_qargs op) circuit"

  have degrees_after_reconnection:
    "has_unique_wire_predecessor ?reconnected_circuit q node_id
   \<and> has_unique_wire_successor ?reconnected_circuit q node_id"
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
    "wire_edge_relation (delete_operation circuit operation_node_id) q
     = wire_edge_relation ?reconnected_circuit q"
    using operation_exists
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp

  show
    "has_unique_wire_predecessor (delete_operation circuit operation_node_id) q node_id
   \<and> has_unique_wire_successor (delete_operation circuit operation_node_id) q node_id"
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  shows
    "wire_is_linear circuit q \<Longrightarrow> wire_is_linear (delete_operation circuit operation_node_id) q"
  
  using delete_operation_used_wire_preserves_comparability
      delete_operation_used_wire_preserves_input_boundary
      delete_operation_used_wire_preserves_operation_degrees
      delete_operation_used_wire_preserves_output_boundary
      operation_exists used_wire
      valid_circuit
      wire_is_linear_def
  by simp

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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  and
    valid_wire_after:
      "qubit_in_circuit (delete_operation circuit operation_node_id) q"
  shows
    "wire_is_linear (delete_operation circuit operation_node_id) q"
  
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
      "nodes circuit operation_node_id = Some (OperationNode op)"
  shows
    "all_wires_linear (delete_operation circuit operation_node_id)"

  unfolding all_wires_linear_def
  using
    delete_operation_preserves_wire_is_linear
    operation_exists
    valid_circuit
  by simp
end
