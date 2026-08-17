theory Quantum_Circuit_Construction
  imports Quantum_Circuit_Graph

begin

definition increment_node_id :: "node_id \<Rightarrow> node_id" where
  (* Given a node ID, return the next node ID (Add 1 to it) *)
  "increment_node_id current_node_id = NodeId (node_id_to_nat current_node_id + 1)"

lemma node_id_to_nat_increment_node_id[simp]:
  (* The next node id is 1 more than the present node id *)
  "node_id_to_nat (increment_node_id current_node_id) = node_id_to_nat current_node_id + 1"
  unfolding increment_node_id_def
  by (cases current_node_id; simp)

lemma increment_node_id_not_same[simp]:
  (* Node id before and after increment are not same *)
  "increment_node_id current_node_id \<noteq> current_node_id"
  unfolding increment_node_id_def
  by (cases current_node_id; simp)

type_synonym frontier = "qubit \<Rightarrow> node_id" (* Frontier is a mapping from qubit \<Rightarrow> node_id, where node_id means the last operation encountered on this qubit *)

definition initial_frontier :: frontier where
  (* Initially, frontier (map) would be from qubit to its input node (since circuit is empty) *)
  "initial_frontier q = get_input_node_id q"

definition update_frontier :: "frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> frontier" where
  (* Updating frontier for a qubit q means that we are updating the existing entry of the qubit q in the map with the id of the new node *)
  "update_frontier frontier q new_node_id = frontier(q := new_node_id)"

lemma update_frontier_same[simp]:
  (* If you look up qubit q after updating the frontier entry for q, you will get the newly supplied node ID *)
  "update_frontier frontier q new_node_id q = new_node_id"
  unfolding update_frontier_def
  by simp

lemma update_frontier_other[simp]:
  (* Updating the frontier for q does not change the frontier entry
     of any different qubit other_q. *)
  assumes "other_q \<noteq> q"
  shows
    "update_frontier frontier q new_node_id other_q =
     frontier other_q"
  using assms
  unfolding update_frontier_def
  by simp

definition is_valid_frontier :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  (* A frontier is valid when, for every valid qubit:
       1. the frontier points to an existing node on that wire, and
       2. that node is connected directly to the output node on that wire.
       3. the frontier node must have a unique successor, which is the output node
  *)
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
  (* The circuit's next_id is unused when no node is currently stored at that ID. This prevents the next insertion from overwriting an existing node *)
  "next_id_is_unused circuit \<longleftrightarrow> nodes circuit (next_id circuit) = None"

definition all_existing_node_ids_below_next_id ::
  "quantum_circuit \<Rightarrow> bool"
  where
    (* Every node currently stored in the circuit has a numerical node ID
     strictly smaller than the circuit's next_id.

     This expresses sequential node-ID allocation:
       - IDs below next_id may already be allocated;
       - next_id and every greater ID are not yet allocated.

     This property is stronger than saying that next_id is unused.
  *)
    "all_existing_node_ids_below_next_id circuit \<longleftrightarrow>
     (\<forall>existing_node_id.
        nodes circuit existing_node_id \<noteq> None
        \<longrightarrow>
        node_id_to_nat existing_node_id
          < node_id_to_nat (next_id circuit))"

definition is_valid_construction_state :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  (* A circuit and frontier form a valid construction state when:
       1. the circuit is structurally well formed;
       2. the frontier correctly describes the current end of every wire;
       3. next_id is unused and can safely identify the next operation node.
       4. every allocated node ID lies strictly below next_id.
  *)
  "is_valid_construction_state circuit frontier \<longleftrightarrow>
      is_well_formed_circuit circuit
        \<and> is_valid_frontier circuit frontier
        \<and> next_id_is_unused circuit
        \<and> all_existing_node_ids_below_next_id circuit"

definition insert_node :: "node_id \<Rightarrow> circuit_node \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  (* Add or replace the node stored at the given node ID. *)
  "insert_node node_id new_node circuit =
     circuit\<lparr>nodes := (nodes circuit)(node_id := Some new_node)\<rparr>" (* create a new function exactly like "nodes circuit", except at "NodeId 2", return "Some new_node" *)

definition insert_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  (* Add an edge to the circuit. *)
  "insert_edge e circuit =
     circuit\<lparr>edges := insert e (edges circuit)\<rparr>" (* Circuit where everything else is same, except that edges is now the union of old edge set with the new edge inserted *)

definition delete_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  (* Remove an edge from the circuit. *)
  "delete_edge e circuit =
     circuit\<lparr>edges := edges circuit - {e}\<rparr>" (* Circuit where everything else is same, except that edges is the difference of old edges and set (new edge) *)

lemma nodes_insert_node_same[simp]: (* helper lemma *)
  (* After insertion, if you lookup at the inserted node id, you would get the new inserted node *)
  "nodes (insert_node node_id node circuit) node_id = Some node"
  unfolding insert_node_def
  by simp

lemma valid_frontier_has_unique_successor:
  (* A valid frontier is the final node immediately before the output
     node, so it has exactly one successor on its wire. *)
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

assumes valid_q:
  "qubit_in_circuit circuit q"

shows
  "has_unique_wire_successor circuit q (frontier q)"
  using valid_frontier valid_q
  unfolding is_valid_frontier_def
  by blast

lemma nodes_insert_node_other[simp]: (* helper lemma *)
  (* All other node ids apart from the one where insertion happen, remain unchanged *)
  assumes "other_node_id \<noteq> node_id"
  shows "nodes (insert_node node_id node circuit) other_node_id =
         nodes circuit other_node_id"
  using assms
  unfolding insert_node_def
  by simp

lemma insert_node_at_unused_id_preserves_valid_frontier:
  (* Storing a new node at an unused node ID preserves frontier validity.

     Since the ID was unused, it cannot be the ID of any existing frontier node. Therefore, every existing frontier lookup remains unchanged. insert_node also leaves the edge set and qubit count unchanged.
  *)
  assumes valid_frontier: "is_valid_frontier circuit frontier"
    (* Assume the circuit already has a correct frontier. This is the property we want to preserve. *)

assumes node_id_unused: "nodes circuit new_node_id = None"
  (* Assume this node ID is currently unused. We are inserting into an empty location, not replacing an existing node. *)

shows
  "is_valid_frontier 
         (insert_node new_node_id new_node circuit)
         frontier"
  (* Shows that after inserting the new node, the exact same frontier is still valid. *)

proof -
  show ?thesis
    unfolding is_valid_frontier_def
  proof (intro allI impI) (* Pick any valid qubit q. Prove the property for it *)
    fix q (* Arbitrary q *)

    assume valid_q_after: (* Assume this qubit belongs to the new circuit. *)
      "qubit_in_circuit
         (insert_node new_node_id new_node circuit)
         q"

    have valid_q_before:
      "qubit_in_circuit circuit q" (* q is a valid qubit prior to insertion *)
      using valid_q_after (* Use this assumption *)
      unfolding qubit_in_circuit_def insert_node_def (* First "use", then "unfold". So that whatever you are "using" also gets "unfolded" in the subsequent steps *)
      by simp

(* Because the old frontier is valid, and q is valid in the old circuit, there must be some node currently stored at "frontier q" (say frontier_node) 

      That node must:
        1. exist in the node mapping ("old_frontier_node" below)
        2. use wire q ("old_frontier_node_uses_q" below)
        3. have an edge to the output node of q ("old_frontier_edge" below)
    *)
    from valid_frontier valid_q_before
    obtain frontier_node where
      old_frontier_node: 
      "nodes circuit (frontier q) = Some frontier_node"

and old_frontier_node_uses_q:
"node_uses_qubit frontier_node q"

and old_frontier_edge:
"make_edge (frontier q) (get_output_node_id q) q \<in> edges circuit"

and old_frontier_unique_successor:
"has_unique_wire_successor circuit q (frontier q)"

      unfolding is_valid_frontier_def
      by auto

(* new_node_id is unused (main assumption of this lemma), so nodes circuit new_node_id = None 
       But frontier q stores "Some frontier_node"

       Combining these two, we can say that frontier q \<noteq> new_node_id. This is proven below.
    *)
    have frontier_id_not_new_node_id:
      "frontier q \<noteq> new_node_id"
    proof
      assume same_id:
        "frontier q = new_node_id" (* Proof by contradiction *)

      from old_frontier_node
      have "nodes circuit new_node_id = Some frontier_node"
        using same_id by simp

      with node_id_unused 
      show False
        by simp
    qed

    show 
      "\<exists>frontier_node.
            nodes (insert_node new_node_id new_node circuit) (frontier q) = Some frontier_node
            \<and> node_uses_qubit frontier_node q
            \<and> make_edge (frontier q) (get_output_node_id q) q
                 \<in> edges (insert_node new_node_id new_node circuit)
            \<and> has_unique_wire_successor
             (insert_node new_node_id new_node circuit) q (frontier q)"

    proof (intro exI[of _ frontier_node] conjI)
      (* Start the proof by applying the introduction rules exI and conjI
        
        exI \<longrightarrow> Introduction rule for an existential statement P x \<Rightarrow> \<exists>x. P x (Predicate P, witness x)
        
        exI[of _ frontier_node] \<longrightarrow> for the existential statement, figure out the predicate yourself and use frontier_node as the witness. This changes the goal from 
            \<exists>frontier_node. A \<and> B \<and> C
        into:
            A \<and> B \<and> C
          
        conjI \<longrightarrow> splits the conjuction A \<and> B \<and> C into three separate proof goals A, B and C

        Each following show statement proves one of those goals.
      *)
      show "nodes (insert_node new_node_id new_node circuit) (frontier q) = Some frontier_node"
        using frontier_id_not_new_node_id old_frontier_node
        by simp

      show "node_uses_qubit frontier_node q"
        using old_frontier_node_uses_q by simp

      show "make_edge (frontier q) (get_output_node_id q) q 
                \<in> edges (insert_node new_node_id new_node circuit)"

        using old_frontier_edge
        unfolding insert_node_def
        by simp

      show "has_unique_wire_successor
           (insert_node new_node_id new_node circuit) q (frontier q)"
        using old_frontier_unique_successor
        unfolding
          has_unique_wire_successor_def
          wire_edge_relation_def
          insert_node_def
        by simp
    qed
  qed
qed

lemma update_next_id_preserves_valid_frontier:
  (* Updating only the next_id field preserves frontier validity.

     The frontier invariant depends on the circuit's qubit count, node mapping, and edge set. Updating next_id changes none of these fields.
  *)

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

shows 
  "is_valid_frontier (circuit \<lparr> next_id := new_next_id \<rparr>) frontier"

  unfolding is_valid_frontier_def

proof (intro allI impI)
  fix q

  assume valid_q:
    "qubit_in_circuit (circuit\<lparr>next_id := new_next_id\<rparr>) q"

  hence valid_q_before:
    "qubit_in_circuit circuit q"
    unfolding qubit_in_circuit_def
    by simp

  from valid_frontier valid_q_before
  obtain frontier_node where
    frontier_lookup:
    "nodes circuit (frontier q) = Some frontier_node"
    and frontier_uses_q:
    "node_uses_qubit frontier_node q"
    and frontier_edge:
    "make_edge (frontier q) (get_output_node_id q) q
         \<in> edges circuit"
    and frontier_unique_successor:
    "has_unique_wire_successor
         circuit q (frontier q)"
    unfolding is_valid_frontier_def
    by auto

  show
    "\<exists>frontier_node.
        nodes (circuit\<lparr>next_id := new_next_id\<rparr>) (frontier q)
          = Some frontier_node
      \<and> node_uses_qubit frontier_node q
      \<and> make_edge (frontier q) (get_output_node_id q) q
          \<in> edges (circuit\<lparr>next_id := new_next_id\<rparr>)
      \<and> has_unique_wire_successor
          (circuit\<lparr>next_id := new_next_id\<rparr>)
          q
          (frontier q)"
  proof (intro exI[of _ frontier_node] conjI)
    show
      "nodes (circuit\<lparr>next_id := new_next_id\<rparr>)
         (frontier q)
       = Some frontier_node"
      using frontier_lookup
      by simp

    show
      "node_uses_qubit frontier_node q"
      using frontier_uses_q
      by simp

    show
      "make_edge (frontier q) (get_output_node_id q) q
         \<in> edges (circuit\<lparr>next_id := new_next_id\<rparr>)"
      using frontier_edge
      by simp

    show
      "has_unique_wire_successor
         (circuit\<lparr>next_id := new_next_id\<rparr>)
         q
         (frontier q)"
      using frontier_unique_successor
      unfolding
        has_unique_wire_successor_def
        wire_edge_relation_def
      by simp
  qed
qed

lemma edges_insert_edge[simp]: (* helper lemma *)
  (* Edge set after insertion is just union of edge set prior to insertion and the newly added edge *)
  "edges (insert_edge e circuit) = insert e (edges circuit)"
  unfolding insert_edge_def
  by simp

lemma edges_delete_edge[simp]: (* helper lemma *)
  (* Edge set after deletion is just difference of edge set prior to deletion and the deleted edge *)
  "edges (delete_edge e circuit) = edges circuit - {e}"
  unfolding delete_edge_def
  by simp

lemma initial_frontier_is_valid:
  (* The initial frontier correctly points from each qubit to its input boundary node. *)
  "is_valid_frontier (initial_circuit number_of_qubits) initial_frontier"

proof -
  show ?thesis
    unfolding is_valid_frontier_def
  proof clarify
    fix q
    assume valid_q:
      "qubit_in_circuit (initial_circuit number_of_qubits) q"

    obtain qubit_number where
      q_form: "q = Qubit qubit_number"
      by (cases q)

    from valid_q have q_lt:
      "qubit_number < number_of_qubits"
      unfolding qubit_in_circuit_def
      using q_form
      by simp

    show
      "\<exists>frontier_node.
         nodes (initial_circuit number_of_qubits)
           (initial_frontier q)
           = Some frontier_node
       \<and> node_uses_qubit frontier_node q
       \<and> make_edge
           (initial_frontier q)
           (get_output_node_id q)
           q
         \<in> edges (initial_circuit number_of_qubits)
      \<and> has_unique_wire_successor (initial_circuit number_of_qubits) q (initial_frontier q)"
      using
        q_lt q_form
        all_wires_linear_def
        initial_circuit_has_linear_wires
        initial_circuit_has_wire_edge
        initial_circuit_input_node
        valid_q wire_is_linear_def
      unfolding initial_frontier_def
      by simp
  qed
qed

lemma initial_next_id_is_unused:
  (* The first operation-node ID is unused in the initial circuit. *)
  "next_id_is_unused (initial_circuit number_of_qubits)"
  unfolding next_id_is_unused_def
    initial_circuit_def
    initial_nodes_def
    get_first_operation_id_def
  by simp

lemma initial_existing_node_ids_are_below_next_id:
  (* Every node stored in the initial circuit is a boundary node whose
     numerical ID is strictly smaller than the first operation-node ID.

     The initial node table stores nodes only at IDs below
     2 * number_of_qubits, while next_id is exactly
     NodeId (2 * number_of_qubits).*)
  "all_existing_node_ids_below_next_id (initial_circuit number_of_qubits)"

  unfolding
    all_existing_node_ids_below_next_id_def
    initial_circuit_def
    initial_nodes_def
    get_first_operation_id_def

  using if_False
  by fastforce

end
