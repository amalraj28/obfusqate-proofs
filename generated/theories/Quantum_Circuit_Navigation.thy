theory Quantum_Circuit_Navigation
  imports Quantum_Circuit_Insert_Validity

begin

definition incoming_edge ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> edge option"
  where
    (* Return an edge entering node_id along wire q.

     In a valid linear quantum-circuit wire, such an edge is unique for
     every non-input node lying on q. If no such edge exists, return None.
  *)
  "incoming_edge circuit node_id q =
     (if \<exists>e \<in> edges circuit.
          edge_target e = node_id \<and>
          edge_wire e = q
      then
        Some
          (SOME e.
             e \<in> edges circuit \<and>
             edge_target e = node_id \<and>
             edge_wire e = q)
      else
        None)"

definition outgoing_edge ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> edge option"
where
  (* Return an edge leaving node_id along wire q.

     In a valid linear quantum-circuit wire, such an edge is unique for
     every non-output node lying on q. If no such edge exists, return None.
  *)
  "outgoing_edge circuit node_id q =
     (if \<exists>e \<in> edges circuit.
          edge_source e = node_id \<and>
          edge_wire e = q
      then
        Some
          (SOME e.
             e \<in> edges circuit \<and>
             edge_source e = node_id \<and>
             edge_wire e = q)
      else
        None)"

definition predecessor_on_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> node_id option"
where
  (* Return the source node of the edge entering node_id on wire q. *)
  "predecessor_on_wire circuit node_id q =
     map_option edge_source
       (incoming_edge circuit node_id q)"

definition successor_on_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> node_id option"
where
  (* Return the target node of the edge leaving node_id on wire q. *)
  "successor_on_wire circuit node_id q =
     map_option edge_target
       (outgoing_edge circuit node_id q)"

lemma incoming_edge_correct:
  (* Whenever incoming_edge returns Some e, e belongs to the circuit,
     enters the requested node, and lies on the requested wire. *)
  "incoming_edge circuit node_id q = Some e
   \<Longrightarrow> e \<in> edges circuit
     \<and> edge_target e = node_id
     \<and> edge_wire e = q"
  proof -
  assume incoming:
    "incoming_edge circuit node_id q = Some e"

  have edge_exists:
    "\<exists>candidate.
       candidate \<in> edges circuit
       \<and> edge_target candidate = node_id
       \<and> edge_wire candidate = q"
  proof (rule ccontr)
    assume no_edge:
      "\<not> (\<exists>candidate.
           candidate \<in> edges circuit
           \<and> edge_target candidate = node_id
           \<and> edge_wire candidate = q)"

    then have
      "incoming_edge circuit node_id q = None"
      unfolding incoming_edge_def
      by simp

    with incoming show False
      by simp
  qed

  have chosen_edge_correct:
    "(SOME candidate.
        candidate \<in> edges circuit
        \<and> edge_target candidate = node_id
        \<and> edge_wire candidate = q)
       \<in> edges circuit
     \<and> edge_target
         (SOME candidate.
            candidate \<in> edges circuit
            \<and> edge_target candidate = node_id
            \<and> edge_wire candidate = q)
         = node_id
     \<and> edge_wire
         (SOME candidate.
            candidate \<in> edges circuit
            \<and> edge_target candidate = node_id
            \<and> edge_wire candidate = q)
         = q"
    using edge_exists
    by (rule someI_ex)

  have returned_edge:
    "e =
      (SOME candidate.
         candidate \<in> edges circuit
         \<and> edge_target candidate = node_id
         \<and> edge_wire candidate = q)"
    using
      incoming
      edge_exists
    unfolding incoming_edge_def
    by (metis (lifting) option.inject)

  show
    "e \<in> edges circuit
     \<and> edge_target e = node_id
     \<and> edge_wire e = q"
    using chosen_edge_correct returned_edge
    by simp
qed

lemma outgoing_edge_correct:
  (* Whenever outgoing_edge returns Some e, e belongs to the circuit,
     leaves the requested node, and lies on the requested wire. *)
  "outgoing_edge circuit node_id q = Some e
   \<Longrightarrow> e \<in> edges circuit
     \<and> edge_source e = node_id
     \<and> edge_wire e = q"

proof -
  assume outgoing:
    "outgoing_edge circuit node_id q = Some e"

  have edge_exists:
    "\<exists>candidate.
       candidate \<in> edges circuit
       \<and> edge_source candidate = node_id
       \<and> edge_wire candidate = q"
  proof (rule ccontr)
    assume no_edge:
      "\<not> (\<exists>candidate.
           candidate \<in> edges circuit
           \<and> edge_source candidate = node_id
           \<and> edge_wire candidate = q)"

    then have
      "outgoing_edge circuit node_id q = None"
      unfolding outgoing_edge_def
      by simp

    with outgoing show False
      by simp
  qed

  have chosen_edge_correct:
    "(SOME candidate.
        candidate \<in> edges circuit
        \<and> edge_source candidate = node_id
        \<and> edge_wire candidate = q)
       \<in> edges circuit
     \<and> edge_source
         (SOME candidate.
            candidate \<in> edges circuit
            \<and> edge_source candidate = node_id
            \<and> edge_wire candidate = q)
         = node_id
     \<and> edge_wire
         (SOME candidate.
            candidate \<in> edges circuit
            \<and> edge_source candidate = node_id
            \<and> edge_wire candidate = q)
         = q"
    using edge_exists
    by (rule someI_ex)

  have returned_edge:
    "e =
      (SOME candidate.
         candidate \<in> edges circuit
         \<and> edge_source candidate = node_id
         \<and> edge_wire candidate = q)"
    using
      outgoing
      edge_exists
    unfolding outgoing_edge_def
    by (metis (lifting) option.inject)

  show
    "e \<in> edges circuit
     \<and> edge_source e = node_id
     \<and> edge_wire e = q"
    using chosen_edge_correct returned_edge
    by simp
qed

lemma predecessor_on_wire_correct:
  (* Whenever predecessor_on_wire returns Some predecessor, the circuit
     contains the corresponding predecessor-to-node edge on wire q. *)
  "predecessor_on_wire circuit node_id q = Some predecessor
   \<Longrightarrow> make_edge predecessor node_id q \<in> edges circuit"

proof -
  assume predecessor:
    "predecessor_on_wire circuit node_id q = Some predecessor"

  show
    "make_edge predecessor node_id q \<in> edges circuit"
  proof (cases "incoming_edge circuit node_id q")

    case None

    then have
      "predecessor_on_wire circuit node_id q = None"
      unfolding predecessor_on_wire_def
      by simp

    with predecessor show ?thesis
      by simp

  next
    case (Some e)

    have source:
      "edge_source e = predecessor"
      using predecessor Some
      unfolding predecessor_on_wire_def
      by simp

    have incoming_properties:
      "e \<in> edges circuit
       \<and> edge_target e = node_id
       \<and> edge_wire e = q"
      using
        Some
        incoming_edge_correct
      by simp

    have edge_identity:
      "e = make_edge predecessor node_id q"
      using
        incoming_properties
        source
        make_edge_def
      by (cases e) simp

    show ?thesis
      using incoming_properties edge_identity
      by simp

  qed
qed

lemma successor_on_wire_correct:
  (* Whenever successor_on_wire returns Some successor, the circuit
     contains the corresponding node-to-successor edge on wire q. *)
  "successor_on_wire circuit node_id q = Some successor
   \<Longrightarrow> make_edge node_id successor q \<in> edges circuit"

proof -
  assume successor:
    "successor_on_wire circuit node_id q = Some successor"

  show
    "make_edge node_id successor q \<in> edges circuit"

  proof (cases "outgoing_edge circuit node_id q")
    case None
    then have 
      "successor_on_wire circuit node_id q = None"
      unfolding successor_on_wire_def
      by simp

    with successor show ?thesis
      by simp

  next
    case (Some e)

    have target:
      "edge_target e = successor"
      using successor Some
      unfolding successor_on_wire_def
      by simp

    have outgoing_properties:
      "e \<in> edges circuit
       \<and> edge_source e = node_id
       \<and> edge_wire e = q"
      using
        Some
        outgoing_edge_correct
      by simp

    have edge_identity:
      "e = make_edge node_id successor q"
      using
        outgoing_properties
        target
        make_edge_def
      by (cases e) simp
      
    show ?thesis
      using
        outgoing_properties
        edge_identity
      by simp
  qed
qed

lemma predecessor_on_wire_not_self:
  assumes acyclic:
    "is_acyclic_circuit circuit"

  assumes predecessor:
    "predecessor_on_wire circuit node_id q =
       Some predecessor_node"

  shows
    "predecessor_node \<noteq> node_id"
proof

  assume predecessor_eq:
    "predecessor_node = node_id"

  have self_loop_edge:
    "make_edge node_id node_id q \<in> edges circuit"
    using
      predecessor_on_wire_correct[OF predecessor]
      predecessor_eq
    by simp

  have self_loop_relation:
    "(node_id, node_id) \<in> edge_relation circuit"
    using self_loop_edge
    unfolding
      edge_relation_def
      make_edge_def
    by force

  have self_reachable:
    "(node_id, node_id) \<in> (edge_relation circuit)\<^sup>+"
    using self_loop_relation
    by (rule r_into_trancl)

  show False
    using acyclic self_reachable
    unfolding is_acyclic_circuit_def
    by (simp add: acyclic_def)
qed

lemma successor_on_wire_not_self:
  assumes acyclic:
    "is_acyclic_circuit circuit"

  assumes successor:
    "successor_on_wire circuit node_id q =
       Some successor_node"

  shows
    "successor_node \<noteq> node_id"
proof

  assume successor_eq:
    "successor_node = node_id"

  have self_loop_edge:
    "make_edge node_id node_id q \<in> edges circuit"
    using
      successor_on_wire_correct[OF successor]
      successor_eq
    by simp

  have self_loop_relation:
    "(node_id, node_id) \<in> edge_relation circuit"
    using self_loop_edge
    unfolding
      edge_relation_def
      make_edge_def
    by force

  have self_reachable:
    "(node_id, node_id) \<in> (edge_relation circuit)\<^sup>+"
    using self_loop_relation
    by (rule r_into_trancl)

  show False
    using acyclic self_reachable
    unfolding is_acyclic_circuit_def
    by (simp add: acyclic_def)
qed

end
