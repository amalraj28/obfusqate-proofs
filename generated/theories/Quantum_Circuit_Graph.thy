theory Quantum_Circuit_Graph
  imports Quantum_Circuit_Data

begin

definition node_exists :: "quantum_circuit \<Rightarrow> node_id \<Rightarrow> bool" where
  (* Checks whether a node Id exists in the given quantum circuit *)
  "node_exists circuit node_id \<longleftrightarrow>
     nodes circuit node_id \<noteq> None
  "
fun node_uses_qubit :: "circuit_node \<Rightarrow> qubit \<Rightarrow> bool" where
  (* Given a circuit node and a qubit (wire), this function checks whether the circuit node lies on the given qubit wire *)
  "node_uses_qubit (InputNode q) r = (q = r)"
| "node_uses_qubit (OutputNode q) r = (q = r)"
| "node_uses_qubit (OperationNode op) r = (r \<in> set (op_qargs op))"
definition qubit_in_circuit :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> bool" where
  (* Given a quantum circuit and a qubit, returns true if the qubit is in the range [0, num_qubits-1] (that is, the qubit is a valid one) *)
  "qubit_in_circuit circuit q \<longleftrightarrow>
     get_qubit_index q < num_qubits circuit"
definition is_well_formed_edge :: "quantum_circuit \<Rightarrow> edge \<Rightarrow> bool" where
  (* An edge is well-formed (valid) iff
      1. The source node exists in the circuit
      2. The target node exists in the circuit
      3. The edge wire (qubit) is valid for the given circuit
      4. The source node should lie on the edge wire
      5. The target node should lie on the edge wire
  *)
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
  (* Checks if all edges present in the quantum circuit are well-formed *)
  "are_well_formed_edges circuit \<longleftrightarrow>
     (\<forall>e \<in> edges circuit. is_well_formed_edge circuit e
     )
  "
definition edge_relation :: "quantum_circuit \<Rightarrow> (node_id \<times> node_id) set" where
  (* Convert the circuit's wire-labelled edges into an ordinary
     directed relation between node IDs.

     A pair (source_id, target_id) belongs to this relation exactly
     when the circuit contains at least one edge whose source and
     target are those node IDs.

     The qubit label is intentionally ignored here because acyclicity
     concerns directed reachability between graph vertices, regardless
     of which wire carries each edge.
  *)
  "edge_relation circuit =
     {(source_id, target_id).
        \<exists>e \<in> edges circuit.
          edge_source e = source_id
        \<and> edge_target e = target_id}"
definition is_acyclic_circuit :: "quantum_circuit \<Rightarrow> bool" where
  (* A circuit is acyclic when its directed node relation contains
     no directed cycle.

     Equivalently, no node can be reached again by repeatedly following
     one or more directed circuit edges from itself.
  *)
  "is_acyclic_circuit circuit \<longleftrightarrow> acyclic (edge_relation circuit)"
definition wire_edge_relation :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> (node_id \<times> node_id) set" where
  (* The directed graph relation formed only by edges carrying qubit q.

     A pair (source_id, target_id) belongs to this relation exactly when
     the circuit contains an edge from source_id to target_id whose wire
     label is q.

     Unlike edge_relation, this relation keeps only the dependency
     structure of one individual qubit wire.
  *)
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
  (* A node has exactly one immediate predecessor on wire q. *)
  "has_unique_wire_predecessor circuit q node_id \<longleftrightarrow>
     (\<exists>! predecessor_id. \<comment>\<open>\<exists>! means exactly one\<close>
        (predecessor_id, node_id)
          \<in> wire_edge_relation circuit q)"
definition has_unique_wire_successor :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool" where
  (* A node has exactly one immediate successor on wire q. *)
  "has_unique_wire_successor circuit q node_id \<longleftrightarrow>
     (\<exists>! successor_id. \<comment>\<open>\<exists>! means exactly one\<close>
        (node_id, successor_id)
          \<in> wire_edge_relation circuit q)"
lemma wire_edge_implies_wire_reaches:
  (* A direct q-labelled edge is a path of length one, so its source 
     reaches its target along wire q. *)
  assumes direct_edge:
    "(source_id, target_id) \<in> wire_edge_relation circuit q"

shows
  "wire_reaches circuit q source_id target_id"

  unfolding wire_reaches_def
  using direct_edge by simp
definition nodes_comparable_on_wire :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> bool" where
  (* Every pair of existing nodes that uses wire q must be ordered
     along that wire.

     For any such nodes node_a and node_b, either:
       1. they are the same node;
       2. node_a occurs before node_b on q; or
       3. node_b occurs before node_a on q.
  *)
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
  (* Wire q forms one directed, non-branching chain.

     The canonical input node:
       - has no predecessor on q;
       - has exactly one successor on q.

     The canonical output node:
       - has exactly one predecessor on q;
       - has no successor on q.

     Every operation node using q:
       - has exactly one predecessor on q;
       - has exactly one successor on q.

     Comparability ensures that all nodes using q belong to one ordered
     chain rather than several disconnected chains.
  *)
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
  (* Every valid qubit wire in the circuit forms one linear chain. *)
  "all_wires_linear circuit \<longleftrightarrow>
     (\<forall>q.
        qubit_in_circuit circuit q
        \<longrightarrow> wire_is_linear circuit q)"
definition all_wire_nodes_comparable :: "quantum_circuit \<Rightarrow> bool" where
  (* Every valid qubit wire in the circuit has a total reachability
     ordering among all existing nodes that use that wire.

     This means that two operations acting on the same qubit cannot be
     unrelated in the graph.
  *)
  "all_wire_nodes_comparable circuit \<longleftrightarrow>
     (\<forall>q.
        qubit_in_circuit circuit q
        \<longrightarrow> nodes_comparable_on_wire circuit q)"
lemma initial_circuit_nodes_comparable_on_wire:
  (* In the initial circuit, the only nodes using a valid wire q are its canonical input node and output node. These two nodes are connected by the initial wire edge, so they are comparable. *)
  assumes valid_qubit:
    "qubit_in_circuit (initial_circuit number_of_qubits) q"
  shows
    "nodes_comparable_on_wire
       (initial_circuit number_of_qubits)
       q"
  unfolding nodes_comparable_on_wire_def

proof (intro allI impI)
  fix node_a node_b node_a_value node_b_value

  let ?init_circuit = "initial_circuit number_of_qubits"

  assume node_a_lookup:
    "nodes ?init_circuit node_a = Some node_a_value"

  assume node_b_lookup:
    "nodes ?init_circuit node_b = Some node_b_value"

  assume node_a_uses_q:
    "node_uses_qubit node_a_value q"

  assume node_b_uses_q:
    "node_uses_qubit node_b_value q"

  have node_a_cases:
    "node_a = get_input_node_id q 
     \<or> node_a = get_output_node_id q"

  proof -
    obtain node_index where node_a_eq:
      "node_a = NodeId node_index"
      by (cases node_a) simp

    obtain qubit_index where q_eq:
      "q = Qubit qubit_index"
      by (cases q) simp

    show ?thesis
      using node_a_lookup node_a_uses_q
      unfolding
        node_a_eq
        q_eq
        initial_circuit_def
        initial_nodes_def
        get_input_node_id_def
        get_output_node_id_def
      by (auto split: if_splits; presburger)
  qed

  have node_b_cases:
    "node_b = get_input_node_id q 
     \<or>node_b = get_output_node_id q"

  proof -
    obtain node_index where node_b_eq:
      "node_b = NodeId node_index"
      by (cases node_b) simp

    obtain qubit_index where q_eq:
      "q = Qubit qubit_index"
      by (cases q) simp

    show ?thesis
      using node_b_lookup node_b_uses_q
      unfolding
        node_b_eq
        q_eq
        initial_circuit_def
        initial_nodes_def
        get_input_node_id_def
        get_output_node_id_def
      by (auto split: if_splits; presburger)
  qed

  from node_a_cases node_b_cases show
    "node_a = node_b
     \<or> wire_reaches ?init_circuit q node_a node_b
     \<or> wire_reaches ?init_circuit q node_b node_a"
  proof (elim disjE)

    assume node_a_input:
      "node_a = get_input_node_id q"

    assume node_b_input:
      "node_b = get_input_node_id q"

    then show ?thesis
      using node_a_input
      by simp

  next

    assume node_a_input:
      "node_a = get_input_node_id q"

    assume node_b_output:
      "node_b = get_output_node_id q"

    have valid_qubit_index:
      "get_qubit_index q < number_of_qubits"
      using valid_qubit
      unfolding qubit_in_circuit_def
      by simp

    have direct_wire_edge:
      "(get_input_node_id q, get_output_node_id q)
       \<in> wire_edge_relation ?init_circuit q"
    proof -
      obtain qubit_index where q_eq:
        "q = Qubit qubit_index"
        by (cases q) simp

      have
        "make_edge
           (get_input_node_id q)
           (get_output_node_id q)
           q
         \<in> edges ?init_circuit"
        using valid_qubit_index
        unfolding q_eq
        by (simp add: initial_circuit_has_wire_edge)

      then show ?thesis
        unfolding wire_edge_relation_def
        by simp
    qed

    have reaches_output:
      "wire_reaches ?init_circuit q
         (get_input_node_id q)
         (get_output_node_id q)"
      using direct_wire_edge
      by (rule wire_edge_implies_wire_reaches)

    show ?thesis
      using node_a_input node_b_output reaches_output
      by simp

  next

    assume node_a_output:
      "node_a = get_output_node_id q"

    assume node_b_input:
      "node_b = get_input_node_id q"

    have valid_qubit_index:
      "get_qubit_index q < number_of_qubits"
      using valid_qubit
      unfolding qubit_in_circuit_def
      by simp

    have direct_wire_edge:
      "(get_input_node_id q, get_output_node_id q)
       \<in> wire_edge_relation ?init_circuit q"
    proof -
      obtain qubit_index where q_eq:
        "q = Qubit qubit_index"
        by (cases q) simp

      have
        "make_edge
           (get_input_node_id q)
           (get_output_node_id q)
           q
         \<in> edges ?init_circuit"
        using valid_qubit_index
        unfolding q_eq
        by (simp add: initial_circuit_has_wire_edge)

      then show ?thesis
        unfolding wire_edge_relation_def
        by simp
    qed

    have input_reaches_output:
      "wire_reaches ?init_circuit q
         (get_input_node_id q)
         (get_output_node_id q)"
      using direct_wire_edge
      by (rule wire_edge_implies_wire_reaches)

    show ?thesis
      using node_a_output node_b_input input_reaches_output
      by simp

  next

    assume node_a_output:
      "node_a = get_output_node_id q"

    assume node_b_output:
      "node_b = get_output_node_id q"

    then show ?thesis
      using node_a_output
      by simp

  qed
qed
lemma initial_circuit_all_wire_nodes_comparable:
  (* Every valid wire in the initial circuit contains only its input and output nodes, connected by the canonical input-to-output edge. Therefore, all nodes using every valid wire are comparable. *)
  "all_wire_nodes_comparable
     (initial_circuit number_of_qubits)"

  unfolding all_wire_nodes_comparable_def

proof (intro allI impI)
  fix q

  assume valid_qubit:
    "qubit_in_circuit (initial_circuit number_of_qubits) q"

  show 
    "nodes_comparable_on_wire (initial_circuit number_of_qubits) q"
    using valid_qubit
    by (rule initial_circuit_nodes_comparable_on_wire)
qed
definition operation_in_circuit :: "quantum_circuit \<Rightarrow> operation \<Rightarrow> bool" where
  (* Checks whether a given operation belongs to the given quantum circuit. An operation belongs to the given circuit iff
      1. The operation itself is valid (correct arity and distinct qubits)
      2. Every qubit used by the operation belongs to the circuit
  *)
  "operation_in_circuit circuit op \<longleftrightarrow>
      is_valid_operation op
    \<and> (\<forall>q \<in> set (op_qargs op). qubit_in_circuit circuit q)
  "
definition are_well_formed_operation_nodes :: "quantum_circuit \<Rightarrow> bool" where
  (* Checks whether every OperationNode stored in the circuit is well-formed. That is, every operation node must contain an operation that is valid for this circuit.
  *)
  "are_well_formed_operation_nodes circuit \<longleftrightarrow>
     (\<forall>node_id op.
        nodes circuit node_id = Some (OperationNode op) \<longrightarrow>
        operation_in_circuit circuit op
     )
  "
definition are_well_formed_boundary_nodes :: "quantum_circuit \<Rightarrow> bool" where
  (* Checks whether every valid qubit in the circuit has the correct canonical input and output nodes (boundary nodes) *)

(* TODO: Add checks to ensure that there are no invalid boundary nodes anywhere as well, meaning an input node like InputNode (Qubit 999) doesn't exist *)
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
  (* A circuit is well-formed iff
      1. Its boundary input/output nodes are well-formed
      2. All its edges are well-formed
      3. All its operation nodes are well-formed
  *)
  "is_well_formed_circuit circuit \<longleftrightarrow>
       are_well_formed_boundary_nodes circuit
     \<and> are_well_formed_edges circuit
     \<and> are_well_formed_operation_nodes circuit
  "
definition is_valid_circuit :: "quantum_circuit \<Rightarrow> bool" where
  (* A structurally valid quantum circuit satisfies every invariant
     established for the DAG representation. *)
  "is_valid_circuit circuit \<longleftrightarrow>
      is_well_formed_circuit circuit
    \<and> is_acyclic_circuit circuit
    \<and> all_wires_linear circuit"
lemma initial_edges_cases: (* helper lemma *)
  (* Assuming that an edge e belongs to the initial circuit, this proof says that we can always find a qubit `qubit_number` such that the edge e is canonical input-to-output edge for that qubit. Meaning, edge e would always be from some InputNode(q0) to OutputNode(q0), where q0 is a valid qubit.
  *)
  assumes "e \<in> edges (initial_circuit number_of_qubits)"
  obtains qubit_number where
    "qubit_number < number_of_qubits"
    "e = make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)"
  using assms
  unfolding initial_circuit_def initial_edges_def
  by auto
lemma initial_edge_relation_cases:
  (* Every source-target pair in the initial circuit relation comes
     from one canonical input-to-output edge of a valid qubit. *)
  assumes relation_pair:
    "(source_id, target_id) \<in> edge_relation (initial_circuit number_of_qubits)"

obtains qubit_number where
  "qubit_number < number_of_qubits"
  "source_id = get_input_node_id (Qubit qubit_number)"
  "target_id = get_output_node_id (Qubit qubit_number)"

proof - 
  from relation_pair obtain e where
    edge_in: "e \<in> edges (initial_circuit number_of_qubits)"
    and source_eq: "edge_source e = source_id"
    and target_eq: "edge_target e = target_id"
    unfolding edge_relation_def
    by auto

  from edge_in obtain qubit_number where
    qubit_valid: "qubit_number < number_of_qubits"
    and edge_eq:
    "e =
        make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)"
    by (elim initial_edges_cases)

  show thesis
    using that[of qubit_number]
      qubit_valid
      source_eq
      target_eq
      edge_eq
    unfolding make_edge_def
    by simp
qed
lemma initial_edge_relation_cannot_compose:
  (* Two edges of the initial circuit relation cannot be composed.

     The target of every initial edge is an output node ID, while the
     source of every initial edge is an input node ID. No output node ID
     can equal any input node ID.
  *)
  assumes first_edge:
    "(first_source, middle_node)
       \<in> edge_relation (initial_circuit number_of_qubits)"

assumes second_edge:
  "(middle_node, second_target)
       \<in> edge_relation (initial_circuit number_of_qubits)"

shows False

proof -
  from first_edge obtain first_qubit where
    first_target:
    "middle_node =
       get_output_node_id (Qubit first_qubit)"
    by (elim initial_edge_relation_cases)

  from second_edge obtain second_qubit where
    second_source:
    "middle_node =
       get_input_node_id (Qubit second_qubit)"
    by (elim initial_edge_relation_cases)

  from first_target second_source show False
    using input_output_ids_distinct[
        of "Qubit second_qubit" "Qubit first_qubit"]
    by simp
qed
lemma initial_circuit_has_no_operation_nodes:(* helper lemma *)
  (* Proves that an initial circuit does not have any operation node  *)
  "nodes (initial_circuit number_of_qubits) node_id \<noteq> Some (OperationNode op)"
  unfolding initial_circuit_def initial_nodes_def
  by (cases node_id; simp split: if_splits)
lemma initial_circuit_is_well_formed:
  (* Proving that the initial empty circuit is a well-formed (valid) circuit *)
  "is_well_formed_circuit (initial_circuit number_of_qubits)"

proof -
  have boundary: (*Prove that initial circuit has well formed boundary nodes *)
    "are_well_formed_boundary_nodes (initial_circuit number_of_qubits)"
    unfolding are_well_formed_boundary_nodes_def
    by (simp add: initial_circuit_input_node initial_circuit_output_node)

  have edges:(* Prove that initial circuit has well formed edges *)
    "are_well_formed_edges (initial_circuit number_of_qubits)"
  proof -
    show ?thesis
      unfolding are_well_formed_edges_def
    proof (intro ballI) (* Introduce a bounded universal proof *)
      fix e (* Pick an arbitrary edge e, and prove the property for that edge *)
      assume edge_in:
        "e \<in> edges (initial_circuit number_of_qubits)"

      from edge_in obtain qubit_number where
        q_lt: "qubit_number < number_of_qubits"
        and edge_eq:
        "e =
          make_edge
            (get_input_node_id (Qubit qubit_number))
            (get_output_node_id (Qubit qubit_number))
            (Qubit qubit_number)"
        by (blast elim: initial_edges_cases)

      show "is_well_formed_edge (initial_circuit number_of_qubits) e"
        unfolding is_well_formed_edge_def
          node_exists_def
          qubit_in_circuit_def
        using q_lt edge_eq
        by (simp add:
            make_edge_def
            initial_circuit_input_node
            initial_circuit_output_node)
    qed
  qed

  have op_nodes: (* Prove that initial circuit has well formed operation nodes. There are no operation nodes, so this will be a vacuous truth *)
    "are_well_formed_operation_nodes (initial_circuit number_of_qubits)"
    unfolding are_well_formed_operation_nodes_def
    using initial_circuit_has_no_operation_nodes by simp

  show ?thesis
    unfolding is_well_formed_circuit_def
    using boundary edges op_nodes
    by simp
qed
lemma initial_circuit_is_acyclic:
  (* The initial circuit is acyclic because every edge goes directly
     from an input boundary node to an output boundary node, and output
     nodes have no outgoing edges. *)
  "is_acyclic_circuit (initial_circuit number_of_qubits)"

proof -
  show ?thesis
    unfolding is_acyclic_circuit_def acyclic_def

  proof (intro allI notI)
    fix node_id

    assume cycle:
      "(node_id, node_id)
       \<in> (edge_relation
            (initial_circuit number_of_qubits))\<^sup>+"

    from cycle show False
    proof (induction rule: trancl_induct)
      have initial_path_is_single_edge:
        "\<And>source_id target_id.
           (source_id, target_id)
             \<in> (edge_relation
                  (initial_circuit number_of_qubits))\<^sup>+
           \<Longrightarrow>
           (source_id, target_id)
             \<in> edge_relation
                  (initial_circuit number_of_qubits)"
      proof - 
        fix source_id target_id

        assume path: 
          "(source_id, target_id)
           \<in> (edge_relation
                (initial_circuit number_of_qubits))\<^sup>+"

        from path show
          "(source_id, target_id)
           \<in> edge_relation
                (initial_circuit number_of_qubits)"
        proof (induction rule: trancl_induct)
          case (base intermediate_id)

          then show ?case
            by assumption

        next
          case (step intermediate_id final_id)

          have first_edge:
            "(source_id, intermediate_id)
             \<in> edge_relation
                  (initial_circuit number_of_qubits)"
            using step.IH .

          have second_edge:
            "(intermediate_id, final_id)
             \<in> edge_relation
                  (initial_circuit number_of_qubits)"
            using step.hyps(2) .

          have False
            using
              initial_edge_relation_cannot_compose[
                OF first_edge second_edge]
            .
          then show ?case
            by simp
        qed
      qed

      have direct_self_edge:
        "(node_id, node_id)
         \<in> edge_relation
              (initial_circuit number_of_qubits)"
        using initial_path_is_single_edge cycle
        by simp

      from direct_self_edge obtain qubit_number where
        node_is_input:
        "node_id =
           get_input_node_id (Qubit qubit_number)"
        and node_is_output:
        "node_id =
           get_output_node_id (Qubit qubit_number)"
        by (elim initial_edge_relation_cases)

      from node_is_input node_is_output show False
        using input_output_ids_distinct[
            of "Qubit qubit_number" "Qubit qubit_number"]
        by simp
    qed
  qed
qed
lemma initial_circuit_has_linear_wires:
  (* Every valid wire in the initial circuit consists of exactly one
     directed edge from its canonical input node to its canonical
     output node. Therefore, every initial wire is linear. *)
  "all_wires_linear (initial_circuit number_of_qubits)"
  unfolding all_wires_linear_def

proof (intro allI impI)
  fix q
  assume valid_qubit:
    "qubit_in_circuit (initial_circuit number_of_qubits) q"

  let ?init_circuit = "initial_circuit number_of_qubits"

  show "wire_is_linear ?init_circuit q"

  proof -
    have nodes_comparable:
      "nodes_comparable_on_wire ?init_circuit q"
      using valid_qubit
      by (simp add: initial_circuit_nodes_comparable_on_wire)

    have input_has_no_predecessor:
      "(\<nexists> predecessor_id.
          (predecessor_id, get_input_node_id q) \<in> wire_edge_relation ?init_circuit q)"
    proof
      assume predecessor_exists:
        "(\<exists> predecessor_id.
            (predecessor_id, get_input_node_id q) \<in> wire_edge_relation ?init_circuit q)"
      then obtain predecessor_id where
        predecessor_edge:
        "(predecessor_id, get_input_node_id q) \<in> wire_edge_relation ?init_circuit q"
        by auto

      have edge_in_initial_circuit:
        "make_edge
            predecessor_id
            (get_input_node_id q)
            q
           \<in> edges ?init_circuit"
        using predecessor_edge
        unfolding wire_edge_relation_def
        by simp

      from edge_in_initial_circuit obtain qubit_number where
        valid_edge_qubit:
        "qubit_number < number_of_qubits"
        and edge_shape:
        "make_edge
              predecessor_id
              (get_input_node_id q)
              q
            =
            make_edge
              (get_input_node_id (Qubit qubit_number))
              (get_output_node_id (Qubit qubit_number))
              (Qubit qubit_number)"
        by (auto elim: initial_edges_cases)

      have impossible_target_equality:
        "get_input_node_id q = get_output_node_id (Qubit qubit_number)"
        using edge_shape
        unfolding make_edge_def
        by simp

      show False
        using impossible_target_equality
        by simp
    qed

    have output_has_no_successor:
      "(\<nexists> successor_id.
          (get_output_node_id q, successor_id) \<in> wire_edge_relation ?init_circuit q)"

    proof
      assume successor_exists:
        "(\<exists> successor_id.
            (get_output_node_id q, successor_id) \<in> wire_edge_relation ?init_circuit q)"

      then obtain successor_id where
        successor_edge:
        "(get_output_node_id q, successor_id) \<in> wire_edge_relation ?init_circuit q"
        by auto

      have edge_in_initial_circuit:
        "make_edge (get_output_node_id q) successor_id q \<in> edges ?init_circuit"
        using successor_edge
        unfolding wire_edge_relation_def
        by simp

      from edge_in_initial_circuit obtain qubit_number where
        valid_edge_qubit: "qubit_number < number_of_qubits"
        and
        edge_shape:
        "make_edge (get_output_node_id q) successor_id q
             =
             make_edge (get_input_node_id (Qubit qubit_number))
                       (get_output_node_id (Qubit qubit_number))
                       (Qubit qubit_number)
            "

        by (auto elim: initial_edges_cases)

      show False
        using edge_shape
        unfolding make_edge_def
          get_input_node_id_def
          get_output_node_id_def
        by (cases q; simp)
    qed

    have unique_successor:
      "has_unique_wire_successor ?init_circuit q (get_input_node_id q)"
    proof -
      obtain qubit_number where q_eq:
        "q = Qubit qubit_number"
        by (cases q) simp

      have valid_qubit_number:
        "qubit_number < number_of_qubits"
        using valid_qubit
        unfolding qubit_in_circuit_def q_eq
        by simp

      have canonical_edge:
        "(get_input_node_id q, get_output_node_id q) \<in> wire_edge_relation ?init_circuit q"
      proof -
        have 
          "make_edge
             (get_input_node_id q)
             (get_output_node_id q)
             q
             \<in> edges ?init_circuit"
          using valid_qubit_number
          unfolding q_eq
          by (simp add: initial_circuit_has_wire_edge)

        then show ?thesis
          unfolding wire_edge_relation_def
          by simp
      qed

      show ?thesis
        unfolding has_unique_wire_successor_def

      proof (rule ex1I[of _ "get_output_node_id q"])
        show 
          "(get_input_node_id q, get_output_node_id q)
               \<in> wire_edge_relation ?init_circuit q"
          using canonical_edge .

      next
        fix successor_id
        assume successor_edge:
          "(get_input_node_id q, successor_id)
               \<in> wire_edge_relation ?init_circuit q"

        have edge_in_initial_circuit:
          "make_edge
               (get_input_node_id q) successor_id  q
             \<in> edges ?init_circuit"

          using successor_edge
          unfolding wire_edge_relation_def
          by simp

        from edge_in_initial_circuit obtain other_qubit_number where
          valid_other_qubit:
          "other_qubit_number < number_of_qubits"
          and edge_shape:
          "make_edge
                 (get_input_node_id q)
                 successor_id
                 q
               =
               make_edge
                 (get_input_node_id (Qubit other_qubit_number))
                 (get_output_node_id (Qubit other_qubit_number))
                 (Qubit other_qubit_number)"
          by (auto elim: initial_edges_cases)

        show
          "successor_id = get_output_node_id q"
          using edge_shape
          unfolding make_edge_def
          by auto
      qed
    qed

    have unique_predecessor:
      "has_unique_wire_predecessor ?init_circuit q (get_output_node_id q)"

    proof -
      obtain qubit_number where q_eq:
        "q = Qubit qubit_number"
        by (cases q) simp

      have valid_qubit_number:
        "qubit_number < number_of_qubits"
        using valid_qubit
        unfolding qubit_in_circuit_def q_eq
        by simp

      have canonical_edge:
        "(get_input_node_id q, get_output_node_id q)
           \<in> wire_edge_relation ?init_circuit q"
      proof -
        have
          "make_edge
             (get_input_node_id q)
             (get_output_node_id q)
             q
           \<in> edges ?init_circuit"
          using valid_qubit_number
          unfolding q_eq
          by (simp add: initial_circuit_has_wire_edge)

        then show ?thesis
          unfolding wire_edge_relation_def
          by simp
      qed

      show ?thesis
        unfolding has_unique_wire_predecessor_def
      proof (rule ex1I[of _ "get_input_node_id q"])

        show
          "(get_input_node_id q, get_output_node_id q)
             \<in> wire_edge_relation ?init_circuit q"
          using canonical_edge .

      next

        fix predecessor_id

        assume predecessor_edge:
          "(predecessor_id, get_output_node_id q)
             \<in> wire_edge_relation ?init_circuit q"

        have edge_in_initial_circuit:
          "make_edge
             predecessor_id
             (get_output_node_id q)
             q
           \<in> edges ?init_circuit"
          using predecessor_edge
          unfolding wire_edge_relation_def
          by simp

        from edge_in_initial_circuit obtain other_qubit_number where
          valid_other_qubit:
          "other_qubit_number < number_of_qubits"
          and edge_shape:
          "make_edge
               predecessor_id
               (get_output_node_id q)
               q
             =
             make_edge
               (get_input_node_id (Qubit other_qubit_number))
               (get_output_node_id (Qubit other_qubit_number))
               (Qubit other_qubit_number)"
          by (blast elim: initial_edges_cases)

        show
          "predecessor_id = get_input_node_id q"
          using edge_shape
          unfolding make_edge_def
          by auto
      qed
    qed

    have operation_node_property:
      "\<forall>node_id op.
         nodes ?init_circuit node_id = Some (OperationNode op)
         \<longrightarrow> node_uses_qubit (OperationNode op) q
         \<longrightarrow> has_unique_wire_predecessor ?init_circuit q node_id
           \<and> has_unique_wire_successor ?init_circuit q node_id"
    proof (intro allI impI)
      fix node_id op
      assume operation_node_exists:
        "nodes ?init_circuit node_id = Some (OperationNode op)"

      assume operation_uses_q:
        "node_uses_qubit (OperationNode op) q"

      have False
        using
          operation_node_exists
          initial_circuit_has_no_operation_nodes
        by blast

      then show
        "has_unique_wire_predecessor ?init_circuit q node_id
         \<and> has_unique_wire_successor ?init_circuit q node_id"
        by simp
    qed

    show "wire_is_linear (initial_circuit number_of_qubits) q"
      unfolding wire_is_linear_def
      using
        nodes_comparable
        input_has_no_predecessor
        output_has_no_successor
        unique_successor
        unique_predecessor
        operation_node_property
      by simp
  qed
qed
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
