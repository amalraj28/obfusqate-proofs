theory Quantum_Circuit_Replacement
  imports Quantum_Circuit_State

begin

definition is_operation_node_id ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> bool"
  where 
    (* True iff the supplied node ID currently stores an operation node. *)
  "is_operation_node_id circuit node_id \<longleftrightarrow>
     (\<exists>op. nodes circuit node_id = Some (OperationNode op))"

definition replace_operation ::
  "node_id \<Rightarrow> operation \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
  where
    (* Replace an existing operation node.
     If the supplied node ID does not refer to an OperationNode,
     leave the circuit unchanged. *)
  "replace_operation node_id replacement_op circuit = (
       case nodes circuit node_id of
         Some (OperationNode old_op) \<Rightarrow> insert_node node_id (OperationNode replacement_op) circuit
       | _ \<Rightarrow> circuit
     )"

definition valid_operation_replacement ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> operation \<Rightarrow> bool"
  where
    (* A replacement is structurally valid iff:

         1. The selected node ID currently stores an existing operation node.

         2. The replacement operation is valid for the circuit. In particular,
          it has the correct gate arity, uses distinct qubits, and every qubit
          used by it belongs to the circuit.

         3. The replacement operation uses exactly the same ordered qubit list
          as the original operation.

       The equality of op_qargs is essential because replace_operation changes only the operation 
       stored at the node and leaves the edge set unchanged.

     Therefore, every incoming and outgoing edge incident on the selected node
     remains labelled by a qubit used by the replacement operation. Changing
     the qubit interface would require rewiring the graph and should instead
     be handled by a separate graph transformation.
  *)
  "valid_operation_replacement
      circuit operation_node_id replacement_op
   \<longleftrightarrow> (\<exists>original_op.
        nodes circuit operation_node_id = Some (OperationNode original_op)
      \<and> operation_in_circuit circuit replacement_op
      \<and> op_qargs replacement_op = op_qargs original_op)"

lemma replace_operation_selected_node:
  (* If operation_node_id currently stores an operation node, then after
     replacement the same node ID stores the replacement operation. *)
  assumes operation_exists:
    "nodes circuit operation_node_id = Some (OperationNode original_op)"
  shows
    "nodes (replace_operation operation_node_id replacement_op circuit) operation_node_id
     = Some (OperationNode replacement_op)"

  using operation_exists
  unfolding replace_operation_def
  by simp

lemma valid_replacement_selected_node:
  (* Every valid replacement successfully installs the replacement
     operation at the selected node ID. *)
  assumes valid_replacement:
    "valid_operation_replacement
       circuit operation_node_id replacement_op"
  shows
    "nodes (replace_operation operation_node_id replacement_op circuit) operation_node_id 
     = Some (OperationNode replacement_op)"
  
  using
    replace_operation_selected_node
    valid_operation_replacement_def
    valid_replacement
  by auto

lemma replacement_preserves_other_nodes:
  (* Replacing the operation stored at operation_node_id does not change
     the node stored at any different node ID. *)
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"
  shows
    "nodes (replace_operation operation_node_id replacement_op circuit) other_node_id
     = nodes circuit other_node_id"

\<comment>\<open>operation_node_id can have 4 possible states
  1. None
  2. InputNode q
  3. OutputNode q
  4. OperationNode original_op

  For first three cases, replace_operation returns circuit
  For last case it calls
    insert_node
      operation_node_id
      (OperationNode replacement_op)
      circuit

  Since other_node_id \<noteq> operation_node_id, the lemma "nodes_insert_node_other" shows that other nodes are unchanged.
\<close>

proof (cases "nodes circuit operation_node_id")
  case None

  then show ?thesis
    unfolding replace_operation_def
    by simp

next
  case (Some selected_node)

  then show ?thesis
  proof (cases selected_node)
    case (InputNode q)

    then show ?thesis
      using Some
      unfolding replace_operation_def
      by simp

  next
    case (OutputNode q)

    then show ?thesis
      using Some
      unfolding replace_operation_def
      by simp

  next
    case (OperationNode original_op)

    then show ?thesis
      using Some different_node
      unfolding replace_operation_def
      by simp
  qed
qed

lemma replacement_preserves_edges:
  (* Replacing an operation does not modify the circuit's edge set. *)
  "edges (replace_operation operation_node_id replacement_op circuit) = edges circuit"

  unfolding
    replace_operation_def
    insert_node_def
  by (auto
      split: option.splits
      circuit_node.splits)

lemma replacement_preserves_num_qubits:
  (* Replacing an operation does not change the number of qubits. *)
  "num_qubits(replace_operation operation_node_id replacement_op circuit) = num_qubits circuit"

  unfolding
    replace_operation_def
    insert_node_def
  by (auto split: option.splits circuit_node.splits)

lemma replacement_preserves_next_id:
  (* Replacing an operation does not allocate or remove node IDs. *)
  "next_id (replace_operation operation_node_id replacement_op circuit) = next_id circuit"

  unfolding
    replace_operation_def
    insert_node_def

  by (auto
      split: option.splits
      circuit_node.splits)

lemma valid_replacement_preserves_node_wire_usage:
  (* A valid replacement preserves whether any node uses a given wire.

     The selected operation node continues to use exactly the same qubits
     because the replacement operation has the same op_qargs as the original
     operation. Every other node is unchanged.
  *)
  assumes valid_replacement:
    "valid_operation_replacement
       circuit operation_node_id replacement_op"
  shows
    "(case nodes (replace_operation operation_node_id replacement_op circuit) node_id of
        None \<Rightarrow> False
      | Some node \<Rightarrow> node_uses_qubit node q)
     =
     (case nodes circuit node_id of
        None \<Rightarrow> False
      | Some node \<Rightarrow> node_uses_qubit node q)"

  by (metis
      node_uses_qubit.simps(3)
      option.simps(5)
      replacement_preserves_other_nodes
      valid_operation_replacement_def
      valid_replacement
      valid_replacement_selected_node)

lemma replacement_preserves_well_formed_circuit:
  (* Replacing an operation with another valid operation using the same
     qubits preserves the circuit's well-formedness. *)
  assumes
    well_formed:
      "is_well_formed_circuit circuit"
  and
    valid_replacement:
      "valid_operation_replacement circuit operation_node_id replacement_op"
  shows
    "is_well_formed_circuit (replace_operation operation_node_id replacement_op circuit)"

  unfolding is_well_formed_circuit_def

proof (intro conjI)
  show well_formed_boundary:
    "are_well_formed_boundary_nodes (replace_operation operation_node_id replacement_op circuit)"

  proof -
    from valid_replacement obtain original_op where
      operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode original_op)"
      unfolding valid_operation_replacement_def
      by auto

    from well_formed have original_boundary:
      "are_well_formed_boundary_nodes circuit"
      unfolding is_well_formed_circuit_def
      by simp

    show ?thesis
      using
          are_well_formed_boundary_nodes_def
          circuit_node.distinct(3,5)
          operation_exists
          option.inject
          original_boundary
          replacement_preserves_num_qubits
          replacement_preserves_other_nodes
      unfolding are_well_formed_boundary_nodes_def
      by metis
  qed

next
  show well_formed_edges:
    "are_well_formed_edges (replace_operation operation_node_id replacement_op circuit)"

  proof -
    from well_formed have original_edges:
      "are_well_formed_edges circuit"
      unfolding is_well_formed_circuit_def
      by simp

    show ?thesis
      unfolding are_well_formed_edges_def

    proof (intro ballI)
      fix e
      assume updated_edge:
        "e \<in> edges (replace_operation operation_node_id replacement_op circuit)"

      have original_edge:
        "e \<in> edges circuit"
        using
          updated_edge
          replacement_preserves_edges
        by simp

      from original_edges original_edge
      have original_edge_well_formed:
        "is_well_formed_edge circuit e"
        unfolding are_well_formed_edges_def
        by simp

      show
        "is_well_formed_edge (replace_operation operation_node_id replacement_op circuit) e"

        unfolding is_well_formed_edge_def
      proof (intro conjI)
        from original_edge_well_formed
        have original_source_exists:
          "node_exists circuit (edge_source e)"
          unfolding is_well_formed_edge_def
          by simp

        show
          "node_exists (replace_operation operation_node_id replacement_op circuit) (edge_source e)"
          by (metis
              node_exists_def
              option.distinct(1)
              original_source_exists
              replacement_preserves_other_nodes
              valid_replacement
              valid_replacement_selected_node)

      next
        from original_edge_well_formed
        have original_target_exists:
          "node_exists circuit (edge_target e)"
          unfolding is_well_formed_edge_def
          by simp

        show
          "node_exists (replace_operation operation_node_id replacement_op circuit) (edge_target e)"

          by (metis
              node_exists_def
              option.distinct(1)
              original_target_exists
              replacement_preserves_other_nodes
              valid_replacement
              valid_replacement_selected_node)

      next
        from original_edge_well_formed
        have original_wire_exists:
          "qubit_in_circuit circuit (edge_wire e)"
          unfolding is_well_formed_edge_def
          by simp

        show
          "qubit_in_circuit  
             (replace_operation operation_node_id replacement_op circuit) (edge_wire e)"
          using
            original_wire_exists
            qubit_in_circuit_def
            replacement_preserves_num_qubits
          by simp
      
      next
        from original_edge_well_formed
        have original_source_uses_wire:
          "case nodes circuit (edge_source e) of
             None \<Rightarrow> False
           | Some source_node \<Rightarrow>
               node_uses_qubit source_node (edge_wire e)"
          unfolding is_well_formed_edge_def
          by simp

        have source_wire_usage_preserved:
          "(case
              nodes (replace_operation operation_node_id replacement_op circuit) (edge_source e) of
              None \<Rightarrow> False
            | Some source_node \<Rightarrow> node_uses_qubit source_node (edge_wire e))
           = (case nodes circuit (edge_source e) of
              None \<Rightarrow> False
            | Some source_node \<Rightarrow> node_uses_qubit source_node (edge_wire e))"
          using 
            valid_replacement
            valid_replacement_preserves_node_wire_usage
          by simp

        show
          "case nodes (replace_operation operation_node_id replacement_op circuit) (edge_source e) of
             None \<Rightarrow> False
           | Some source_node \<Rightarrow>
               node_uses_qubit source_node (edge_wire e)"
          using
            original_source_uses_wire
            source_wire_usage_preserved
          by simp

      next
        from original_edge_well_formed
        have original_target_uses_wire:
          "case nodes circuit (edge_target e) of
             None \<Rightarrow> False
           | Some target_node \<Rightarrow>
               node_uses_qubit target_node (edge_wire e)"
          unfolding is_well_formed_edge_def
          by simp

        have target_wire_usage_preserved:
          "(case nodes (replace_operation operation_node_id replacement_op circuit) (edge_target e) of
              None \<Rightarrow> False
            | Some target_node \<Rightarrow> node_uses_qubit target_node (edge_wire e))
           = (case nodes circuit (edge_target e) of
              None \<Rightarrow> False
            | Some target_node \<Rightarrow>
                node_uses_qubit target_node (edge_wire e))"
          using
            valid_replacement
            valid_replacement_preserves_node_wire_usage
          by simp

        show
          "case nodes (replace_operation operation_node_id replacement_op circuit) (edge_target e) of
             None \<Rightarrow> False
           | Some target_node \<Rightarrow> node_uses_qubit target_node (edge_wire e)"
          using
            original_target_uses_wire
            target_wire_usage_preserved
          by simp
      qed
    qed
  qed

next
  show well_formed_op_nodes:
    "are_well_formed_operation_nodes (replace_operation operation_node_id replacement_op circuit)"
    proof -      
      from well_formed have original_operation_nodes:
        "are_well_formed_operation_nodes circuit"
        unfolding is_well_formed_circuit_def
        by simp

    from valid_replacement obtain original_op where
      operation_exists:
        "nodes circuit operation_node_id = Some (OperationNode original_op)"
    and
      replacement_in_circuit:
        "operation_in_circuit circuit replacement_op"

      unfolding valid_operation_replacement_def
      by blast

    show ?thesis
      by (metis
          are_well_formed_operation_nodes_def
          circuit_node.inject(3)
          operation_in_circuit_def
          option.sel
          original_operation_nodes
          qubit_in_circuit_def
          replacement_in_circuit
          replacement_preserves_num_qubits
          replacement_preserves_other_nodes
          valid_replacement
          valid_replacement_selected_node)
  qed
qed

lemma replacement_preserves_acyclicity:
  (* Replacing an operation payload leaves the graph relation unchanged.
     Therefore, every directed path and every possible directed cycle is
     unchanged, and acyclicity is preserved. *)

  assumes acyclic:
    "is_acyclic_circuit circuit"

  shows
   "is_acyclic_circuit (replace_operation operation_node_id replacement_op circuit)"

  using
    assms
    replacement_preserves_edges
  unfolding
    is_acyclic_circuit_def
    edge_relation_def
  by simp

lemma replacement_preserves_wire_edge_relation:
  (* Replacing an operation does not change any wire-specific edge relation because the circuit's edge set is unchanged. *)
  "wire_edge_relation (replace_operation operation_node_id replacement_op circuit) q
   = wire_edge_relation circuit q"

  unfolding wire_edge_relation_def
  using replacement_preserves_edges
  by simp

lemma replacement_preserves_wire_reaches:
  (* Since the wire edge relation is unchanged, reachability along every wire is unchanged. *)
  "wire_reaches (replace_operation operation_node_id replacement_op circuit) q node_a node_b
   \<longleftrightarrow> wire_reaches circuit q node_a node_b"

  unfolding wire_reaches_def
  using replacement_preserves_wire_edge_relation
  by simp

lemma replacement_preserves_unique_wire_predecessor:
  "has_unique_wire_predecessor (replace_operation operation_node_id replacement_op circuit) q node_id
   \<longleftrightarrow> has_unique_wire_predecessor circuit q node_id"

  unfolding has_unique_wire_predecessor_def
  using replacement_preserves_wire_edge_relation
  by simp

lemma replacement_preserves_unique_wire_successor:
  "has_unique_wire_successor (replace_operation operation_node_id replacement_op circuit) q node_id
   \<longleftrightarrow> has_unique_wire_successor circuit q node_id"

  unfolding has_unique_wire_successor_def
  using replacement_preserves_wire_edge_relation
  by simp

lemma valid_replacement_preserves_nodes_comparable_on_wire:
  (* A valid replacement preserves the set of nodes using each wire and
     leaves wire reachability unchanged. Therefore, comparability of all
     nodes on a wire is preserved. *)
  assumes
    valid_replacement:
      "valid_operation_replacement circuit operation_node_id replacement_op"
  and
    original_comparable:
      "nodes_comparable_on_wire circuit q"
  shows
    "nodes_comparable_on_wire (replace_operation operation_node_id replacement_op circuit) q"

  unfolding nodes_comparable_on_wire_def

proof (intro allI impI)
  fix node_a node_b node_a_value node_b_value

  assume updated_node_a:
    "nodes (replace_operation operation_node_id replacement_op circuit) node_a = Some node_a_value"

  assume updated_node_b:
    "nodes (replace_operation operation_node_id replacement_op circuit) node_b = Some node_b_value"

  assume updated_node_a_uses_q:
    "node_uses_qubit node_a_value q"

  assume updated_node_b_uses_q:
    "node_uses_qubit node_b_value q"

  have original_node_a_uses_q:
    "case nodes circuit node_a of
       None \<Rightarrow> False
     | Some node \<Rightarrow> node_uses_qubit node q"
    by (metis
        option.simps(5)
        updated_node_a
        updated_node_a_uses_q
        valid_replacement
        valid_replacement_preserves_node_wire_usage)

  then obtain original_node_a_value where
    original_node_a:
      "nodes circuit node_a = Some original_node_a_value"
  and
    original_node_a_value_uses_q:
      "node_uses_qubit original_node_a_value q"
    by (cases "nodes circuit node_a") auto

  have original_node_b_uses_q:
    "case nodes circuit node_b of
       None \<Rightarrow> False
     | Some node \<Rightarrow> node_uses_qubit node q"
    using
      updated_node_b
      updated_node_b_uses_q
      valid_replacement
      valid_replacement_preserves_node_wire_usage
    by fastforce

  then obtain original_node_b_value where
    original_node_b:
      "nodes circuit node_b = Some original_node_b_value"
  and
    original_node_b_value_uses_q:
      "node_uses_qubit original_node_b_value q"
    by (cases "nodes circuit node_b") auto

  from original_comparable
  have original_order:
    "node_a = node_b
     \<or> wire_reaches circuit q node_a node_b
     \<or> wire_reaches circuit q node_b node_a"
    unfolding nodes_comparable_on_wire_def
    using
      original_node_a
      original_node_b
      original_node_a_value_uses_q
      original_node_b_value_uses_q
    by simp

  show
    "node_a = node_b
     \<or> wire_reaches (replace_operation operation_node_id replacement_op circuit) q node_a node_b
     \<or> wire_reaches (replace_operation operation_node_id replacement_op circuit) q node_b node_a"
    using
      original_order
      replacement_preserves_wire_reaches
    by simp
qed

lemma replacement_preserves_wire_linearity:
  (* A valid replacement preserves the qubit interface of the selected
     operation and leaves all edges unchanged. Consequently, the nodes
     using each wire, their predecessor and successor relationships, and
     their reachability order remain unchanged. Every linear wire
     therefore remains linear. *)
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    valid_replacement:
      "valid_operation_replacement circuit operation_node_id replacement_op"
  shows
    "all_wires_linear (replace_operation operation_node_id replacement_op circuit)"

proof -
  from valid_circuit have original_all_wires_linear:
    "all_wires_linear circuit"
    unfolding is_valid_circuit_def
    by simp

  show ?thesis
    unfolding all_wires_linear_def
  
  proof (intro allI impI)
    fix q

    assume updated_qubit:
      "qubit_in_circuit (replace_operation operation_node_id replacement_op circuit) q"

    have original_qubit:
      "qubit_in_circuit circuit q"
      using
        updated_qubit
        replacement_preserves_num_qubits
      unfolding qubit_in_circuit_def
      by simp

    from
      original_all_wires_linear
      original_qubit

    have original_wire_linear:
      "wire_is_linear circuit q"
      unfolding all_wires_linear_def
      by simp

    from original_wire_linear have original_comparable:
      "nodes_comparable_on_wire circuit q"
      unfolding wire_is_linear_def
      by simp

    have updated_comparable:
      "nodes_comparable_on_wire (replace_operation operation_node_id replacement_op circuit) q"
      using
        valid_replacement
        original_comparable
      by (rule valid_replacement_preserves_nodes_comparable_on_wire)
    
    show "wire_is_linear (replace_operation operation_node_id replacement_op circuit) q"
      unfolding wire_is_linear_def

    proof (intro conjI)
      show
          "nodes_comparable_on_wire (replace_operation operation_node_id replacement_op circuit) q"
        using updated_comparable .
    next
      from original_wire_linear have original_input_has_no_predecessor:
        "\<nexists>predecessor_id. (predecessor_id, get_input_node_id q) \<in> wire_edge_relation circuit q"
        unfolding wire_is_linear_def
        by simp

      show
        "\<nexists>predecessor_id. 
           (predecessor_id, get_input_node_id q)
             \<in> wire_edge_relation (replace_operation operation_node_id replacement_op circuit) q"
        using
          original_input_has_no_predecessor
          replacement_preserves_wire_edge_relation
        by simp

    next
      from original_wire_linear
      have original_input_has_unique_successor:
        "has_unique_wire_successor
           circuit q (get_input_node_id q)"
        unfolding wire_is_linear_def
        by simp

      show
        "has_unique_wire_successor (replace_operation operation_node_id replacement_op
              circuit)
           q
           (get_input_node_id q)"
        using
          original_input_has_unique_successor
          replacement_preserves_unique_wire_successor
        by simp

    next
      from original_wire_linear
      have original_output_has_unique_predecessor:
        "has_unique_wire_predecessor circuit q (get_output_node_id q)"
        unfolding wire_is_linear_def
        by simp

      show
        "has_unique_wire_predecessor
          (replace_operation operation_node_id replacement_op circuit) q (get_output_node_id q)"
        using
          original_output_has_unique_predecessor
          replacement_preserves_unique_wire_predecessor
        by simp

    next
      from original_wire_linear
      have original_output_has_no_successor:
        "\<nexists>successor_id. (get_output_node_id q, successor_id) \<in> wire_edge_relation circuit q"
        unfolding wire_is_linear_def
        by simp

      show
        "\<nexists>successor_id. (get_output_node_id q, successor_id)
         \<in> wire_edge_relation (replace_operation operation_node_id replacement_op circuit) q"
        using
          original_output_has_no_successor
          replacement_preserves_wire_edge_relation
        by simp

    next
      show
        "\<forall>node_id op. nodes (replace_operation operation_node_id replacement_op circuit) node_id = Some (OperationNode op)
           \<longrightarrow> node_uses_qubit (OperationNode op) q
           \<longrightarrow> has_unique_wire_predecessor (replace_operation operation_node_id replacement_op circuit) q node_id
           \<and> has_unique_wire_successor (replace_operation operation_node_id replacement_op circuit) q node_id"

      proof (intro allI impI)
        fix node_id op

        assume updated_operation_node:
          "nodes (replace_operation operation_node_id replacement_op circuit) node_id = Some (OperationNode op)"

        assume updated_operation_uses_q:
          "node_uses_qubit (OperationNode op) q"

        have original_node_uses_q:
          "case nodes circuit node_id of
             None \<Rightarrow> False
           | Some node \<Rightarrow> node_uses_qubit node q"
          by (metis
              option.simps(5)
              updated_operation_node
              updated_operation_uses_q
              valid_replacement
              valid_replacement_preserves_node_wire_usage)

        then obtain original_node where
          original_node:
            "nodes circuit node_id = Some original_node"
          and original_node_uses_q:
            "node_uses_qubit original_node q"
          by (cases "nodes circuit node_id") auto

        have original_node_is_operation:
          "\<exists>original_op. original_node = OperationNode original_op"
          by (metis
              option.inject
              original_node
              replacement_preserves_other_nodes
              updated_operation_node
              valid_operation_replacement_def
              valid_replacement)

        then obtain original_op where
          original_node_value:
            "original_node = OperationNode original_op"
          by auto

        have original_operation_node:
          "nodes circuit node_id = Some (OperationNode original_op)"
          using original_node original_node_value
          by simp

        have original_operation_uses_q:
          "node_uses_qubit (OperationNode original_op) q"
          using original_node_uses_q original_node_value
          by simp

        from original_wire_linear
        have original_operation_linear:
          "has_unique_wire_predecessor circuit q node_id
           \<and> has_unique_wire_successor circuit q node_id"
          unfolding wire_is_linear_def
          using
            original_operation_node
            original_operation_uses_q
          by simp

        show
          "has_unique_wire_predecessor (replace_operation operation_node_id replacement_op circuit) q node_id
         \<and> has_unique_wire_successor (replace_operation operation_node_id replacement_op circuit) q node_id"
          using
            original_operation_linear
            replacement_preserves_unique_wire_predecessor
            replacement_preserves_unique_wire_successor
          by simp
      qed
    qed
  qed
qed

section \<open>Subcircuit Replacement\<close>

record subcircuit =
  subgraph :: quantum_circuit
    (* The circuit fragment that will replace an operation node. *)

  input_interface :: "qubit \<Rightarrow> node_id option"
    (* For each wire entering the subcircuit, gives the corresponding
       entry node inside the fragment. Wires not used by the fragment
       map to None. *)

  output_interface :: "qubit \<Rightarrow> node_id option"

definition subcircuit_uses_qubit ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> bool"
  where
    (* Returns true iff the given qubit is part of the subcircuit
       interface (that is, the subcircuit has both an entry and exit
       point on this wire). *)
    "subcircuit_uses_qubit subcircuit q \<longleftrightarrow>
        input_interface subcircuit q \<noteq> None
     \<or> output_interface subcircuit q \<noteq> None"

definition subcircuit_interface_qubits ::
  "subcircuit \<Rightarrow> qubit set"
  where
    (* Returns the set of all qubits exposed by the subcircuit interface.
  
       Since a valid subcircuit must provide both an input and an output
       interface node for every used qubit, checking the input interface
       is sufficient once validity has been established.
    *)
    "subcircuit_interface_qubits subcircuit =
       {q. input_interface subcircuit q \<noteq> None}"

definition interface_node_uses_qubit ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    (* Checks whether the given interface node exists inside the
       subcircuit graph and lies on the indicated qubit wire. *)
    "interface_node_uses_qubit subcircuit q node_id \<longleftrightarrow>
       (\<exists>node.
          nodes (subgraph subcircuit) node_id = Some node
        \<and> node_uses_qubit node q)"

definition is_input_interface_node ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    (* Checks whether node_id is the declared input interface node for
       wire q and whether it is a genuine node on that wire inside the
       subcircuit graph. *)
    "is_input_interface_node subcircuit q node_id \<longleftrightarrow>
         input_interface subcircuit q = Some node_id
       \<and> interface_node_uses_qubit subcircuit q node_id"

definition is_output_interface_node ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    (* Checks whether node_id is the declared output interface node for
       wire q and whether it is a genuine node on that wire inside the
       subcircuit graph. *)
    "is_output_interface_node subcircuit q node_id \<longleftrightarrow>
         output_interface subcircuit q = Some node_id
       \<and> interface_node_uses_qubit subcircuit q node_id"

definition is_first_operation_on_subcircuit_wire ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    (* Checks whether node_id contains an operation and is the first
       operation node encountered after the canonical input boundary
       node on wire q. *)
    "is_first_operation_on_subcircuit_wire subcircuit q node_id \<longleftrightarrow>
         (\<exists>op. nodes (subgraph subcircuit) node_id = Some (OperationNode op))
       \<and> (get_input_node_id q, node_id) \<in> wire_edge_relation (subgraph subcircuit) q"

definition is_last_operation_on_subcircuit_wire ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    (* Checks whether node_id contains an operation and is the final
       operation node encountered before the canonical output boundary
       node on wire q. *)
    "is_last_operation_on_subcircuit_wire subcircuit q node_id \<longleftrightarrow>
         (\<exists>op. nodes (subgraph subcircuit) node_id = Some (OperationNode op))
       \<and> (node_id, get_output_node_id q) \<in> wire_edge_relation (subgraph subcircuit) q"

definition subcircuit_operation_qubits ::
  "subcircuit \<Rightarrow> qubit set"
  where
    (* Returns all qubits used by operation nodes inside the replacement
       fragment. Boundary nodes do not contribute to this set. *)
    "subcircuit_operation_qubits subcircuit =
       {q. \<exists>node_id op. nodes (subgraph subcircuit) node_id = Some (OperationNode op)
           \<and> q \<in> set (op_qargs op)}"

definition is_valid_subcircuit ::
  "subcircuit \<Rightarrow> bool"
  where
    (* A subcircuit is valid iff
        1. Its underlying graph is a valid circuit
        2. A qubit has an input interface iff it has an output interface
        3. Every declared input interface node is the first operation
           node on its corresponding wire
        4. Every declared output interface node is the last operation
           node on its corresponding wire
        5. The interface exposes exactly the qubits used by operation
           nodes in the fragment
        6. On every exposed wire, the input interface node can reach the
           output interface node inside the fragment
    *)
    "is_valid_subcircuit subcircuit \<longleftrightarrow>
         is_valid_circuit (subgraph subcircuit)
  
       \<and> (\<forall>q. (input_interface subcircuit q = None) = (output_interface subcircuit q = None))
       \<and> (\<forall>q input_node_id. input_interface subcircuit q = Some input_node_id
         \<longrightarrow> is_first_operation_on_subcircuit_wire subcircuit q input_node_id)
        
       \<and> (\<forall>q output_node_id. output_interface subcircuit q = Some output_node_id
             \<longrightarrow> is_last_operation_on_subcircuit_wire subcircuit q output_node_id)

       \<and> subcircuit_interface_qubits subcircuit = subcircuit_operation_qubits subcircuit
  
       \<and> (\<forall>q input_node_id output_node_id. input_interface subcircuit q = Some input_node_id
            \<longrightarrow> output_interface subcircuit q = Some output_node_id
            \<longrightarrow> (input_node_id, output_node_id) \<in> (wire_edge_relation (subgraph subcircuit) q)\<^sup>*)"

definition is_compatible_subcircuit ::
  "qubit list \<Rightarrow> subcircuit \<Rightarrow> bool"
where
  (* A subcircuit is compatible with a list of operation qubits iff
      1. The qubit list contains no duplicates
      2. The subcircuit exposes exactly those qubits and no others
      3. Every required qubit has both an input and output interface

     Exact interface equality prevents the replacement fragment from
     unexpectedly introducing dependencies on additional circuit wires.
  *)
  "is_compatible_subcircuit qubits subcircuit \<longleftrightarrow>
       distinct qubits
     \<and> subcircuit_interface_qubits subcircuit = set qubits
     \<and> (\<forall>q \<in> set qubits.
          input_interface subcircuit q \<noteq> None
        \<and> output_interface subcircuit q \<noteq> None)"

definition is_valid_subcircuit_replacement ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> bool"
  where
    (* Checks whether the supplied subcircuit may structurally replace
       the operation stored at operation_node_id.
  
       A replacement is valid iff
        1. The selected node contains an operation
        2. The replacement subcircuit is valid
        3. The host circuit and subcircuit use the same qubit universe
        4. The subcircuit exposes exactly the qubits used by the removed
           operation
    *)
    "is_valid_subcircuit_replacement 
        circuit operation_node_id subcircuit
     \<longleftrightarrow> (\<exists>op. nodes circuit operation_node_id = Some (OperationNode op)
        \<and> is_valid_subcircuit subcircuit
        \<and> num_qubits (subgraph subcircuit) = num_qubits circuit
        \<and> is_compatible_subcircuit (op_qargs op) subcircuit)"

definition operation_node_ids ::
  "quantum_circuit \<Rightarrow> node_id set"
  where
    (* Returns exactly the node IDs that store operation nodes.
       This definition depends only on the graph contents and not on a
       separate next_id allocation invariant. *)
    "operation_node_ids circuit = {node_id. \<exists>op. nodes circuit node_id = Some (OperationNode op)}"

definition subcircuit_operation_node_ids ::
  "subcircuit \<Rightarrow> node_id set"
  where
    (* Returns the operation nodes belonging to the replacement fragment.
       These are the nodes that will be copied into the host circuit. *)
    "subcircuit_operation_node_ids subcircuit = operation_node_ids (subgraph subcircuit)"

definition subcircuit_internal_edges ::
  "subcircuit \<Rightarrow> edge set"
  where
    (* Returns the edges whose source and target are both operation nodes
       belonging to the replacement fragment.
  
       Edges connected to the fragment's canonical boundary nodes are
       excluded because the surrounding host circuit supplies the actual
       predecessors and successors after replacement.
    *)
    "subcircuit_internal_edges subcircuit =
       {e \<in> edges (subgraph subcircuit). 
          edge_source e \<in> subcircuit_operation_node_ids subcircuit
        \<and> edge_target e \<in> subcircuit_operation_node_ids subcircuit}"

definition rename_subcircuit_node_id ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> node_id"
  where
    (* Renames a subcircuit-local node ID into a fresh host-circuit ID.
  
       Every renamed ID begins at or above next_id of the host circuit,
       so it cannot collide with any existing host node when the host
       satisfies its node-allocation invariant.
    *)
    "rename_subcircuit_node_id circuit local_node_id = 
       NodeId (node_id_to_nat (next_id circuit) + node_id_to_nat local_node_id)"

definition rename_subcircuit_edge ::
  "quantum_circuit \<Rightarrow> edge \<Rightarrow> edge"
where
  (* Renames both endpoints of a subcircuit edge while preserving its
     wire label. *)
  "rename_subcircuit_edge circuit e =
     make_edge 
       (rename_subcircuit_node_id circuit (edge_source e))
       (rename_subcircuit_node_id circuit (edge_target e))
       (edge_wire e)"

definition renamed_subcircuit_internal_edges ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> edge set"
where
  (* Returns the internal edge set of the replacement fragment after
     translating every local node ID into the fresh host namespace. *)
  "renamed_subcircuit_internal_edges circuit subcircuit = 
     rename_subcircuit_edge circuit ` subcircuit_internal_edges subcircuit"

definition renamed_input_interface ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> node_id option"
  where
    (* Returns the fresh host-circuit ID corresponding to the
       subcircuit's input interface node on wire q. *)
    "renamed_input_interface circuit subcircuit q = 
       map_option (rename_subcircuit_node_id circuit) (input_interface subcircuit q)"

definition renamed_output_interface ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> node_id option"
  where
    (* Returns the fresh host-circuit ID corresponding to the
       subcircuit's output interface node on wire q. *)
    "renamed_output_interface circuit subcircuit q =
       map_option
         (rename_subcircuit_node_id circuit)
         (output_interface subcircuit q)"

lemma rename_subcircuit_node_id_injective:
  (* Renaming subcircuit-local node IDs is injective.

     Every local node ID is renamed by adding the same host-circuit
     offset, namely next_id circuit. Therefore, two renamed node IDs
     can be equal only when their original local node IDs were equal.
  *)
  assumes renamed_equal:
    "rename_subcircuit_node_id circuit node_id1 =
     rename_subcircuit_node_id circuit node_id2"
  shows
    "node_id1 = node_id2"

  using renamed_equal
  unfolding rename_subcircuit_node_id_def
  by (cases node_id1; cases node_id2; simp)

lemma renamed_subcircuit_node_id_is_unused:
  (* Every renamed subcircuit node ID is unused in the host circuit.

     The renaming function places each local node ID at or above
     next_id circuit. Under the assumption that every node ID at or
     above next_id is unallocated, the renamed node must map to None
     in the host circuit.
  *)
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id \<ge> node_id_to_nat (next_id circuit) \<Longrightarrow> nodes circuit node_id = None"
  shows
    "nodes circuit (rename_subcircuit_node_id circuit local_node_id) = None"

proof (rule unused_above_next_id)
  show
    "node_id_to_nat (rename_subcircuit_node_id circuit local_node_id) \<ge> node_id_to_nat (next_id circuit)"

    unfolding rename_subcircuit_node_id_def
    by simp
qed

lemma rename_subcircuit_edge_preserves_wire:
  (* Renaming an edge changes only its source and target node IDs.

     The wire label is copied directly from the original edge, so the
     renamed edge remains on the same qubit wire.
  *)
  "edge_wire (rename_subcircuit_edge circuit e) = edge_wire e"

  unfolding rename_subcircuit_edge_def
  unfolding make_edge_def
  by simp

lemma rename_subcircuit_edge_preserves_distinct_endpoints:
  (* If the source and target of an edge are distinct before renaming,
     then they remain distinct after renaming.

     This follows because rename_subcircuit_node_id is injective:
     equality between the renamed endpoints would imply equality
     between the original endpoints.
  *)
  assumes distinct_endpoints:
    "edge_source e \<noteq> edge_target e"

  shows
    "edge_source (rename_subcircuit_edge circuit e) \<noteq> edge_target (rename_subcircuit_edge circuit e)"

proof
  assume renamed_endpoints_equal:
    "edge_source (rename_subcircuit_edge circuit e) =
     edge_target (rename_subcircuit_edge circuit e)"

  have renamed_node_ids_equal:
    "rename_subcircuit_node_id circuit (edge_source e) =
     rename_subcircuit_node_id circuit (edge_target e)"

    using renamed_endpoints_equal
    unfolding rename_subcircuit_edge_def
    unfolding make_edge_def
    by simp

  have original_endpoints_equal:
    "edge_source e = edge_target e"

    using renamed_node_ids_equal
    by (rule rename_subcircuit_node_id_injective)

  show False
    using distinct_endpoints original_endpoints_equal
    by contradiction
qed

lemma renamed_subcircuit_internal_edge:
  (* Every internal edge of the original subcircuit belongs to the set
     of renamed internal edges after applying the edge-renaming
     function.

     This follows directly from the definition of the renamed edge set
     as the image of subcircuit_internal_edges.
  *)
  assumes internal_edge:
    "e \<in> subcircuit_internal_edges subcircuit"

  shows
    "rename_subcircuit_edge circuit e \<in> renamed_subcircuit_internal_edges circuit subcircuit"

  using internal_edge
  unfolding renamed_subcircuit_internal_edges_def
  by simp

lemma renamed_input_interface_node_is_unused:
  (* If a renamed input interface contains node_id, then node_id is
     unused in the host circuit.

     The renamed interface is obtained by applying the fresh node-ID
     renaming function to the original interface node. Therefore, the
     general unused-renamed-node theorem applies.
  *)
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id \<ge> node_id_to_nat (next_id circuit) \<Longrightarrow> nodes circuit node_id = None"

  and renamed_interface:
    "renamed_input_interface circuit subcircuit q = Some renamed_node_id"

  shows
    "nodes circuit renamed_node_id = None"
  using
    renamed_input_interface_def
    renamed_interface
    renamed_subcircuit_node_id_is_unused
    unused_above_next_id
  by auto

lemma renamed_output_interface_node_is_unused:
  (* If a renamed output interface contains node_id, then node_id is
     unused in the host circuit.

     As with the input interface, the output interface node is mapped
     through rename_subcircuit_node_id and is therefore placed at or
     above next_id of the host circuit.
  *)
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id \<ge> node_id_to_nat (next_id circuit) \<Longrightarrow> nodes circuit node_id = None"

  and renamed_interface:
    "renamed_output_interface circuit subcircuit q = Some renamed_node_id"

  shows
    "nodes circuit renamed_node_id = None"
  using
    renamed_interface
    renamed_output_interface_def
    renamed_subcircuit_node_id_is_unused
    unused_above_next_id
  by auto

lemma renamed_subcircuit_edge_source:
  (* The source of a renamed edge is the renamed form of its original
     source node ID. *)
  "edge_source (rename_subcircuit_edge circuit e) =
     rename_subcircuit_node_id circuit (edge_source e)"

  unfolding rename_subcircuit_edge_def
  unfolding make_edge_def
  by simp

lemma renamed_subcircuit_edge_target:
  (* The target of a renamed edge is the renamed form of its original
     target node ID. *)
  "edge_target (rename_subcircuit_edge circuit e) =
     rename_subcircuit_node_id circuit (edge_target e)"

  unfolding rename_subcircuit_edge_def
  unfolding make_edge_def
  by simp

definition remove_operation_node ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> quantum_circuit"
  where
    (* Removes one node from the circuit without reconnecting its wires.
  
       The transformation:
         1. changes the selected node-table entry to None; and
         2. removes every edge whose source or target is the selected node.
  
       All unrelated nodes and edges remain unchanged. The circuit's
       qubit count and next_id are also preserved.
  
       This helper deliberately does not reconnect the surrounding wires.
       Later subcircuit-replacement stages connect the original
       predecessors to the replacement input interface and connect the
       replacement output interface to the original successors.
    *)
    "remove_operation_node circuit operation_node_id =
       circuit
         \<lparr>
           nodes := (nodes circuit) (operation_node_id := None),
  
           edges := 
             {e \<in> edges circuit.
                edge_source e \<noteq> operation_node_id
              \<and> edge_target e \<noteq> operation_node_id}
         \<rparr>"

lemma remove_operation_node_selected[simp]:
  (* Looking up the removed node ID after removal returns None. *)
  "nodes (remove_operation_node circuit operation_node_id) operation_node_id = None"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_other[simp]:
  (* Removing one node does not alter the node-table entry stored at
     any different node ID. *)
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  shows
    "nodes (remove_operation_node circuit operation_node_id) other_node_id = nodes circuit other_node_id"

  using different_node
  unfolding remove_operation_node_def
  by simp

lemma edges_remove_operation_node[simp]:
  (* The resulting edge set contains exactly the original edges that
     are not incident on the removed node. *)
  "edges (remove_operation_node circuit operation_node_id) 
   = {e \<in> edges circuit.
      edge_source e \<noteq> operation_node_id
    \<and> edge_target e \<noteq> operation_node_id}"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_has_no_outgoing_edge:
  (* After removal, no remaining edge has the removed node as its
     source. *)
  assumes edge_remains:
    "e \<in> edges (remove_operation_node circuit operation_node_id)"

  shows
    "edge_source e \<noteq> operation_node_id"

  using edge_remains
  by simp

lemma remove_operation_node_has_no_incoming_edge:
  (* After removal, no remaining edge has the removed node as its
     target. *)
  assumes edge_remains:
    "e \<in> edges (remove_operation_node circuit operation_node_id)"

  shows
    "edge_target e \<noteq> operation_node_id"

  using edge_remains
  by simp

lemma remove_operation_node_preserves_unrelated_edge:
  (* An original edge remains after node removal when neither endpoint
     is the removed node. *)
  assumes edge_exists:
    "e \<in> edges circuit"

  assumes source_different:
    "edge_source e \<noteq> operation_node_id"

  assumes target_different:
    "edge_target e \<noteq> operation_node_id"

  shows
    "e \<in> edges (remove_operation_node circuit operation_node_id)"

  using
    edge_exists
    source_different
    target_different
  by simp

lemma remove_operation_node_preserves_num_qubits[simp]:
  (* Removing a node does not change the circuit's qubit count. *)
  "num_qubits (remove_operation_node circuit operation_node_id) = num_qubits circuit"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_preserves_next_id[simp]:
  (* Removing a node does not allocate any IDs, so next_id remains
     unchanged. *)
  "next_id (remove_operation_node circuit operation_node_id) = next_id circuit"

  unfolding remove_operation_node_def
  by simp

definition insert_subcircuit_nodes ::
  "quantum_circuit \<Rightarrow> quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> quantum_circuit"
where
  (* Copies every operation node from the replacement subcircuit into
     the current host circuit.

     original_circuit fixes the renaming namespace. In particular,
     next_id original_circuit is used as the offset for every copied
     node throughout the complete replacement transformation.

     current_circuit is the circuit currently being transformed. It may
     already have had the original operation node and its incident edges
     removed.

     Only operation nodes are copied. The canonical input and output
     boundary nodes of the subcircuit are not copied because the host
     circuit already provides its own boundary nodes.

     A local node with numeric ID i is stored at

         next_id original_circuit + i.

     After copying, next_id is advanced beyond the complete local node
     namespace of the subcircuit. The edge set and qubit count are left
     unchanged.
  *)
  "insert_subcircuit_nodes original_circuit current_circuit replacement
   = current_circuit
       \<lparr>
         nodes :=
           (\<lambda>host_node_id.
              let
                renaming_offset = node_id_to_nat (next_id original_circuit);
                host_node_number = node_id_to_nat host_node_id;
                local_node_id = NodeId (host_node_number - renaming_offset)
              in
                if renaming_offset \<le> host_node_number
                   \<and> local_node_id \<in> subcircuit_operation_node_ids replacement
                then
                  nodes (subgraph replacement) local_node_id
                else nodes current_circuit host_node_id)
       \<rparr>"

lemma insert_subcircuit_nodes_node_cases:
  assumes inserted_node:
    "nodes (insert_subcircuit_nodes original_circuit circuit replacement) node_id = Some node"
  shows
    "nodes circuit node_id = Some node
     \<or>
     (\<exists>local_node_id.
        local_node_id \<in> subcircuit_operation_node_ids replacement
        \<and> node_id = rename_subcircuit_node_id original_circuit local_node_id
        \<and> nodes (subgraph replacement) local_node_id = Some node)"

proof -
  obtain host_node_number where node_id_eq:
    "node_id = NodeId host_node_number"
    by (cases node_id) simp

  obtain renaming_offset where next_id_eq:
    "next_id original_circuit = NodeId renaming_offset"
    by (cases "next_id original_circuit") simp

  let ?local_node_id =
    "NodeId (host_node_number - renaming_offset)"

  from inserted_node have inserted_node_cases:
    "(if renaming_offset \<le> host_node_number
         \<and> ?local_node_id \<in> subcircuit_operation_node_ids replacement
      then
        nodes (subgraph replacement) ?local_node_id
      else
        nodes circuit node_id)
     = Some node"
    unfolding
      insert_subcircuit_nodes_def
      node_id_eq
      next_id_eq
    by auto

  show ?thesis
    by (metis
        inserted_node_cases
        next_id_eq
        node_id_eq
        node_id_to_nat.simps
        ordered_cancel_comm_monoid_diff_class.add_diff_inverse
        rename_subcircuit_node_id_def)
qed

lemma insert_subcircuit_nodes_copies_operation_node:
  (* Every local operation node appears at its renamed host-circuit ID
     after insertion. *)
  assumes local_operation_node:
    "local_node_id \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes (insert_subcircuit_nodes original_circuit current_circuit replacement)
       (rename_subcircuit_node_id original_circuit local_node_id)
     = nodes (subgraph replacement) local_node_id"

  using local_operation_node
  unfolding
    insert_subcircuit_nodes_def
    rename_subcircuit_node_id_def
  by (cases local_node_id;
      cases "next_id original_circuit";
      simp)

lemma insert_subcircuit_nodes_copies_operation:
  (* If a local subcircuit node stores OperationNode op, then its
     renamed host ID stores the same operation after insertion. *)
  assumes local_operation:
    "nodes (subgraph replacement) local_node_id = Some (OperationNode op)"

  assumes allocated_local_node:
    "local_node_id \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes (insert_subcircuit_nodes original_circuit current_circuit replacement)
       (rename_subcircuit_node_id original_circuit local_node_id)
     = Some (OperationNode op)"

  using
    insert_subcircuit_nodes_copies_operation_node[
      OF allocated_local_node,
      of original_circuit current_circuit]
    local_operation
  by simp

lemma insert_subcircuit_nodes_preserves_node_below_next_id:
  (* Node-table entries below the original next_id cannot belong to the
     renamed subcircuit namespace and therefore remain unchanged. *)
  assumes existing_namespace:
    "node_id_to_nat node_id < node_id_to_nat (next_id original_circuit)"

  shows
    "nodes (insert_subcircuit_nodes original_circuit current_circuit replacement) node_id
     = nodes current_circuit node_id"

  using existing_namespace
  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_edges[simp]:
  (* Copying nodes does not yet insert any subcircuit edges. *)
  "edges (insert_subcircuit_nodes original_circuit current_circuit replacement) = edges current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_num_qubits[simp]:
  (* Copying replacement nodes does not change the host's qubit
     universe. *)
  "num_qubits (insert_subcircuit_nodes original_circuit current_circuit replacement) = num_qubits current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_next_id[simp]:
  (* Copying the replacement nodes does not yet advance the host
     circuit's allocation boundary. The complete replacement
     transformation will update next_id once all nodes and edges have
     been installed. *)
  "next_id (insert_subcircuit_nodes original_circuit current_circuit replacement) = next_id current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

definition insert_subcircuit_internal_edges ::
  "quantum_circuit \<Rightarrow> quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> quantum_circuit"
where
  (* Inserts all internal edges of the replacement subcircuit into the
     current host circuit.

     original_circuit fixes the renaming offset through its next_id.
     current_circuit is the intermediate circuit being transformed.

     Only edges whose source and target are both operation nodes of the
     replacement are inserted here. Connections between the host
     circuit and the replacement interfaces are added by later helpers.
  *)
  "insert_subcircuit_internal_edges original_circuit current_circuit replacement =
     current_circuit
       \<lparr>
         edges :=
           edges current_circuit 
           \<union> renamed_subcircuit_internal_edges original_circuit replacement
       \<rparr>"

lemma edges_insert_subcircuit_internal_edges[simp]:
  "edges (insert_subcircuit_internal_edges original_circuit current_circuit replacement)
   = edges current_circuit \<union> renamed_subcircuit_internal_edges original_circuit replacement"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_existing_edge:
  assumes existing_edge:
    "e \<in> edges current_circuit"

  shows
    "e \<in> edges (insert_subcircuit_internal_edges original_circuit current_circuit replacement)"

  using existing_edge
  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_contains_renamed_edge:
  assumes renamed_edge:
    "e \<in> renamed_subcircuit_internal_edges original_circuit replacement"

  shows
    "e \<in> edges (insert_subcircuit_internal_edges original_circuit current_circuit replacement)"

  using renamed_edge
  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_contains_internal_edge:
  assumes internal_edge:
    "e \<in> subcircuit_internal_edges replacement"

  shows
    "rename_subcircuit_edge original_circuit e 
       \<in> edges (insert_subcircuit_internal_edges original_circuit current_circuit replacement)"

  using
    renamed_subcircuit_internal_edge[
      OF internal_edge,
      of original_circuit]
  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_nodes[simp]:
  "nodes (insert_subcircuit_internal_edges original_circuit current_circuit replacement) = nodes current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_node[simp]:
  "nodes (insert_subcircuit_internal_edges original_circuit current_circuit replacement) node_id = nodes current_circuit node_id"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_num_qubits[simp]:
  "num_qubits (insert_subcircuit_internal_edges original_circuit current_circuit replacement) = num_qubits current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_next_id[simp]:
  "next_id (insert_subcircuit_internal_edges original_circuit current_circuit replacement) = next_id current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

definition connect_subcircuit_input_on_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
where
  "connect_subcircuit_input_on_wire original_circuit operation_node replacement q current_circuit =
     (case (predecessor_on_wire original_circuit operation_node q, renamed_input_interface original_circuit replacement q)
      of
        (Some predecessor, Some input_node) \<Rightarrow> insert_edge (make_edge predecessor input_node q) current_circuit
      | _ \<Rightarrow> current_circuit)"

definition connect_subcircuit_inputs ::
  "quantum_circuit \<Rightarrow> quantum_circuit \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> quantum_circuit"
  where
    (* Redirects every incoming wire of the removed operation to the
       corresponding renamed input interface node of the replacement
       subcircuit.
  
       After this step, every predecessor of the removed operation
       becomes a predecessor of the replacement fragment.
    *)

    "connect_subcircuit_inputs original_circuit current_circuit operation_node replacement =
       Finite_Set.fold (connect_subcircuit_input_on_wire original_circuit operation_node replacement)
             current_circuit (subcircuit_interface_qubits replacement)"

lemma connect_subcircuit_input_on_wire_preserves_nodes[simp]:
  (* Connecting one replacement input wire changes only the edge set.
     Therefore, every node-table entry remains unchanged. *)
  "nodes (connect_subcircuit_input_on_wire original_circuit operation_node replacement q circuit) = nodes circuit"
  unfolding
    connect_subcircuit_input_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_inputs_preserve_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes (connect_subcircuit_inputs original_circuit circuit operation_node replacement) = nodes circuit"

proof -
  let ?connect_input = "connect_subcircuit_input_on_wire original_circuit operation_node replacement"

  interpret connect_input: comp_fun_commute ?connect_input
  proof
    fix first_qubit second_qubit

    show
      "?connect_input second_qubit \<circ> ?connect_input first_qubit 
       = ?connect_input first_qubit \<circ> ?connect_input second_qubit"
      unfolding
        connect_subcircuit_input_on_wire_def
        insert_edge_def
        fun_eq_iff
      apply (auto split: option.splits)
      by (simp add: insert_commute)
  qed

  have fold_preserves_nodes:
    "finite interface_qubits \<Longrightarrow> 
       nodes (Finite_Set.fold ?connect_input current_circuit interface_qubits) = nodes current_circuit"
    for interface_qubits current_circuit
 
  proof (induction interface_qubits arbitrary: current_circuit
           rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_input current_circuit (insert q interface_qubits)
         = ?connect_input q (Finite_Set.fold ?connect_input current_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have folded_nodes:
    "nodes (Finite_Set.fold ?connect_input circuit (subcircuit_interface_qubits replacement))
     = nodes circuit"
    using
      finite_interfaces
      fold_preserves_nodes
    by blast

  show ?thesis
    unfolding connect_subcircuit_inputs_def
    using folded_nodes
    by simp
qed

lemma connect_subcircuit_input_on_wire_preserves_num_qubits[simp]:
  (* Connecting one replacement input wire does not change the number
     of qubits in the host circuit. *)
  "num_qubits (connect_subcircuit_input_on_wire original_circuit operation_node replacement q circuit)
   = num_qubits circuit"
  unfolding
    connect_subcircuit_input_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_input_on_wire_preserves_next_id[simp]:
  (* Connecting one replacement input wire inserts no nodes and
     therefore does not advance the host circuit's allocation
     boundary. *)
  "next_id (connect_subcircuit_input_on_wire original_circuit operation_node replacement q circuit)
   = next_id circuit"
  unfolding
    connect_subcircuit_input_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_input_on_wire_commute:
  (* Connecting two replacement input wires is independent of the order
     in which the wires are processed.

     Each successful connection inserts one edge into the circuit's
     edge set. Since inserting edges into a set is commutative, applying
     the q1 connection followed by the q2 connection yields the same
     circuit as applying them in the opposite order.

     This property is required for Finite_Set.fold, because the
     interface-qubit set has no distinguished traversal order.
  *)
  "connect_subcircuit_input_on_wire original_circuit operation_node replacement q1 (connect_subcircuit_input_on_wire original_circuit operation_node replacement q2 circuit)
   = connect_subcircuit_input_on_wire original_circuit operation_node replacement q2 (connect_subcircuit_input_on_wire original_circuit operation_node replacement q1 circuit)"

  unfolding
    connect_subcircuit_input_on_wire_def
    insert_edge_def
  
  apply (auto split: option.splits prod.splits)
  by (simp add: insert_commute)

interpretation connect_subcircuit_input:
  comp_fun_commute "connect_subcircuit_input_on_wire original_circuit operation_node replacement"
  by (simp add: comp_def comp_fun_commute.intro connect_subcircuit_input_on_wire_commute)

lemma compatible_subcircuit_interface_qubits_finite:
  (* A compatible subcircuit has exactly the finite set of qubits
     listed by the replaced operation. Therefore, its interface-qubit
     set is finite. *)
  assumes compatible:
    "is_compatible_subcircuit qubits replacement"

  shows
    "finite (subcircuit_interface_qubits replacement)"

  using compatible
  unfolding is_compatible_subcircuit_def
  by simp

lemma connect_subcircuit_inputs_preserves_nodes[simp]:
  (* Folding the per-wire input connection over a finite interface set
     changes only edges. Hence the complete input-connection phase
     preserves the node table. *)
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes (connect_subcircuit_inputs original_circuit current_circuit operation_node replacement)
     = nodes current_circuit"

  unfolding connect_subcircuit_inputs_def
  using
    connect_subcircuit_inputs_def
    connect_subcircuit_inputs_preserve_nodes
    finite_interfaces
  by auto


definition connect_subcircuit_output_on_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
  where
  (* Connects the renamed output interface node on one wire to the
     original successor of the removed operation on that wire.

     The predecessor/successor information is read from the original
     circuit because the removed operation and its incident edges are
     no longer present in the current intermediate circuit.
  *)
  "connect_subcircuit_output_on_wire original_circuit operation_node replacement q current_circuit =
     (case
        (successor_on_wire original_circuit operation_node q, 
         renamed_output_interface original_circuit replacement q)
      of
        (Some successor, Some output_node) \<Rightarrow> insert_edge (make_edge output_node successor q) current_circuit
      | _ \<Rightarrow> current_circuit)"

definition connect_subcircuit_outputs ::
  "quantum_circuit \<Rightarrow> quantum_circuit \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> quantum_circuit"
  where
    (* Redirects every outgoing wire of the removed operation to the
       corresponding renamed output interface node of the replacement
       subcircuit.
  
       After this step, every successor of the removed operation becomes
       a successor of the replacement fragment.
    *)
    "connect_subcircuit_outputs original_circuit current_circuit operation_node replacement =
     Finite_Set.fold
       (connect_subcircuit_output_on_wire original_circuit operation_node replacement) current_circuit
       (subcircuit_interface_qubits replacement)"

lemma connect_subcircuit_output_on_wire_preserves_nodes[simp]:
  (* Connecting one replacement output wire changes only the edge set.
     Therefore, every node-table entry remains unchanged. *)
  "nodes (connect_subcircuit_output_on_wire original_circuit operation_node replacement q circuit)
   = nodes circuit"
  unfolding
    connect_subcircuit_output_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_outputs_preserve_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes (connect_subcircuit_outputs original_circuit circuit operation_node replacement) = nodes circuit"

proof -
  let ?connect_output = "connect_subcircuit_output_on_wire original_circuit operation_node replacement"

  interpret connect_output: comp_fun_commute ?connect_output
  proof
    fix first_qubit second_qubit

    show
      "?connect_output second_qubit \<circ> ?connect_output first_qubit
       = ?connect_output first_qubit \<circ> ?connect_output second_qubit"
      unfolding
        connect_subcircuit_output_on_wire_def
        insert_edge_def
        fun_eq_iff
      apply (auto split: option.splits)
      by (simp add: insert_commute)
  qed

  have fold_preserves_nodes:
    "finite interface_qubits \<Longrightarrow> nodes (Finite_Set.fold ?connect_output current_circuit interface_qubits)
     = nodes current_circuit"
    for interface_qubits current_circuit

  proof (induction interface_qubits arbitrary: current_circuit rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_output current_circuit (insert q interface_qubits)
       = ?connect_output q (Finite_Set.fold ?connect_output current_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have folded_nodes:
    "nodes (Finite_Set.fold ?connect_output circuit (subcircuit_interface_qubits replacement))
     = nodes circuit"
    using
      finite_interfaces
      fold_preserves_nodes
    by blast

  show ?thesis
    unfolding connect_subcircuit_outputs_def
    using folded_nodes
    by simp
qed

lemma connect_subcircuit_output_on_wire_preserves_num_qubits[simp]:
  (* Connecting one replacement output wire does not change the number
     of qubits in the host circuit. *)
  "num_qubits (connect_subcircuit_output_on_wire original_circuit operation_node replacement q circuit)
   = num_qubits circuit"
  unfolding
    connect_subcircuit_output_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_output_on_wire_preserves_next_id[simp]:
  (* Connecting one replacement output wire inserts no nodes and
     therefore does not advance the host circuit's allocation
     boundary. *)
  "next_id (connect_subcircuit_output_on_wire original_circuit operation_node replacement q circuit)
   = next_id circuit"
  unfolding
    connect_subcircuit_output_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_output_on_wire_commute:
  (* Connecting two replacement output wires is independent of the
     order in which the wires are processed.

     Each successful connection inserts one edge into the circuit's
     edge set. Since inserting edges into a set is commutative, applying
     the q1 connection followed by the q2 connection yields the same
     circuit as applying them in the opposite order.

     This property is required for Finite_Set.fold because the
     interface-qubit set has no distinguished traversal order.
  *)
  "connect_subcircuit_output_on_wire original_circuit operation_node replacement q1
      (connect_subcircuit_output_on_wire original_circuit operation_node replacement q2 circuit)
   = connect_subcircuit_output_on_wire original_circuit operation_node replacement q2
      (connect_subcircuit_output_on_wire original_circuit operation_node replacement q1 circuit)"

  unfolding
    connect_subcircuit_output_on_wire_def
    insert_edge_def
  
  apply (auto split: option.splits prod.splits)
  by (simp add: insert_commute)

interpretation connect_subcircuit_output:
  comp_fun_commute "connect_subcircuit_output_on_wire original_circuit operation_node replacement"

proof
  fix q1 q2

  show
    "connect_subcircuit_output_on_wire original_circuit operation_node replacement q2 \<circ>
     connect_subcircuit_output_on_wire original_circuit operation_node replacement q1
     = connect_subcircuit_output_on_wire original_circuit operation_node replacement q1 \<circ>
       connect_subcircuit_output_on_wire original_circuit operation_node replacement q2"

    apply (rule ext)
    using connect_subcircuit_output_on_wire_commute
    by simp
qed

lemma connect_subcircuit_outputs_preserves_nodes[simp]:
  (* Folding the per-wire output connection over a finite interface set
     changes only edges. Hence the complete output-connection phase
     preserves the node table. *)
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes (connect_subcircuit_outputs original_circuit current_circuit operation_node replacement)
     = nodes current_circuit"

  unfolding connect_subcircuit_outputs_def
  using
    connect_subcircuit_outputs_def
    connect_subcircuit_outputs_preserve_nodes
    finite_interfaces
  by auto


definition update_frontier_after_subcircuit ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> subcircuit \<Rightarrow> frontier"
where
  (* Updates the construction frontier after replacing an operation by
     a subcircuit.

     On every qubit for which the replacement has an output interface,
     the new frontier is the renamed output-interface node.

     On every other qubit, the original frontier is preserved.

     The original host circuit is required because its next_id fixes the
     renaming offset used for all inserted subcircuit nodes.
  *)
  "update_frontier_after_subcircuit original_circuit current_frontier replacement =
     (\<lambda>q.
        case renamed_output_interface original_circuit replacement q
        of
          Some output_node \<Rightarrow> output_node
        | None \<Rightarrow> current_frontier q)"

lemma update_frontier_after_subcircuit_with_output:
  (* If the replacement has a renamed output-interface node on q, that
     node becomes the new frontier on q. *)
  assumes renamed_output: 
    "renamed_output_interface original_circuit replacement q = Some output_node"

  shows
    "update_frontier_after_subcircuit original_circuit current_frontier replacement q = output_node"

  using renamed_output
  unfolding update_frontier_after_subcircuit_def
  by simp

lemma update_frontier_after_subcircuit_without_output:
  (* If the replacement has no output interface on q, the old frontier
     on q remains unchanged. *)
  assumes no_renamed_output:
    "renamed_output_interface original_circuit replacement q = None"

  shows
    "update_frontier_after_subcircuit original_circuit current_frontier replacement q = current_frontier q"

  using no_renamed_output
  unfolding update_frontier_after_subcircuit_def
  by simp

lemma update_frontier_after_subcircuit_output_interface:
  (* A local output-interface node becomes its renamed host-circuit node
     in the updated frontier. *)
  assumes output_interface:
    "output_interface replacement q = Some local_output_node"

  shows
    "update_frontier_after_subcircuit original_circuit current_frontier replacement q =
       rename_subcircuit_node_id original_circuit local_output_node"

  using output_interface
  unfolding
    update_frontier_after_subcircuit_def
    renamed_output_interface_def
  by simp

lemma update_frontier_after_subcircuit_no_output_interface:
  (* A qubit outside the replacement's output interface keeps its
     previous frontier node. *)
  assumes no_output_interface:
    "output_interface replacement q = None"

  shows
    "update_frontier_after_subcircuit original_circuit current_frontier replacement q = current_frontier q"

  using no_output_interface
  unfolding
    update_frontier_after_subcircuit_def
    renamed_output_interface_def
  by simp

definition replace_operation_by_subcircuit ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> quantum_circuit \<times> frontier"
where
  (* Replaces the specified operation node by the supplied subcircuit.

     The replacement proceeds in six stages:
       1. Remove the original operation.
       2. Copy the replacement operation nodes.
       3. Insert the replacement's internal edges.
       4. Connect incoming host wires.
       5. Connect outgoing host wires.
       6. Update the frontier.
                                       
     Each stage is specified independently to simplify correctness
     proofs.
  *)
  "replace_operation_by_subcircuit circuit frontier operation_node subcircuit =
     (let
        circuit1 = remove_operation_node circuit operation_node;
        circuit2 = insert_subcircuit_nodes circuit circuit1 subcircuit;
        circuit3 = insert_subcircuit_internal_edges circuit circuit2 subcircuit;
        circuit4 = connect_subcircuit_inputs circuit circuit3 operation_node subcircuit;
        circuit5 = connect_subcircuit_outputs circuit circuit4 operation_node subcircuit;
        frontier' = update_frontier_after_subcircuit circuit frontier subcircuit
      in
        (circuit5
           \<lparr>
             next_id :=
               NodeId (node_id_to_nat (next_id circuit) + node_id_to_nat (next_id (subgraph subcircuit)))
           \<rparr>, \<comment>\<open> The intermediate helpers preserve next_id so that the original allocation boundary can be used consistently for every renaming. Once all replacement nodes and edges have been installed, advance next_id beyond the copied local node namespace. \<close>
         frontier'))"

lemma replace_operation_by_subcircuit_next_id[simp]:
  (* After replacement, the allocation boundary lies beyond all copied
     replacement nodes. *)
  "next_id (fst (replace_operation_by_subcircuit circuit frontier operation_node replacement))
    = NodeId (node_id_to_nat (next_id circuit) + node_id_to_nat (next_id (subgraph replacement)))"

  unfolding replace_operation_by_subcircuit_def
  by simp

lemma replace_operation_by_subcircuit_frontier[simp]:
  (* The second component returned by replacement is precisely the
     updated construction frontier. *)
  "snd (replace_operation_by_subcircuit circuit frontier operation_node replacement)
   = update_frontier_after_subcircuit circuit frontier replacement"

  unfolding replace_operation_by_subcircuit_def
  by simp

lemma replace_operation_by_subcircuit_removes_old_operation:
  (* After replacing operation_node_id by a subcircuit, the original
     operation node is no longer present at operation_node_id.

     This establishes that replacement does not accidentally leave the
     removed operation in the resulting node table.
  *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  shows
    "nodes (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)) operation_node_id = None"

proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode original_op)"
    and valid_subcircuit:
      "is_valid_subcircuit replacement"
    and same_num_qubits:
      "num_qubits (subgraph replacement) = num_qubits circuit"
    and compatible:
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by auto

  have allocation_valid:
    "all_existing_node_ids_below_next_id circuit"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have operation_id_below_next_id:
    "node_id_to_nat operation_node_id < node_id_to_nat (next_id circuit)"
    using
      all_existing_node_ids_below_next_id_def
      allocation_valid
      operation_exists
    by simp

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using
      compatible
      compatible_subcircuit_interface_qubits_finite
    by simp

  let ?circuit1 = "remove_operation_node circuit operation_node_id"

  let ?circuit2 = "insert_subcircuit_nodes circuit ?circuit1 replacement"

  let ?circuit3 = "insert_subcircuit_internal_edges circuit ?circuit2 replacement"

  let ?circuit4 = "connect_subcircuit_inputs circuit ?circuit3 operation_node_id replacement"

  let ?circuit5 = "connect_subcircuit_outputs circuit ?circuit4 operation_node_id replacement"

  have absent_after_removal:
    "nodes ?circuit1 operation_node_id = None"
    by simp

  have absent_after_node_insertion:
    "nodes ?circuit2 operation_node_id = None"
    using
      insert_subcircuit_nodes_preserves_node_below_next_id
      operation_id_below_next_id
    by simp

  have absent_after_internal_edges:
    "nodes ?circuit3 operation_node_id = None"
    using absent_after_node_insertion
    by simp

  have absent_after_input_connections:
    "nodes ?circuit4 operation_node_id = None"
    using
      absent_after_node_insertion
      finite_interfaces
    by simp

  have absent_after_output_connections:
    "nodes ?circuit5 operation_node_id = None"
    using
      absent_after_input_connections
      finite_interfaces
    by simp

  show ?thesis
    unfolding replace_operation_by_subcircuit_def
    using absent_after_output_connections
    by simp
qed

lemma replace_operation_by_subcircuit_contains_renamed_nodes:
  (* Every operation node from the replacement subcircuit appears in
     the resulting circuit at the global node ID assigned by the
     replacement renaming function.
  *)

  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  assumes local_operation:
    "nodes (subgraph replacement) local_node_id = Some (OperationNode op)"

  assumes allocated_local_node:
    "local_node_id \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes (fst (replace_operation_by_subcircuit original_circuit frontier operation_node_id replacement))
       (rename_subcircuit_node_id original_circuit local_node_id) = Some (OperationNode op)"

  by (simp add: allocated_local_node finite_interfaces insert_subcircuit_nodes_copies_operation local_operation
      replace_operation_by_subcircuit_def)

lemma replace_operation_by_subcircuit_preserves_unrelated_nodes:
  (* Every existing original circuit node other than the removed
     operation node remains unchanged after subcircuit replacement. *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  assumes original_node:
    "nodes circuit other_node_id = Some node"

  shows
    "nodes
       (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)) other_node_id
     = Some node"
  using
    all_existing_node_ids_below_next_id_def
    compatible_subcircuit_interface_qubits_finite
    different_node
    insert_subcircuit_nodes_preserves_node_below_next_id
    is_valid_construction_state_def
    is_valid_subcircuit_replacement_def
    original_node
    replace_operation_by_subcircuit_def
    valid_replacement
    valid_state
  by fastforce

lemma replace_operation_by_subcircuit_contains_renamed_internal_edges:
  (* Every internal edge of the replacement subcircuit appears in the
     resulting circuit after both endpoint IDs have been renamed into
     the surrounding circuit's node-ID space. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement original_circuit operation_node_id replacement"

  assumes internal_edge:
    "e \<in> subcircuit_internal_edges replacement"

  shows
    "rename_subcircuit_edge original_circuit e
       \<in> edges 
         (fst (replace_operation_by_subcircuit original_circuit frontier operation_node_id replacement))"
proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id = Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by auto

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using
      compatible
      compatible_subcircuit_interface_qubits_finite
    by simp

  let ?renamed_edge =
    "rename_subcircuit_edge original_circuit e"

  let ?circuit1 = "remove_operation_node original_circuit operation_node_id"

  let ?circuit2 = "insert_subcircuit_nodes original_circuit ?circuit1 replacement"

  let ?circuit3 = "insert_subcircuit_internal_edges original_circuit ?circuit2 replacement"

  let ?circuit4 = "connect_subcircuit_inputs original_circuit ?circuit3 operation_node_id replacement"

  let ?circuit5 = "connect_subcircuit_outputs original_circuit ?circuit4 operation_node_id replacement"

  have inserted_internal_edge:
    "?renamed_edge \<in> edges ?circuit3"
    using internal_edge
    by (rule insert_subcircuit_internal_edges_contains_internal_edge)

  have input_step_preserves_edge:
    "edge_to_preserve \<in> edges circuit
     \<Longrightarrow> edge_to_preserve \<in> edges (connect_subcircuit_input_on_wire original_circuit operation_node_id replacement q circuit)"
    for edge_to_preserve circuit q

    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have input_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow> edge_to_preserve \<in> edges circuit
     \<Longrightarrow> edge_to_preserve \<in>  
       edges 
         (Finite_Set.fold
            (connect_subcircuit_input_on_wire original_circuit operation_node_id replacement)
            circuit interface_qubits)"
    for interface_qubits circuit edge_to_preserve

  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)

    let ?connect = "connect_subcircuit_input_on_wire original_circuit operation_node_id replacement"

    have edge_after_remaining_wires:
      "edge_to_preserve \<in> edges (Finite_Set.fold ?connect circuit interface_qubits)"
      using
        insert.IH
        insert.prems
      by simp

    have edge_after_current_wire:
      "edge_to_preserve \<in> edges (?connect q (Finite_Set.fold ?connect circuit interface_qubits))"
      using
        edge_after_remaining_wires
        input_step_preserves_edge
      by blast

    have fold_insert:
      "Finite_Set.fold ?connect circuit (insert q interface_qubits)
       = ?connect q (Finite_Set.fold ?connect circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      using
        fold_insert
        edge_after_current_wire
      by simp
  qed

  have preserved_after_inputs:
    "?renamed_edge \<in> edges ?circuit4"
    unfolding
      connect_subcircuit_inputs_def
    using
      finite_interfaces
      inserted_internal_edge
      input_fold_preserves_edge
    by blast

  have output_step_preserves_edge:
    "edge_to_preserve \<in> edges circuit 
     \<Longrightarrow> edge_to_preserve \<in> edges (connect_subcircuit_output_on_wire original_circuit operation_node_id replacement q circuit)"
    for edge_to_preserve circuit q

    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow>edge_to_preserve \<in> edges circuit
     \<Longrightarrow> edge_to_preserve
         \<in> edges (Finite_Set.fold (connect_subcircuit_output_on_wire original_circuit operation_node_id replacement) circuit interface_qubits)"
    
    for interface_qubits circuit edge_to_preserve
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)
    let ?connect = "connect_subcircuit_output_on_wire original_circuit operation_node_id replacement"

    have edge_after_remaining_wires:
      "edge_to_preserve \<in> edges (Finite_Set.fold ?connect circuit interface_qubits)"
      using
        insert.IH
        insert.prems
      by simp

    have edge_after_current_wire:
      "edge_to_preserve \<in> edges (?connect q (Finite_Set.fold ?connect circuit interface_qubits))"
      using
        edge_after_remaining_wires
        output_step_preserves_edge
      by blast

    have fold_insert:
      "Finite_Set.fold ?connect circuit (insert q interface_qubits)
       = ?connect q (Finite_Set.fold ?connect circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      using
        fold_insert
        edge_after_current_wire
      by simp
  qed

  have preserved_after_outputs:
    "?renamed_edge \<in> edges ?circuit5"
    unfolding
      connect_subcircuit_outputs_def
    using
      finite_interfaces
      preserved_after_inputs
      output_fold_preserves_edge
    by simp

  show ?thesis
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    using preserved_after_outputs
    by simp
qed

lemma replace_operation_by_subcircuit_connects_inputs:
  (* On every interface wire, the predecessor of the removed operation
     is connected to the renamed input-interface node of the inserted
     subcircuit. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement original_circuit operation_node_id replacement"

  assumes predecessor:
    "predecessor_on_wire original_circuit operation_node_id q = Some predecessor_node"

  assumes input_interface:
    "input_interface replacement q = Some local_input_node"

  shows
    "make_edge predecessor_node (rename_subcircuit_node_id original_circuit local_input_node) q
       \<in> edges (fst (replace_operation_by_subcircuit original_circuit frontier operation_node_id replacement))"
proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id = Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

  have q_in_interfaces:
    "q \<in> subcircuit_interface_qubits replacement"
    using input_interface
    unfolding subcircuit_interface_qubits_def
    by simp

  have renamed_input:
    "renamed_input_interface original_circuit replacement q
     = Some (rename_subcircuit_node_id original_circuit local_input_node)"
    using input_interface
    unfolding renamed_input_interface_def
    by simp

  let ?new_edge = "make_edge predecessor_node (rename_subcircuit_node_id original_circuit local_input_node) q"

  let ?connect_input = "connect_subcircuit_input_on_wire original_circuit operation_node_id replacement"

  have input_step_preserves_edge:
    "e \<in> edges circuit \<Longrightarrow> e \<in> edges (?connect_input wire circuit)"
    for e circuit wire
    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have selected_input_step_adds_edge:
    "?new_edge \<in> edges (?connect_input q circuit)"
    for circuit
    using predecessor renamed_input
    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by simp

  have input_fold_contains_edge:
    "finite interface_qubits
     \<Longrightarrow> q \<in> interface_qubits
     \<Longrightarrow> ?new_edge \<in> edges (Finite_Set.fold ?connect_input circuit interface_qubits)"
    for interface_qubits circuit
    using 
      connect_subcircuit_input.fold_rec
      selected_input_step_adds_edge
    by simp

  let ?circuit1 = "remove_operation_node original_circuit operation_node_id"

  let ?circuit2 = "insert_subcircuit_nodes original_circuit ?circuit1 replacement"

  let ?circuit3 = "insert_subcircuit_internal_edges original_circuit ?circuit2 replacement"

  let ?circuit4 = "connect_subcircuit_inputs original_circuit ?circuit3 operation_node_id replacement"

  have edge_after_inputs:
    "?new_edge \<in> edges ?circuit4"
    unfolding connect_subcircuit_inputs_def
    using
      finite_interfaces
      q_in_interfaces
      input_fold_contains_edge
    by simp

  let ?connect_output = "connect_subcircuit_output_on_wire original_circuit operation_node_id replacement"

  have output_step_preserves_edge:
    "e \<in> edges circuit \<Longrightarrow> e \<in> edges (?connect_output wire circuit)"
    for e circuit wire
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow> e \<in> edges circuit
     \<Longrightarrow> e \<in> edges (Finite_Set.fold ?connect_output circuit interface_qubits)"
    for interface_qubits circuit e
 
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert wire interface_qubits)

    have fold_insert: 
      "Finite_Set.fold ?connect_output circuit (insert wire interface_qubits)
       = ?connect_output wire (Finite_Set.fold ?connect_output circuit interface_qubits)"
      using insert.hyps(1, 2)
      by (rule connect_subcircuit_output.fold_insert)

    have edge_after_remaining:
      "e \<in> edges (Finite_Set.fold ?connect_output circuit interface_qubits)"
      using insert.IH insert.prems
      by simp

    have edge_after_current:
      "e \<in> edges (?connect_output wire (Finite_Set.fold ?connect_output circuit interface_qubits))"
      using edge_after_remaining
      by (rule output_step_preserves_edge)

    show ?case
      unfolding fold_insert
      using edge_after_current .
  qed

  let ?circuit5 = "connect_subcircuit_outputs original_circuit ?circuit4 operation_node_id replacement"

  have edge_after_outputs:
    "?new_edge \<in> edges ?circuit5"
    unfolding connect_subcircuit_outputs_def
    using
      finite_interfaces
      edge_after_inputs
      output_fold_preserves_edge
    by blast

  show ?thesis
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    using edge_after_outputs
    by simp
qed

lemma replace_operation_by_subcircuit_connects_outputs:
  (* On every interface wire, the renamed output-interface node of the
     inserted subcircuit is connected to the successor of the removed
     operation. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement original_circuit operation_node_id replacement"

  assumes successor:
    "successor_on_wire original_circuit operation_node_id q = Some successor_node"

  assumes output_interface:
    "output_interface replacement q = Some local_output_node"

  shows
    "make_edge (rename_subcircuit_node_id original_circuit local_output_node) successor_node q
       \<in> edges (fst (replace_operation_by_subcircuit original_circuit frontier operation_node_id replacement))"
proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id = Some (OperationNode original_op)"
    and compatible: 
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by auto

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

  have q_in_interfaces:
    "q \<in> subcircuit_interface_qubits replacement"
    using
      is_valid_subcircuit_def
      is_valid_subcircuit_replacement_def
      output_interface
      subcircuit_interface_qubits_def
      valid_replacement
    by auto


  have renamed_output:
    "renamed_output_interface original_circuit replacement q
     = Some (rename_subcircuit_node_id original_circuit local_output_node)"
    using output_interface
    unfolding renamed_output_interface_def
    by simp

  let ?new_edge = "make_edge (rename_subcircuit_node_id original_circuit local_output_node) successor_node q"

  let ?connect_output = "connect_subcircuit_output_on_wire original_circuit operation_node_id replacement"

  have output_step_preserves_edge:
    "e \<in> edges circuit \<Longrightarrow> e \<in> edges (?connect_output wire circuit)"
    for e circuit wire
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have selected_output_step_adds_edge:
    "?new_edge \<in> edges (?connect_output q circuit)"
    for circuit
    using successor renamed_output
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by simp

  have output_fold_contains_edge:
    "finite interface_qubits
     \<Longrightarrow> q \<in> interface_qubits
     \<Longrightarrow> ?new_edge \<in> edges (Finite_Set.fold ?connect_output circuit interface_qubits)"
    for interface_qubits circuit
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert wire interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_output circuit (insert wire interface_qubits)
       = ?connect_output wire (Finite_Set.fold ?connect_output circuit interface_qubits)"
      using insert.hyps(1, 2)
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      using
        fold_insert
        insert.IH
        insert.prems
        output_step_preserves_edge
        selected_output_step_adds_edge
      by auto
  qed

  show ?thesis
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    using
      connect_subcircuit_outputs_def
      finite_interfaces
      output_fold_contains_edge
      q_in_interfaces
    by simp  
qed

lemma replace_operation_by_subcircuit_preserves_unrelated_edges:
  (* Every edge that does not touch the removed operation is preserved by
     subcircuit replacement. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement original_circuit operation_node_id replacement"

  assumes unrelated_edge:
    "e \<in> edges original_circuit"

  assumes source_not_removed:
    "edge_source e \<noteq> operation_node_id"

  assumes target_not_removed:
    "edge_target e \<noteq> operation_node_id"

  shows
    "e \<in> edges
        (fst (replace_operation_by_subcircuit original_circuit frontier operation_node_id replacement))"

proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id = Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

  let ?circuit1 = "remove_operation_node original_circuit operation_node_id" 

  let ?circuit2 = "insert_subcircuit_nodes original_circuit ?circuit1 replacement"

  let ?circuit3 = "insert_subcircuit_internal_edges original_circuit ?circuit2 replacement"

  let ?circuit4 = "connect_subcircuit_inputs original_circuit ?circuit3 operation_node_id replacement"

  let ?circuit5 = "connect_subcircuit_outputs original_circuit ?circuit4 operation_node_id replacement"
 
  have edge_after_removal:
    "e \<in> edges ?circuit1"
    using
      unrelated_edge
      source_not_removed
      target_not_removed
    by (rule remove_operation_node_preserves_unrelated_edge)

  have edge_after_node_insertion:
    "e \<in> edges ?circuit2"
    using edge_after_removal
    unfolding insert_subcircuit_nodes_def
    by simp

  have edge_after_internal_edges:
    "e \<in> edges ?circuit3"
    using edge_after_node_insertion
    unfolding insert_subcircuit_internal_edges_def
    by auto

  have input_step_preserves_edge:
    "edge_to_preserve \<in> edges circuit
     \<Longrightarrow> edge_to_preserve
         \<in> edges (connect_subcircuit_input_on_wire original_circuit operation_node_id replacement q circuit)"
    
    for edge_to_preserve circuit q
    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have input_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow> edge_to_preserve \<in> edges circuit
     \<Longrightarrow> edge_to_preserve
       \<in> edges
           (Finite_Set.fold 
              (connect_subcircuit_input_on_wire original_circuit operation_node_id replacement) circuit interface_qubits)"
    for interface_qubits circuit edge_to_preserve
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)

    let ?connect = "connect_subcircuit_input_on_wire original_circuit operation_node_id replacement"

    have edge_after_remaining:
      "edge_to_preserve \<in> edges (Finite_Set.fold ?connect circuit interface_qubits)"
      using insert.IH insert.prems
      by blast

    have edge_after_q:
      "edge_to_preserve \<in> edges (?connect q (Finite_Set.fold ?connect circuit interface_qubits))"
      using edge_after_remaining
      by (rule input_step_preserves_edge)

    have fold_insert:
      "Finite_Set.fold ?connect circuit (insert q interface_qubits)
       = ?connect q (Finite_Set.fold ?connect circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      using edge_after_q
      unfolding fold_insert
      by simp
  qed

  have edge_after_inputs:
    "e \<in> edges ?circuit4"
    unfolding connect_subcircuit_inputs_def
    using
      finite_interfaces
      edge_after_internal_edges
      input_fold_preserves_edge
    by simp

    have output_step_preserves_edge:
    "edge_to_preserve \<in> edges circuit
     \<Longrightarrow> edge_to_preserve
       \<in> edges (connect_subcircuit_output_on_wire original_circuit operation_node_id replacement q circuit)"
    for edge_to_preserve circuit q
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow> edge_to_preserve \<in> edges circuit
     \<Longrightarrow> edge_to_preserve
       \<in> edges
           (Finite_Set.fold 
             (connect_subcircuit_output_on_wire original_circuit operation_node_id replacement) circuit interface_qubits)"
    for interface_qubits circuit edge_to_preserve

  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)

    let ?connect = "connect_subcircuit_output_on_wire original_circuit operation_node_id replacement"

    have edge_after_remaining:
      "edge_to_preserve \<in> edges (Finite_Set.fold ?connect circuit interface_qubits)"
      using
        insert.IH
        insert.prems
      by simp

    have edge_after_q:
      "edge_to_preserve \<in> edges (?connect q (Finite_Set.fold ?connect circuit interface_qubits))"
      using edge_after_remaining
      by (rule output_step_preserves_edge)

    have fold_insert:
      "Finite_Set.fold ?connect circuit (insert q interface_qubits)
       = ?connect q (Finite_Set.fold ?connect circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      using edge_after_q
      unfolding fold_insert .
  qed

  have edge_after_outputs:
    "e \<in> edges ?circuit5"
    unfolding connect_subcircuit_outputs_def
    using
      finite_interfaces
      edge_after_inputs
      output_fold_preserves_edge
    by simp

  show ?thesis
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    using edge_after_outputs
    by simp
qed

lemma replace_operation_by_subcircuit_node_cases:
  (* Every node in the resulting circuit is either:
       1. an unchanged node of the original circuit other than the removed
          operation node, or
       2. a renamed operation node copied from the replacement subcircuit.
  *)
  assumes valid_state:
    "is_valid_construction_state original_circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement original_circuit operation_node_id replacement"

  assumes node_in_result:
    "nodes (fst(replace_operation_by_subcircuit original_circuit frontier operation_node_id replacement)) node_id
     = Some node"

  shows
    "(node_id \<noteq> operation_node_id
      \<and> nodes original_circuit node_id = Some node)
      \<or> (\<exists>local_node_id.
          local_node_id \<in> subcircuit_operation_node_ids replacement
          \<and> node_id = rename_subcircuit_node_id original_circuit local_node_id
          \<and> nodes (subgraph replacement) local_node_id = Some node)"

proof -
  let ?circuit1 =
    "remove_operation_node
       original_circuit
       operation_node_id"

  let ?circuit2 =
    "insert_subcircuit_nodes
       original_circuit
       ?circuit1
       replacement"

  let ?circuit3 =
    "insert_subcircuit_internal_edges
       original_circuit
       ?circuit2
       replacement"

  let ?circuit4 =
    "connect_subcircuit_inputs
       original_circuit
       ?circuit3
       operation_node_id
       replacement"

  let ?circuit5 =
    "connect_subcircuit_outputs
       original_circuit
       ?circuit4
       operation_node_id
       replacement"

  have result_node_in_circuit5:
    "nodes ?circuit5 node_id = Some node"
    using node_in_result
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    by simp

  have node_after_outputs:
    "nodes ?circuit4 node_id = Some node"
    using
      result_node_in_circuit5
      compatible_subcircuit_interface_qubits_finite
      is_valid_subcircuit_replacement_def
      valid_replacement
    by auto

  have node_after_inputs:
    "nodes ?circuit3 node_id = Some node"
    using
      node_after_outputs
      compatible_subcircuit_interface_qubits_finite
      is_valid_subcircuit_replacement_def
      valid_replacement
    by auto

  have node_after_internal_edges:
    "nodes ?circuit2 node_id = Some node"
    using node_after_inputs
    unfolding insert_subcircuit_internal_edges_def
    by simp

  from insert_subcircuit_nodes_node_cases[
      OF node_after_internal_edges]
  
  show ?thesis
    by (metis option.distinct(1) remove_operation_node_other remove_operation_node_selected)

qed

lemma replace_operation_by_subcircuit_edge_cases:
  (* Every edge in the resulting circuit is one of:
       1. an original edge unrelated to the removed operation,
       2. a renamed internal edge of the replacement,
       3. an input-interface reconnection edge, or
       4. an output-interface reconnection edge.
  *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement original_circuit operation_node_id replacement"

  assumes edge_in_result:
    "e \<in> edges (fst (replace_operation_by_subcircuit original_circuit frontier operation_node_id replacement))"

  shows
    "(e \<in> edges original_circuit
      \<and> edge_source e \<noteq> operation_node_id
      \<and> edge_target e \<noteq> operation_node_id)

     \<or> e \<in> renamed_subcircuit_internal_edges original_circuit replacement
     \<or> (\<exists>q predecessor_node renamed_input_node.
         q \<in> subcircuit_interface_qubits replacement
        \<and> predecessor_on_wire original_circuit operation_node_id q = Some predecessor_node
        \<and> renamed_input_interface original_circuit replacement q = Some renamed_input_node
        \<and> e = make_edge predecessor_node renamed_input_node q)

     \<or> (\<exists>q renamed_output_node successor_node.
        q \<in> subcircuit_interface_qubits replacement
        \<and> renamed_output_interface original_circuit replacement q = Some renamed_output_node
        \<and> successor_on_wire original_circuit operation_node_id q = Some successor_node
        \<and> e = make_edge renamed_output_node successor_node q)"

proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id = Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

  let ?circuit1 = "remove_operation_node original_circuit operation_node_id"

  let ?circuit2 = "insert_subcircuit_nodes original_circuit ?circuit1 replacement"

  let ?circuit3 = "insert_subcircuit_internal_edges original_circuit ?circuit2 replacement"

  let ?circuit4 = "connect_subcircuit_inputs original_circuit ?circuit3 operation_node_id replacement"

  let ?circuit5 = "connect_subcircuit_outputs original_circuit ?circuit4 operation_node_id replacement"

  have edge_in_circuit5:
    "e \<in> edges ?circuit5"
    using edge_in_result
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    by simp

  let ?connect_input = "connect_subcircuit_input_on_wire original_circuit operation_node_id replacement"

  let ?connect_output = "connect_subcircuit_output_on_wire original_circuit operation_node_id replacement"

  have input_step_cases:
    "edge_to_classify \<in> edges (?connect_input q circuit)
     \<Longrightarrow> edge_to_classify \<in> edges circuit
       \<or> (\<exists>predecessor_node renamed_input_node.
          predecessor_on_wire original_circuit operation_node_id q = Some predecessor_node
          \<and> renamed_input_interface original_circuit replacement q = Some renamed_input_node
          \<and> edge_to_classify = make_edge predecessor_node renamed_input_node q)"
    for edge_to_classify circuit q
    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have input_fold_cases:
    "finite interface_qubits
     \<Longrightarrow> edge_to_classify \<in> edges (Finite_Set.fold ?connect_input circuit interface_qubits)
     \<Longrightarrow> edge_to_classify \<in> edges circuit
       \<or>
       (\<exists>q predecessor_node renamed_input_node.
          q \<in> interface_qubits
          \<and> predecessor_on_wire original_circuit operation_node_id q = Some predecessor_node
          \<and> renamed_input_interface original_circuit replacement q = Some renamed_input_node
          \<and> edge_to_classify = make_edge predecessor_node renamed_input_node q)"
    for interface_qubits circuit edge_to_classify
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_input circuit (insert q interface_qubits)
       = ?connect_input q (Finite_Set.fold ?connect_input circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    have edge_after_q:
      "edge_to_classify \<in> edges (?connect_input q (Finite_Set.fold ?connect_input circuit interface_qubits))"
      using insert.prems
      unfolding fold_insert
      by simp

    from input_step_cases[OF edge_after_q]
    show ?case
      using insert.IH
      by auto
  qed

  have output_step_cases:
    "edge_to_classify \<in> edges (?connect_output q circuit)
     \<Longrightarrow> edge_to_classify \<in> edges circuit
       \<or> (\<exists>renamed_output_node successor_node.
          renamed_output_interface original_circuit replacement q = Some renamed_output_node
        \<and> successor_on_wire original_circuit operation_node_id q = Some successor_node
        \<and> edge_to_classify = make_edge renamed_output_node successor_node q)"
    for edge_to_classify circuit q
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_cases:
    "finite interface_qubits
     \<Longrightarrow> edge_to_classify \<in>  edges (Finite_Set.fold ?connect_output circuit interface_qubits)
     \<Longrightarrow> edge_to_classify \<in> edges circuit
       \<or> (\<exists>q renamed_output_node successor_node.
          q \<in> interface_qubits
          \<and> renamed_output_interface original_circuit replacement q = Some renamed_output_node
          \<and> successor_on_wire original_circuit operation_node_id q = Some successor_node
          \<and> edge_to_classify = make_edge renamed_output_node successor_node q)"
    for interface_qubits circuit edge_to_classify

  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_output circuit (insert q interface_qubits)
       = ?connect_output q (Finite_Set.fold ?connect_output circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    have edge_after_q:
      "edge_to_classify \<in> edges (?connect_output q (Finite_Set.fold ?connect_output circuit interface_qubits))"
      using insert.prems
      unfolding fold_insert
      by simp

    from output_step_cases[OF edge_after_q]
    show ?case
      using insert.IH
      by auto
  qed

  have after_output_cases:
    "e \<in> edges ?circuit4
     \<or> (\<exists>q renamed_output_node successor_node.
        q \<in> subcircuit_interface_qubits replacement
        \<and> renamed_output_interface original_circuit replacement q = Some renamed_output_node
        \<and> successor_on_wire original_circuit operation_node_id q = Some successor_node
        \<and> e = make_edge renamed_output_node successor_node q)"

    using
      connect_subcircuit_outputs_def
      edge_in_circuit5
      finite_interfaces
      output_fold_cases
    by auto

  from after_output_cases show ?thesis
  proof
    assume edge_before_outputs:
      "e \<in> edges ?circuit4"

    have after_input_cases:
      "e \<in> edges ?circuit3
       \<or>
       (\<exists>q predecessor_node renamed_input_node.
          q \<in> subcircuit_interface_qubits replacement
          \<and> predecessor_on_wire original_circuit operation_node_id q = Some predecessor_node
          \<and> renamed_input_interface original_circuit replacement q = Some renamed_input_node
          \<and> e = make_edge predecessor_node renamed_input_node q)"
      using
        connect_subcircuit_inputs_def
        edge_before_outputs
        finite_interfaces
        input_fold_cases
      unfolding connect_subcircuit_inputs_def
      by presburger

    from after_input_cases show ?thesis
      by auto

  next
    assume output_edge:
      "\<exists>q renamed_output_node successor_node.
         q \<in> subcircuit_interface_qubits replacement
         \<and> renamed_output_interface original_circuit replacement q = Some renamed_output_node
         \<and> successor_on_wire original_circuit operation_node_id q = Some successor_node
         \<and> e = make_edge renamed_output_node successor_node q"

    then show ?thesis
      by blast
  qed
qed

lemma replace_operation_by_subcircuit_preserves_boundary_nodes:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  shows
    "are_well_formed_boundary_nodes
       (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement))"

proof -
  let ?result = "fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)"

  from valid_state have original_well_formed:
    "is_well_formed_circuit circuit"
    unfolding is_valid_construction_state_def
    by simp

  from original_well_formed have original_boundaries:
    "are_well_formed_boundary_nodes circuit"
    unfolding is_well_formed_circuit_def
    by simp

  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode original_op)"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using valid_replacement
    unfolding
      is_valid_subcircuit_replacement_def
      is_compatible_subcircuit_def
    by auto

  let ?circuit1 =
    "remove_operation_node circuit operation_node_id"

  let ?circuit2 = "insert_subcircuit_nodes circuit ?circuit1 replacement"

  let ?circuit3 = "insert_subcircuit_internal_edges circuit ?circuit2 replacement"

  let ?connect_input = "connect_subcircuit_input_on_wire circuit operation_node_id replacement"

  let ?connect_output = "connect_subcircuit_output_on_wire circuit operation_node_id replacement"

  have input_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow> num_qubits (Finite_Set.fold ?connect_input base_circuit interface_qubits) = num_qubits base_circuit"
    for interface_qubits base_circuit

  proof (induction interface_qubits arbitrary: base_circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_input base_circuit (insert q interface_qubits)
       = ?connect_input q (Finite_Set.fold ?connect_input base_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have output_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow> num_qubits (Finite_Set.fold ?connect_output base_circuit interface_qubits) = num_qubits base_circuit"
    for interface_qubits base_circuit

  proof (induction interface_qubits arbitrary: base_circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_output base_circuit (insert q interface_qubits)
       = ?connect_output q (Finite_Set.fold ?connect_output base_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have inputs_preserve_num_qubits:
    "num_qubits (connect_subcircuit_inputs circuit ?circuit3 operation_node_id replacement)
     = num_qubits ?circuit3"
    unfolding connect_subcircuit_inputs_def
    using
      finite_interfaces
      input_fold_preserves_num_qubits
    by blast

  let ?circuit4 = "connect_subcircuit_inputs circuit ?circuit3 operation_node_id replacement"

  have outputs_preserve_num_qubits:
    "num_qubits (connect_subcircuit_outputs circuit ?circuit4 operation_node_id replacement) = num_qubits ?circuit4"
    unfolding connect_subcircuit_outputs_def
    using
      finite_interfaces
      output_fold_preserves_num_qubits
    by blast

  have result_num_qubits:
    "num_qubits ?result = num_qubits circuit"
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    using
      inputs_preserve_num_qubits
      outputs_preserve_num_qubits
    by simp

  show ?thesis
    unfolding are_well_formed_boundary_nodes_def
    by (metis
        are_well_formed_boundary_nodes_def
        circuit_node.distinct(3,5)
        operation_exists
        option.inject
        original_boundaries
        replace_operation_by_subcircuit_preserves_unrelated_nodes
        result_num_qubits
        valid_replacement
        valid_state)
qed

lemma replace_operation_by_subcircuit_preserves_well_formed_operation_nodes:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  shows
    "are_well_formed_operation_nodes 
       (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement))"

proof -
  let ?result = "fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)"

  from valid_state have original_well_formed:
    "is_well_formed_circuit circuit"
    unfolding is_valid_construction_state_def
    by simp

  from original_well_formed have original_operation_nodes:
    "are_well_formed_operation_nodes circuit"
    unfolding is_well_formed_circuit_def
    by simp

  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode original_op)"
  and replacement_valid:
      "is_valid_subcircuit replacement"
  and same_num_qubits:
      "num_qubits (subgraph replacement) = num_qubits circuit"
  and compatible:
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  from replacement_valid have replacement_well_formed:
    "is_well_formed_circuit (subgraph replacement)"
    unfolding
      is_valid_subcircuit_def
      is_valid_circuit_def
    by simp

  from replacement_well_formed
  have replacement_operation_nodes:
    "are_well_formed_operation_nodes
       (subgraph replacement)"
    unfolding is_well_formed_circuit_def
    by simp

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

  let ?connect_input = "connect_subcircuit_input_on_wire circuit operation_node_id replacement"

  have input_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow> num_qubits (Finite_Set.fold ?connect_input current_circuit interface_qubits) = num_qubits current_circuit"
    for interface_qubits current_circuit

  proof (induction interface_qubits arbitrary: current_circuit rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_input current_circuit (insert q interface_qubits)
       = ?connect_input q (Finite_Set.fold ?connect_input current_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  let ?connect_output = "connect_subcircuit_output_on_wire circuit operation_node_id replacement"

  have output_fold_preserves_num_qubits:
    "finite interface_qubits \<Longrightarrow> num_qubits (Finite_Set.fold ?connect_output current_circuit interface_qubits)
     = num_qubits current_circuit"
    for interface_qubits current_circuit

  proof (induction interface_qubits arbitrary: current_circuit rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_output current_circuit (insert q interface_qubits)
       = ?connect_output q (Finite_Set.fold ?connect_output current_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have result_num_qubits:
    "num_qubits ?result = num_qubits circuit"
    using
        connect_subcircuit_inputs_def
        connect_subcircuit_outputs_def
        finite_interfaces
        input_fold_preserves_num_qubits
        output_fold_preserves_num_qubits
        replace_operation_by_subcircuit_def
    by simp

  show ?thesis
    unfolding are_well_formed_operation_nodes_def
    by (metis
        are_well_formed_operation_nodes_def
        operation_in_circuit_def
        original_operation_nodes
        qubit_in_circuit_def
        replace_operation_by_subcircuit_node_cases
        replacement_operation_nodes
        result_num_qubits
        same_num_qubits
        valid_replacement
        valid_state)
qed

lemma valid_subcircuit_input_interface_uses_qubit:
  assumes valid_subcircuit:
    "is_valid_subcircuit replacement"

  assumes input_interface:
    "input_interface replacement q = Some node_id"

  assumes operation_node:
    "nodes (subgraph replacement) node_id = Some (OperationNode op)"

  shows
    "q \<in> set (op_qargs op)"

proof -
  from valid_subcircuit input_interface
  have first_operation:
    "is_first_operation_on_subcircuit_wire replacement q node_id"
    unfolding is_valid_subcircuit_def
    by blast

  from first_operation have input_edge:
    "(get_input_node_id q, node_id) \<in> wire_edge_relation (subgraph replacement) q"
    unfolding is_first_operation_on_subcircuit_wire_def
    by blast

  then have edge_in_subgraph:
    "make_edge (get_input_node_id q) node_id q \<in> edges (subgraph replacement)"
    unfolding wire_edge_relation_def
    by simp

  from valid_subcircuit have valid_subgraph:
    "is_valid_circuit (subgraph replacement)"
    unfolding is_valid_subcircuit_def
    by simp

  from valid_subgraph have well_formed_subgraph:
    "is_well_formed_circuit (subgraph replacement)"
    unfolding is_valid_circuit_def
    by simp

  from well_formed_subgraph have well_formed_edges:
    "are_well_formed_edges (subgraph replacement)"
    unfolding is_well_formed_circuit_def
    by simp

  from well_formed_edges edge_in_subgraph
  have well_formed_input_edge:
    "is_well_formed_edge (subgraph replacement) (make_edge (get_input_node_id q) node_id q)"
    unfolding are_well_formed_edges_def
    by blast

  from well_formed_input_edge operation_node
  have
    "node_uses_qubit (OperationNode op) q"
    unfolding
      is_well_formed_edge_def
      make_edge_def
    by simp

  then show ?thesis
    by simp
qed

lemma valid_subcircuit_output_interface_uses_qubit:
  assumes valid_subcircuit:
    "is_valid_subcircuit replacement"

  assumes output_interface:
    "output_interface replacement q = Some node_id"

  assumes operation_node:
    "nodes (subgraph replacement) node_id = Some (OperationNode op)"

  shows
    "q \<in> set (op_qargs op)"

proof -
  from valid_subcircuit output_interface
  have last_operation:
    "is_last_operation_on_subcircuit_wire replacement q node_id"
    unfolding is_valid_subcircuit_def
    by blast

  from last_operation have output_edge:
    "(node_id, get_output_node_id q) \<in> wire_edge_relation (subgraph replacement) q"
    unfolding is_last_operation_on_subcircuit_wire_def
    by blast

  then have edge_in_subgraph:
    "make_edge node_id (get_output_node_id q) q \<in> edges (subgraph replacement)"
    unfolding wire_edge_relation_def
    by simp

  from valid_subcircuit have valid_subgraph:
    "is_valid_circuit (subgraph replacement)"
    unfolding is_valid_subcircuit_def
    by simp

  from valid_subgraph have well_formed_subgraph:
    "is_well_formed_circuit (subgraph replacement)"
    unfolding is_valid_circuit_def
    by simp

  from well_formed_subgraph have well_formed_edges:
    "are_well_formed_edges (subgraph replacement)"
    unfolding is_well_formed_circuit_def
    by simp

  from well_formed_edges edge_in_subgraph
  have well_formed_output_edge:
    "is_well_formed_edge (subgraph replacement) (make_edge node_id (get_output_node_id q) q)"
    unfolding are_well_formed_edges_def
    by blast

  from well_formed_output_edge operation_node have
    "node_uses_qubit (OperationNode op) q"
    unfolding
      is_well_formed_edge_def
      make_edge_def
    by simp

  then show ?thesis
    by simp
qed

lemma replace_operation_by_subcircuit_preserves_well_formed_edges:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes acyclic_circuit:
    "is_acyclic_circuit circuit"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  shows
    "are_well_formed_edges (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement))"

proof -
  let ?result = "fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)"

  from valid_state have original_well_formed:
    "is_well_formed_circuit circuit"
    unfolding is_valid_construction_state_def
    by simp

  from original_well_formed have original_edges_well_formed:
    "are_well_formed_edges circuit"
    unfolding is_well_formed_circuit_def
    by simp

  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode original_op)"
  and replacement_valid:
      "is_valid_subcircuit replacement"
  and same_num_qubits:
      "num_qubits (subgraph replacement) = num_qubits circuit"
  and compatible:
      "is_compatible_subcircuit (op_qargs original_op) replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  from replacement_valid have replacement_valid_circuit:
    "is_valid_circuit (subgraph replacement)"
    unfolding is_valid_subcircuit_def
    by simp

  from replacement_valid_circuit have replacement_well_formed:
    "is_well_formed_circuit (subgraph replacement)"
    unfolding is_valid_circuit_def
    by simp

  from replacement_well_formed have replacement_edges_well_formed:
    "are_well_formed_edges (subgraph replacement)"
    unfolding is_well_formed_circuit_def
    by simp

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

  let ?connect_input = "connect_subcircuit_input_on_wire circuit operation_node_id replacement"

  let ?connect_output = "connect_subcircuit_output_on_wire circuit operation_node_id replacement"

  have input_fold_preserves_num_qubits:
    "finite interface_qubits \<Longrightarrow>
         num_qubits (Finite_Set.fold ?connect_input current_circuit interface_qubits)
       = num_qubits current_circuit"

    for interface_qubits current_circuit

  proof (induction interface_qubits arbitrary: current_circuit rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_input current_circuit (insert q interface_qubits)
       = ?connect_input q (Finite_Set.fold ?connect_input current_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have output_fold_preserves_num_qubits:
    "finite interface_qubits \<Longrightarrow>
      num_qubits (Finite_Set.fold ?connect_output current_circuit interface_qubits) = num_qubits current_circuit"

    for interface_qubits current_circuit

  proof (induction interface_qubits arbitrary: current_circuit
           rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold ?connect_output current_circuit (insert q interface_qubits)
       = ?connect_output q (Finite_Set.fold ?connect_output current_circuit interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have result_num_qubits:
    "num_qubits ?result = num_qubits circuit"
  proof -
    let ?circuit1 = "remove_operation_node circuit operation_node_id"

    let ?circuit2 = "insert_subcircuit_nodes circuit ?circuit1 replacement"

    let ?circuit3 = "insert_subcircuit_internal_edges circuit ?circuit2 replacement"

    let ?circuit4 = "connect_subcircuit_inputs circuit ?circuit3 operation_node_id replacement"

    let ?circuit5 = "connect_subcircuit_outputs circuit ?circuit4 operation_node_id replacement"

    have inputs_preserve_num_qubits:
      "num_qubits ?circuit4 = num_qubits ?circuit3"
      unfolding connect_subcircuit_inputs_def
      using
        finite_interfaces
        input_fold_preserves_num_qubits
      by blast

    have outputs_preserve_num_qubits:
      "num_qubits ?circuit5 = num_qubits ?circuit4"
      unfolding connect_subcircuit_outputs_def
      using
        finite_interfaces
        output_fold_preserves_num_qubits
      by blast

    show ?thesis
      unfolding
        replace_operation_by_subcircuit_def
        Let_def
      using
        inputs_preserve_num_qubits
        outputs_preserve_num_qubits
      by simp
  qed

  have preserve_original_well_formed_edge:
    "e \<in> edges circuit
     \<Longrightarrow> edge_source e \<noteq> operation_node_id
     \<Longrightarrow> edge_target e \<noteq> operation_node_id
     \<Longrightarrow> is_well_formed_edge ?result e"
    for e
    using
      are_well_formed_edges_def
      domIff
      is_well_formed_edge_def
      node_exists_def
      original_edges_well_formed
      qubit_in_circuit_def
      replace_operation_by_subcircuit_preserves_unrelated_nodes
      result_num_qubits
      valid_replacement
      valid_state
    by auto

  have renamed_internal_edge_well_formed:
    "renamed_edge \<in> (renamed_subcircuit_internal_edges circuit replacement)
       \<Longrightarrow> is_well_formed_edge ?result renamed_edge"
    for renamed_edge
  proof -
    assume renamed_edge:
      "renamed_edge \<in> renamed_subcircuit_internal_edges circuit replacement"

    then obtain local_edge where
      local_edge:
        "local_edge \<in> subcircuit_internal_edges replacement"
    and renamed_edge_eq:
        "renamed_edge = rename_subcircuit_edge circuit local_edge"
      unfolding renamed_subcircuit_internal_edges_def
      by blast

    from local_edge have local_edge_in_graph:
      "local_edge \<in> edges (subgraph replacement)"
      unfolding subcircuit_internal_edges_def
      by simp

    from replacement_edges_well_formed local_edge_in_graph
    have local_edge_well_formed:
      "is_well_formed_edge (subgraph replacement) local_edge"
      unfolding are_well_formed_edges_def
      by blast

    from local_edge have source_allocated:
      "edge_source local_edge \<in> subcircuit_operation_node_ids replacement"
    and target_allocated:
      "edge_target local_edge \<in> subcircuit_operation_node_ids replacement"
      unfolding subcircuit_internal_edges_def
      by auto

    from local_edge_well_formed obtain source_node target_node where
      local_source:
        "nodes (subgraph replacement) (edge_source local_edge) = Some source_node"
    and local_target:
        "nodes (subgraph replacement) (edge_target local_edge) = Some target_node"
    and local_valid_wire:
        "qubit_in_circuit (subgraph replacement) (edge_wire local_edge)"
    and source_uses_wire:
        "node_uses_qubit source_node (edge_wire local_edge)"
    and target_uses_wire:
        "node_uses_qubit target_node (edge_wire local_edge)"
      unfolding
        is_well_formed_edge_def
        node_exists_def
      by (auto split: option.splits)

    from source_allocated obtain source_op where
      source_operation:
        "nodes (subgraph replacement) (edge_source local_edge) = Some (OperationNode source_op)"
      unfolding
        subcircuit_operation_node_ids_def
        operation_node_ids_def
      by blast

    from target_allocated obtain target_op where
      target_operation:
        "nodes (subgraph replacement) (edge_target local_edge) = Some (OperationNode target_op)"
      unfolding
        subcircuit_operation_node_ids_def
        operation_node_ids_def
      by blast

    have source_node_eq:
      "source_node = OperationNode source_op"
      using local_source source_operation
      by simp

    have target_node_eq:
      "target_node = OperationNode target_op"
      using local_target target_operation
      by simp

    have renamed_source:
      "nodes ?result (rename_subcircuit_node_id circuit (edge_source local_edge)) = Some (OperationNode source_op)"
      using
         finite_interfaces
         replace_operation_by_subcircuit_contains_renamed_nodes
         source_allocated
         source_operation
      by simp

    have renamed_target:
      "nodes ?result (rename_subcircuit_node_id circuit (edge_target local_edge)) = Some (OperationNode target_op)"
      using
         finite_interfaces
         replace_operation_by_subcircuit_contains_renamed_nodes
         target_allocated
         target_operation
      by simp

    have result_valid_wire:
      "qubit_in_circuit ?result (edge_wire local_edge)"
      using
        local_valid_wire
        same_num_qubits
        result_num_qubits
      unfolding qubit_in_circuit_def
      by simp

    show
      "is_well_formed_edge ?result renamed_edge"
      unfolding
        renamed_edge_eq
        rename_subcircuit_edge_def
        make_edge_def
        is_well_formed_edge_def
        node_exists_def
      using
        renamed_source
        renamed_target
        result_valid_wire
        source_uses_wire
        target_uses_wire
        source_node_eq
        target_node_eq
      by simp
  qed

  have input_connection_well_formed:
    "q \<in> subcircuit_interface_qubits replacement
     \<Longrightarrow> predecessor_on_wire circuit operation_node_id q = Some predecessor_node
     \<Longrightarrow> renamed_input_interface circuit replacement q = Some renamed_input_node
     \<Longrightarrow> is_well_formed_edge ?result (make_edge predecessor_node renamed_input_node q)"
    for q predecessor_node renamed_input_node
  proof -

    assume interface_qubit:
      "q \<in> subcircuit_interface_qubits replacement"

    assume predecessor:
      "predecessor_on_wire circuit operation_node_id q = Some predecessor_node"

    assume renamed_input:
      "renamed_input_interface circuit replacement q = Some renamed_input_node"

    from predecessor_on_wire_correct[OF predecessor]
    have predecessor_edge:
      "make_edge predecessor_node operation_node_id q \<in> edges circuit"
      by simp

    from original_edges_well_formed predecessor_edge
    have predecessor_edge_well_formed:
      "is_well_formed_edge circuit (make_edge predecessor_node operation_node_id q)"
      unfolding are_well_formed_edges_def
      by blast

    from predecessor_edge_well_formed obtain predecessor_node_value where
      predecessor_node_value:
        "nodes circuit predecessor_node = Some predecessor_node_value"
    and predecessor_uses_wire:
        "node_uses_qubit predecessor_node_value q"
    and valid_wire:
        "qubit_in_circuit circuit q"
      unfolding
        is_well_formed_edge_def
        node_exists_def
        make_edge_def
      by (auto split: option.splits)

    have predecessor_not_removed:
      "predecessor_node \<noteq> operation_node_id"
      using
        acyclic_circuit
        predecessor
        predecessor_on_wire_not_self
      by simp

    have result_predecessor:
      "nodes ?result predecessor_node = Some predecessor_node_value"
      using
        replace_operation_by_subcircuit_preserves_unrelated_nodes[
          OF valid_state
             valid_replacement
             predecessor_not_removed
             predecessor_node_value]
      by simp

    from renamed_input obtain local_input_node where
      input_interface:
        "input_interface replacement q = Some local_input_node"
    and renamed_input_node_eq:
        "renamed_input_node = rename_subcircuit_node_id circuit local_input_node"
      unfolding renamed_input_interface_def
      by (cases "input_interface replacement q") auto

    from replacement_valid input_interface
    obtain input_op where
      input_operation:
        "nodes (subgraph replacement) local_input_node = Some (OperationNode input_op)"
      unfolding
        is_valid_subcircuit_def
        is_first_operation_on_subcircuit_wire_def
      by blast

    have input_allocated:
      "local_input_node \<in> subcircuit_operation_node_ids replacement"
      using input_operation
      unfolding
        subcircuit_operation_node_ids_def
        operation_node_ids_def
      by blast

    have input_uses_wire:
      "node_uses_qubit (OperationNode input_op) q"
      using
        valid_subcircuit_input_interface_uses_qubit[
          OF replacement_valid
             input_interface
             input_operation]
      by simp

    have result_input:
      "nodes ?result renamed_input_node = Some (OperationNode input_op)"
      using
        finite_interfaces
        input_allocated
        input_operation
        replace_operation_by_subcircuit_contains_renamed_nodes
      unfolding renamed_input_node_eq
      by simp

    have result_valid_wire:
      "qubit_in_circuit ?result q"
      using valid_wire result_num_qubits
      unfolding qubit_in_circuit_def
      by simp

    show ?thesis
      unfolding
        is_well_formed_edge_def
        node_exists_def
        make_edge_def
      using
        result_predecessor
        result_input
        result_valid_wire
        predecessor_uses_wire
        input_uses_wire
      by simp
  qed

  have output_connection_well_formed:
    "q \<in> subcircuit_interface_qubits replacement
     \<Longrightarrow> renamed_output_interface circuit replacement q = Some renamed_output_node
     \<Longrightarrow> successor_on_wire circuit operation_node_id q = Some successor_node
     \<Longrightarrow> is_well_formed_edge ?result (make_edge renamed_output_node successor_node q)"
    for q renamed_output_node successor_node
  proof -
    assume interface_qubit:
      "q \<in> subcircuit_interface_qubits replacement"

    assume renamed_output:
      "renamed_output_interface circuit replacement q = Some renamed_output_node"

    assume successor:
      "successor_on_wire circuit operation_node_id q = Some successor_node"

    from successor_on_wire_correct[OF successor]
    have successor_edge:
      "make_edge operation_node_id successor_node q \<in> edges circuit"
      by simp

    from original_edges_well_formed successor_edge
    have successor_edge_well_formed:
      "is_well_formed_edge circuit (make_edge operation_node_id successor_node q)"
      unfolding are_well_formed_edges_def
      by blast

    from successor_edge_well_formed
    obtain successor_node_value where
      successor_node_value:
        "nodes circuit successor_node = Some successor_node_value"
    and successor_uses_wire:
        "node_uses_qubit successor_node_value q"
    and valid_wire:
        "qubit_in_circuit circuit q"
      unfolding
        is_well_formed_edge_def
        node_exists_def
        make_edge_def
      by (auto split: option.splits)

    have successor_not_removed:
      "successor_node \<noteq> operation_node_id"
      using
        acyclic_circuit
        successor
        successor_on_wire_not_self
      by auto

    have result_successor:
      "nodes ?result successor_node = Some successor_node_value"
      using
        replace_operation_by_subcircuit_preserves_unrelated_nodes[
          OF valid_state
             valid_replacement
             successor_not_removed
             successor_node_value]
      by simp

    from renamed_output
    obtain local_output_node where
      output_interface:
        "output_interface replacement q = Some local_output_node"
    and renamed_output_node_eq:
        "renamed_output_node = rename_subcircuit_node_id circuit local_output_node"
      unfolding renamed_output_interface_def
      by (cases "output_interface replacement q") auto

    from replacement_valid output_interface
    obtain output_op where
      output_operation:
        "nodes (subgraph replacement) local_output_node = Some (OperationNode output_op)"
      unfolding
        is_valid_subcircuit_def
        is_last_operation_on_subcircuit_wire_def
      by blast

    have output_allocated:
      "local_output_node \<in> subcircuit_operation_node_ids replacement"
      using output_operation
      unfolding
        subcircuit_operation_node_ids_def
        operation_node_ids_def
      by blast

    have output_uses_wire:
      "node_uses_qubit (OperationNode output_op) q"
      using
        valid_subcircuit_output_interface_uses_qubit[
          OF replacement_valid
             output_interface
             output_operation]
      by simp

    have result_output:
      "nodes ?result renamed_output_node = Some (OperationNode output_op)"
      using
        finite_interfaces
        output_allocated
        output_operation
        renamed_output_node_eq
        replace_operation_by_subcircuit_contains_renamed_nodes
      by simp

    have result_valid_wire:
      "qubit_in_circuit ?result q"
      using valid_wire result_num_qubits
      unfolding qubit_in_circuit_def
      by simp

    show ?thesis
      unfolding
        is_well_formed_edge_def
        node_exists_def
        make_edge_def
      using
        result_output
        result_successor
        result_valid_wire
        output_uses_wire
        successor_uses_wire
      by simp
  qed

  show ?thesis
    using
      input_connection_well_formed
      output_connection_well_formed
      preserve_original_well_formed_edge
      renamed_internal_edge_well_formed
      replace_operation_by_subcircuit_edge_cases
      valid_replacement
    unfolding are_well_formed_edges_def
    by blast
    
qed

lemma replace_operation_by_subcircuit_preserves_well_formed_circuit:
  (* Replacing an existing operation node by a valid compatible
       subcircuit preserves local circuit well-formedness.
  
       The replacement preserves the canonical boundary nodes of the
       surrounding circuit.
  
       Every surviving original operation node remains valid, and every
       operation node copied from the replacement subcircuit is valid for
       the surrounding circuit.
  
       Every resulting edge is well formed:
         - surviving original edges retain valid endpoints and wire labels;
         - renamed internal subcircuit edges connect renamed nodes that use
           the corresponding wire;
         - input-interface edges connect the original predecessor to the
           renamed subcircuit input node;
         - output-interface edges connect the renamed subcircuit output
           node to the original successor.
  
       Therefore, the resulting circuit has well-formed boundary nodes,
       edges, and operation nodes.
  *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes acyclic_circuit:
    "is_acyclic_circuit circuit"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  shows
    "is_well_formed_circuit (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement))"
  using
      acyclic_circuit
      is_well_formed_circuit_def
      replace_operation_by_subcircuit_preserves_boundary_nodes
      replace_operation_by_subcircuit_preserves_well_formed_edges
      replace_operation_by_subcircuit_preserves_well_formed_operation_nodes
      valid_replacement valid_state
  by simp

lemma valid_subcircuit_replacement_is_acyclic:
  (* A valid subcircuit replacement contains a valid replacement subgraph.

     Validity of the subcircuit includes validity of its underlying circuit,
     and validity of that circuit includes acyclicity. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  shows
    "is_acyclic_circuit (subgraph replacement)"
  using valid_replacement
  unfolding
    is_valid_subcircuit_replacement_def
    is_valid_subcircuit_def
    is_valid_circuit_def
  by auto

lemma injective_renaming_trancl_reflects_cycle:
  (* Let relation be an original directed graph relation, and let rename be
     an injective renaming of its vertices.

     If the graph obtained by renaming both endpoints of every edge contains
     a directed cycle, then the original relation also contains a directed
     cycle.

     First, we prove the stronger fact that every nonempty path in the
     renamed relation corresponds to a nonempty path in the original
     relation. Injectivity is needed when joining two consecutive renamed
     edges: if their shared renamed endpoint is equal, then their original
     endpoints must also be equal.

     Applying this fact to a renamed cycle gives an original path whose
     endpoints have the same renamed value. Injectivity then shows that the
     original endpoints are equal, producing an original cycle. *)
  assumes rename_injective:
    "inj rename"

  assumes renamed_cycle:
    "(renamed_node, renamed_node)
       \<in> {(rename source, rename target) |
          source target. (source, target) \<in> relation}\<^sup>+"

  shows
    "\<exists>local_node. (local_node, local_node) \<in> relation\<^sup>+"

proof -
  let ?renamed_relation = "{(rename source, rename target) | source target. (source, target) \<in> relation}"

  have reflect_renamed_path:
    "(renamed_source, renamed_target) \<in> ?renamed_relation\<^sup>+
     \<Longrightarrow> \<exists>local_source local_target.
         renamed_source = rename local_source
       \<and> renamed_target = rename local_target
       \<and> (local_source, local_target) \<in> relation\<^sup>+"
    for renamed_source renamed_target

  proof (induction rule: trancl_induct)
    case (base y)

    from base.hyps obtain local_source local_target where
      renamed_source_eq:
        "renamed_source = rename local_source"
    and y_eq:
        "y = rename local_target"
    and local_edge:
        "(local_source, local_target) \<in> relation"
      by blast

    have local_path:
      "(local_source, local_target) \<in> relation\<^sup>+"
      using local_edge
      by (rule trancl.r_into_trancl)

    show ?case
      using
        renamed_source_eq
        y_eq
        local_path
      by blast

  next
    case (step y z)

    from step.IH obtain local_source local_intermediate where
      renamed_source_eq:
        "renamed_source = rename local_source"
    and y_eq:
        "y = rename local_intermediate"
    and local_prefix:
        "(local_source, local_intermediate) \<in> relation\<^sup>+"
      by blast

    from step.hyps(2) obtain edge_source edge_target where
      y_edge_source:
        "y = rename edge_source"
    and z_eq:
        "z = rename edge_target"
    and local_edge:
        "(edge_source, edge_target) \<in> relation"
      by blast

    have same_renamed_intermediate:
      "rename local_intermediate = rename edge_source"
      using y_eq y_edge_source
      by simp

    from rename_injective same_renamed_intermediate have
      same_local_intermediate:
        "local_intermediate = edge_source"
      unfolding inj_def
      by blast

    have local_result_path:
      "(local_source, edge_target) \<in> relation\<^sup>+"
      using
        local_edge
        local_prefix
        same_local_intermediate
      by auto

    show ?case
      using
        renamed_source_eq
        z_eq
        local_result_path
      by auto
  qed

  from reflect_renamed_path[OF renamed_cycle]
  obtain local_source local_target where
    renamed_source_eq:
      "renamed_node = rename local_source"
  and renamed_target_eq:
      "renamed_node = rename local_target"
  and local_path:
      "(local_source, local_target) \<in> relation\<^sup>+"
    by blast

  have same_renamed_endpoint:
    "rename local_source = rename local_target"
    using
      renamed_source_eq
      renamed_target_eq
    by simp

  from rename_injective same_renamed_endpoint have
    same_local_endpoint:
      "local_source = local_target"
    unfolding inj_def
    by simp

  show ?thesis
    using
      local_path
      same_local_endpoint
    by auto
qed

lemma renamed_internal_cycle_implies_subcircuit_cycle:
  (* A cycle consisting entirely of renamed internal replacement edges
     corresponds to a cycle in the original replacement subgraph.

     Each renamed edge comes from an internal edge of the replacement.
     Injectivity of rename_subcircuit_node_id on allocated replacement
     operation nodes ensures that the endpoints can be transferred back
     consistently. *)
  assumes internal_cycle:
    "(renamed_node, renamed_node)
       \<in> {(edge_source e, edge_target e) | e. e \<in> renamed_subcircuit_internal_edges circuit replacement}\<^sup>+"

  shows
    "\<exists>local_node. (local_node, local_node) \<in> (edge_relation (subgraph replacement))\<^sup>+"

proof -
  let ?rename = "rename_subcircuit_node_id circuit"

  let ?internal_relation =
    "{(edge_source e, edge_target e) | e.  e \<in> subcircuit_internal_edges replacement}"

  have rename_injective:
    "inj ?rename"
    unfolding inj_def
    using rename_subcircuit_node_id_injective
    by blast

  have renamed_relation_eq:
    "{(edge_source e, edge_target e) | e. e \<in> renamed_subcircuit_internal_edges circuit replacement}
     = {(?rename source, ?rename target) | source target. (source, target) \<in> ?internal_relation}"

  proof (rule set_eqI)
    fix renamed_pair

    show
      "renamed_pair \<in> {(edge_source e, edge_target e) | e. e \<in> renamed_subcircuit_internal_edges circuit replacement}
       \<longleftrightarrow> renamed_pair \<in> {(?rename source, ?rename target) | source target. (source, target) \<in> ?internal_relation}"
    proof
      assume renamed_pair_in:
        "renamed_pair \<in> {(edge_source e, edge_target e) | e. e \<in> renamed_subcircuit_internal_edges circuit replacement}"

      then obtain renamed_edge where
        renamed_edge:
          "renamed_edge \<in> renamed_subcircuit_internal_edges circuit replacement"
      and renamed_pair_eq:
          "renamed_pair = (edge_source renamed_edge, edge_target renamed_edge)"
        by auto

      from renamed_edge obtain local_edge where
        local_edge:
          "local_edge \<in> subcircuit_internal_edges replacement"
      and renamed_edge_eq:
          "renamed_edge = rename_subcircuit_edge circuit local_edge"
        unfolding renamed_subcircuit_internal_edges_def
        by auto

      have local_pair:
        "(edge_source local_edge, edge_target local_edge) \<in> ?internal_relation"
        using local_edge
        by auto

      show
        "renamed_pair \<in> {(?rename source, ?rename target) | source target. (source, target) \<in> ?internal_relation}"
        using
          renamed_pair_eq
          renamed_edge_eq
          local_pair
        unfolding
          rename_subcircuit_edge_def
          make_edge_def
        by auto

    next
      assume renamed_pair_in:
        "renamed_pair \<in> {(?rename source, ?rename target) | source target. (source, target) \<in> ?internal_relation}"

      then obtain source target where
        local_pair:
          "(source, target) \<in> ?internal_relation"
      and renamed_pair_eq:
          "renamed_pair = (?rename source, ?rename target)"
        by auto

      from local_pair obtain local_edge where
        local_edge:
          "local_edge \<in> subcircuit_internal_edges replacement"
      and source_eq:
          "source = edge_source local_edge"
      and target_eq:
          "target = edge_target local_edge"
        by auto

      have renamed_edge:
        "rename_subcircuit_edge circuit local_edge \<in> renamed_subcircuit_internal_edges circuit replacement"
        using local_edge
        unfolding renamed_subcircuit_internal_edges_def
        by simp

      show
        "renamed_pair \<in> {(edge_source e, edge_target e) | e. e \<in> renamed_subcircuit_internal_edges circuit replacement}"
        using
          renamed_edge
          renamed_pair_eq
          source_eq
          target_eq
        unfolding
          rename_subcircuit_edge_def
          make_edge_def
        by force
    qed
  qed

  from internal_cycle have renamed_internal_relation_cycle:
    "(renamed_node, renamed_node) \<in> {(?rename source, ?rename target) | 
          source target. (source, target) \<in> ?internal_relation}\<^sup>+"
    unfolding renamed_relation_eq
    by simp

  from injective_renaming_trancl_reflects_cycle[OF
      rename_injective
      renamed_internal_relation_cycle]
  obtain local_node where
    local_internal_cycle:
      "(local_node, local_node) \<in> ?internal_relation\<^sup>+"
    by auto

  have internal_relation_subset:
    "?internal_relation \<subseteq> edge_relation (subgraph replacement)"
  proof
    fix pair

    assume pair_in:
      "pair \<in> ?internal_relation"

    then obtain local_edge where
      local_edge:
        "local_edge \<in> subcircuit_internal_edges replacement"
    and pair_eq:
        "pair = (edge_source local_edge, edge_target local_edge)"
      by auto

    from local_edge have
      "local_edge \<in> edges (subgraph replacement)"
      unfolding subcircuit_internal_edges_def
      by simp

    then show
      "pair \<in> edge_relation (subgraph replacement)"
      using pair_eq
      unfolding edge_relation_def
      by auto
  qed

  have
    "?internal_relation\<^sup>+ \<subseteq> (edge_relation (subgraph replacement))\<^sup>+"
    
    using internal_relation_subset 
    by (simp add: trancl_mono_subset)

  with local_internal_cycle show ?thesis
    by auto
qed

lemma replacement_cycle_internal_or_original:
  (* Every cycle in the replacement result has one of two forms.

     Internal case:
       Every edge used by the cycle is a renamed internal edge of the
       replacement subcircuit. Hence the renamed internal-edge relation
       itself contains a cycle.

     External case:
       The cycle contains at least one surviving original edge or one of the
       newly inserted input/output interface edges.

       In this case, collapse every maximal path through renamed replacement
       nodes back to operation_node_id:

         predecessor \<rightarrow> renamed input
           becomes
         predecessor \<rightarrow> operation_node_id

         renamed output \<rightarrow> successor
           becomes
         operation_node_id \<rightarrow> successor

       Surviving original edges remain unchanged. The collapsed nonempty
       result cycle therefore gives a nonempty cycle in the original circuit.

     This is the central path-decomposition argument for replacement
     acyclicity. *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  assumes result_cycle:
    "(node, node) 
       \<in> (edge_relation (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)))\<^sup>+"

  shows
    "(\<exists>original_node. (original_node, original_node) \<in> (edge_relation circuit)\<^sup>+)
   \<or> (\<exists>renamed_node. (renamed_node, renamed_node) \<in>
         {(edge_source e, edge_target e) | e. e \<in> renamed_subcircuit_internal_edges circuit replacement}\<^sup>+)"

  using
    valid_replacement
    result_cycle
    replace_operation_by_subcircuit_edge_cases

proof -
  let ?result = "fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)"

  let ?renamed_nodes = "rename_subcircuit_node_id circuit ` subcircuit_operation_node_ids replacement"

  let ?internal_relation =
    "{(edge_source e, edge_target e) | e. e \<in> renamed_subcircuit_internal_edges circuit replacement}"

  let ?collapse = "\<lambda>n.
       if n \<in> ?renamed_nodes
       then operation_node_id
       else n"

  from valid_state have original_well_formed:
    "is_well_formed_circuit circuit"
    unfolding is_valid_construction_state_def
    by simp

  from original_well_formed have original_edges_well_formed:
    "are_well_formed_edges circuit"
    unfolding is_well_formed_circuit_def
    by simp

  from valid_state have allocation:
    "all_existing_node_ids_below_next_id circuit"
    unfolding is_valid_construction_state_def
    by simp

  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id = Some (OperationNode original_op)"
  and replacement_valid:
      "is_valid_subcircuit replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have renamed_fresh:
    "local_node \<in> subcircuit_operation_node_ids replacement \<Longrightarrow> 
           nodes circuit (rename_subcircuit_node_id circuit local_node) = None"
    for local_node
    using allocation
    by (metis
        all_existing_node_ids_below_next_id_def
        linorder_not_less
        renamed_subcircuit_node_id_is_unused)


  have existing_node_not_renamed:
    "nodes circuit original_node \<noteq> None \<Longrightarrow> original_node \<notin> ?renamed_nodes"
    for original_node
    using renamed_fresh
    by fastforce


  have result_edge_cases:
    "(u, v) \<in> edge_relation ?result \<Longrightarrow> 
         ((u, v) \<in> ?internal_relation)
       \<or> ((?collapse u, ?collapse v) \<in> edge_relation circuit)"
    for u v
  proof -
    assume result_relation:
      "(u, v) \<in> edge_relation ?result"

    then obtain e where
      edge_in_result:
        "e \<in> edges ?result"
    and source_eq:
        "u = edge_source e"
    and target_eq:
        "v = edge_target e"
      unfolding edge_relation_def
      by blast

    from replace_operation_by_subcircuit_edge_cases[OF
        valid_replacement
        edge_in_result]
    show ?thesis
    proof
      assume original_case:
        "e \<in> edges circuit
         \<and> edge_source e \<noteq> operation_node_id
         \<and> edge_target e \<noteq> operation_node_id"

      then have original_edge:
        "e \<in> edges circuit"
        by simp

      from original_edges_well_formed original_edge
      have edge_well_formed:
        "is_well_formed_edge circuit e"
        unfolding are_well_formed_edges_def
        by blast

      from edge_well_formed have source_exists:
        "nodes circuit (edge_source e) \<noteq> None"
      and target_exists:
        "nodes circuit (edge_target e) \<noteq> None"
        unfolding
          is_well_formed_edge_def
          node_exists_def
        by simp_all

      have source_not_renamed:
        "edge_source e \<notin> ?renamed_nodes"
        using source_exists
        by (rule existing_node_not_renamed)

      have target_not_renamed:
        "edge_target e \<notin> ?renamed_nodes"
        using target_exists
        by (rule existing_node_not_renamed)

      have original_relation:
        "(edge_source e, edge_target e) \<in> edge_relation circuit"
        using original_edge
        unfolding edge_relation_def
        by blast

      show ?thesis
        using
          original_relation
          source_eq
          target_eq
          source_not_renamed
          target_not_renamed
        by simp

    next

      assume remaining_cases:
        "e \<in> renamed_subcircuit_internal_edges circuit replacement
         \<or>
         (\<exists>q predecessor_node renamed_input_node.
            q \<in> subcircuit_interface_qubits replacement
            \<and> predecessor_on_wire circuit operation_node_id q = Some predecessor_node
            \<and> renamed_input_interface circuit replacement q = Some renamed_input_node
            \<and> e = make_edge predecessor_node renamed_input_node q)
         \<or>
         (\<exists>q renamed_output_node successor_node.
            q \<in> subcircuit_interface_qubits replacement
            \<and> renamed_output_interface circuit replacement q = Some renamed_output_node
            \<and> successor_on_wire circuit operation_node_id q = Some successor_node
            \<and> e = make_edge renamed_output_node successor_node q)"

      from remaining_cases show ?thesis
      proof
        assume internal_edge:
          "e \<in> renamed_subcircuit_internal_edges circuit replacement"

        have
          "(edge_source e, edge_target e) \<in> ?internal_relation"
          using internal_edge
          by blast

        then show ?thesis
          using source_eq target_eq
          by simp

      next
        assume connection_cases:
          "(\<exists>q predecessor_node renamed_input_node.
              q \<in> subcircuit_interface_qubits replacement 
              \<and> predecessor_on_wire circuit operation_node_id q = Some predecessor_node
              \<and> renamed_input_interface circuit replacement q = Some renamed_input_node
              \<and> e = make_edge predecessor_node renamed_input_node q)
           \<or>
           (\<exists>q renamed_output_node successor_node.
              q \<in> subcircuit_interface_qubits replacement
              \<and> renamed_output_interface circuit replacement q = Some renamed_output_node
              \<and> successor_on_wire circuit operation_node_id q = Some successor_node
              \<and> e = make_edge renamed_output_node successor_node q)"

        from connection_cases show ?thesis
        proof
          assume input_case:
            "\<exists>q predecessor_node renamed_input_node.
               q \<in> subcircuit_interface_qubits replacement
               \<and> predecessor_on_wire circuit operation_node_id q = Some predecessor_node
               \<and> renamed_input_interface circuit replacement q = Some renamed_input_node
               \<and> e = make_edge predecessor_node renamed_input_node q"

          then obtain q predecessor_node renamed_input_node where
            predecessor:
              "predecessor_on_wire circuit operation_node_id q = Some predecessor_node"
          and renamed_input:
              "renamed_input_interface circuit replacement q = Some renamed_input_node"
          and edge_eq:
              "e = make_edge predecessor_node renamed_input_node q"
            by blast

          from predecessor_on_wire_correct[OF predecessor]
          have predecessor_edge:
            "make_edge predecessor_node operation_node_id q \<in> edges circuit" .

          from original_edges_well_formed predecessor_edge
          have predecessor_edge_well_formed:
            "is_well_formed_edge circuit (make_edge predecessor_node operation_node_id q)"
            unfolding are_well_formed_edges_def
            by blast

          from predecessor_edge_well_formed have predecessor_exists:
            "nodes circuit predecessor_node \<noteq> None"
            unfolding
              is_well_formed_edge_def
              node_exists_def
              make_edge_def
            by simp

          have predecessor_not_renamed:
            "predecessor_node \<notin> ?renamed_nodes"
            using predecessor_exists
            by (rule existing_node_not_renamed)

          from renamed_input obtain local_input_node where
            input_interface:
              "input_interface replacement q = Some local_input_node"
          and renamed_input_eq:
              "renamed_input_node = rename_subcircuit_node_id circuit local_input_node"
            unfolding renamed_input_interface_def
            by (cases "input_interface replacement q") auto

          from replacement_valid input_interface
          obtain input_op where
            input_operation:
              "nodes (subgraph replacement) local_input_node = Some (OperationNode input_op)"
            unfolding
              is_valid_subcircuit_def
              is_first_operation_on_subcircuit_wire_def
            by blast

          have input_allocated:
            "local_input_node \<in> subcircuit_operation_node_ids replacement"
            using input_operation
            unfolding
              subcircuit_operation_node_ids_def
              operation_node_ids_def
            by blast

          have renamed_input_in:
            "renamed_input_node \<in> ?renamed_nodes"
            using
              input_allocated
              renamed_input_eq
            by blast

          have collapsed_original_edge:
            "(?collapse predecessor_node, ?collapse renamed_input_node) = (predecessor_node, operation_node_id)"
            using
              predecessor_not_renamed
              renamed_input_in
            by simp

          have original_relation:
            "(predecessor_node, operation_node_id) \<in> edge_relation circuit"
            using predecessor_edge
            unfolding
              edge_relation_def
              make_edge_def
            by force

          show ?thesis
            using
              source_eq
              target_eq
              edge_eq
              collapsed_original_edge
              original_relation
            unfolding make_edge_def
            by auto

        next
          assume output_case:
            "\<exists>q renamed_output_node successor_node.
               q \<in> subcircuit_interface_qubits replacement
               \<and> renamed_output_interface circuit replacement q = Some renamed_output_node
               \<and> successor_on_wire circuit operation_node_id q = Some successor_node
               \<and> e = make_edge renamed_output_node successor_node q"

          then obtain q renamed_output_node successor_node where
            renamed_output:
              "renamed_output_interface circuit replacement q = Some renamed_output_node"
          and successor:
              "successor_on_wire circuit operation_node_id q = Some successor_node"
          and edge_eq:
              "e = make_edge renamed_output_node successor_node q"
            by blast

          from successor_on_wire_correct[OF successor]
          have successor_edge:
            "make_edge operation_node_id successor_node q \<in> edges circuit"
            by simp

          from original_edges_well_formed successor_edge
          have successor_edge_well_formed:
            "is_well_formed_edge circuit (make_edge operation_node_id successor_node q)"
            unfolding are_well_formed_edges_def
            by blast

          from successor_edge_well_formed have successor_exists:
            "nodes circuit successor_node \<noteq> None"
            unfolding
              is_well_formed_edge_def
              node_exists_def
              make_edge_def
            by simp

          have successor_not_renamed:
            "successor_node \<notin> ?renamed_nodes"
            using successor_exists
            by (rule existing_node_not_renamed)

          from renamed_output obtain local_output_node where
            output_interface:
              "output_interface replacement q = Some local_output_node"
          and renamed_output_eq:
              "renamed_output_node = rename_subcircuit_node_id circuit local_output_node"
            unfolding renamed_output_interface_def
            by (cases "output_interface replacement q") auto

          from replacement_valid output_interface
          obtain output_op where
            output_operation:
              "nodes (subgraph replacement) local_output_node = Some (OperationNode output_op)"
            unfolding
              is_valid_subcircuit_def
              is_last_operation_on_subcircuit_wire_def
            by blast

          have output_allocated:
            "local_output_node \<in> subcircuit_operation_node_ids replacement"
            using output_operation
            unfolding
              subcircuit_operation_node_ids_def
              operation_node_ids_def
            by blast

          have renamed_output_in:
            "renamed_output_node \<in> ?renamed_nodes"
            using
              output_allocated
              renamed_output_eq
            by blast

          have collapsed_original_edge:
            "(?collapse renamed_output_node, ?collapse successor_node) = (operation_node_id, successor_node)"
            using
              renamed_output_in
              successor_not_renamed
            by simp

          have original_relation:
            "(operation_node_id, successor_node) \<in> edge_relation circuit"
            using successor_edge
            unfolding
              edge_relation_def
              make_edge_def
            by force

          show ?thesis
            using
              source_eq
              target_eq
              edge_eq
              collapsed_original_edge
              original_relation
            unfolding make_edge_def
            by auto
        qed
      qed
    qed
  qed

  have path_cases:
    "(u, v) \<in> (edge_relation ?result)\<^sup>+ \<Longrightarrow>
         (u, v) \<in> ?internal_relation\<^sup>+ \<or> (?collapse u, ?collapse v) \<in> (edge_relation circuit)\<^sup>+"
    for u v
  proof (induction rule: trancl_induct)
    case (base v)

    from result_edge_cases[OF base.hyps]
    show ?case
      by auto

  next
    case (step v w)

    from step.IH show ?case
    proof
      assume prefix_internal:
        "(u, v) \<in> ?internal_relation\<^sup>+"

      from result_edge_cases[OF step.hyps(2)]
      show ?case
      proof
        assume final_internal:
          "(v, w) \<in> ?internal_relation"

        have
          "(u, w) \<in> ?internal_relation\<^sup>+"
          using prefix_internal final_internal
          by (rule trancl_into_trancl)

        then show ?case
          by blast

      next
        assume final_original:
          "(?collapse v, ?collapse w) \<in> edge_relation circuit"

        have internal_endpoints_renamed:
          "u \<in> ?renamed_nodes
         \<and> v \<in> ?renamed_nodes"
        proof -
          from prefix_internal obtain next_e where
            first_edge:
              "(u, next_e) \<in> ?internal_relation"
            by (meson tranclD)

          from first_edge have
            "u \<in> ?renamed_nodes"
            unfolding
              renamed_subcircuit_internal_edges_def
              rename_subcircuit_edge_def
              subcircuit_internal_edges_def
              make_edge_def
            by auto

          moreover from prefix_internal obtain previous where
            last_edge:
              "(previous, v) \<in> ?internal_relation"
            by (meson trancl.cases)

          from last_edge have
            "v \<in> ?renamed_nodes"
            unfolding
              renamed_subcircuit_internal_edges_def
              rename_subcircuit_edge_def
              subcircuit_internal_edges_def
              make_edge_def
            by auto

          ultimately show ?thesis
            by blast
        qed

        then have collapse_uv:
          "?collapse u = operation_node_id"
          "?collapse v = operation_node_id"
          by simp_all

        have
          "(?collapse u, ?collapse w) \<in> (edge_relation circuit)\<^sup>+"
          using final_original collapse_uv
          by auto 

        then show ?case
          by blast
      qed

    next
      assume prefix_original:
        "(?collapse u, ?collapse v) \<in> (edge_relation circuit)\<^sup>+"

      from result_edge_cases[OF step.hyps(2)]
      show ?case
      proof
        assume final_internal:
          "(v, w) \<in> ?internal_relation"

        from final_internal have
          "v \<in> ?renamed_nodes"
          "w \<in> ?renamed_nodes"
          unfolding
            renamed_subcircuit_internal_edges_def
            rename_subcircuit_edge_def
            subcircuit_internal_edges_def
            make_edge_def
          by auto

        then have collapse_vw:
          "?collapse v = ?collapse w"
          by simp

        have
          "(?collapse u, ?collapse w) \<in> (edge_relation circuit)\<^sup>+"
          using prefix_original collapse_vw
          by simp

        then show ?case
          by blast

      next
        assume final_original:
          "(?collapse v, ?collapse w) \<in> edge_relation circuit"

        have
          "(?collapse u, ?collapse w)\<in> (edge_relation circuit)\<^sup>+"
          using prefix_original final_original
          by (rule trancl_into_trancl)

        then show ?case
          by blast
      qed
    qed
  qed

  from path_cases[OF result_cycle]
  
  show ?thesis
    by auto

qed

lemma replacement_cycle_cases:
  (* Every directed cycle created by subcircuit replacement has one of two
     origins.

     Case 1: The cycle leaves the renamed replacement region.

       Every surviving original edge remains an original edge.
       Every input reconnection

           predecessor \<rightarrow> renamed-input

       can be collapsed back to

           predecessor \<rightarrow> operation_node_id.

       Every output reconnection

           renamed-output \<rightarrow> successor

       can be collapsed back to

           operation_node_id \<rightarrow> successor.

       Every maximal path through renamed internal nodes is therefore
       collapsed to the removed operation node. A cycle that enters or exits
       the replacement region consequently yields a nonempty cycle in the
       original circuit.

     Case 2: The cycle remains entirely inside the renamed replacement
     region.

       All of its edges are renamed internal replacement edges. By
       injectivity of the renaming operation, this yields a cycle in the
       original replacement subgraph.

     Thus a result cycle implies either an original-circuit cycle or a
     replacement-subgraph cycle. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes result_cycle:
    "(node, node) \<in> (edge_relation
          (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement)))\<^sup>+"

  shows
    "(\<exists>original_node. (original_node, original_node) \<in> (edge_relation circuit)\<^sup>+)
     \<or> (\<exists>replacement_node. (replacement_node, replacement_node) \<in> (edge_relation (subgraph replacement))\<^sup>+)"
  by (meson
      renamed_internal_cycle_implies_subcircuit_cycle
      replacement_cycle_internal_or_original
      result_cycle valid_replacement
      valid_state)

lemma replace_operation_by_subcircuit_preserves_acyclicity:
  (* Replacing an operation by a valid acyclic subcircuit preserves
     acyclicity.

     Suppose the resulting circuit contained a cycle. The cycle-decomposition
     lemma shows that this would imply either:

       1. a cycle in the original circuit, contradicting the original
          circuit's acyclicity; or

       2. a cycle in the replacement subgraph, contradicting validity of
          the replacement subcircuit.

     Therefore the replacement result is acyclic. *)

  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes original_acyclic:
    "is_acyclic_circuit circuit"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement circuit operation_node_id replacement"

  shows
    "is_acyclic_circuit 
       (fst (replace_operation_by_subcircuit circuit frontier operation_node_id replacement))"
  by (meson
      acyclic_def
      is_acyclic_circuit_def
      original_acyclic
      replacement_cycle_cases
      valid_replacement
      valid_state
      valid_subcircuit_replacement_is_acyclic)

end
