theory Quantum_Circuit_Operation_Replace
  imports Quantum_Circuit_Delete_Validity

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
  "replace_operation node_id replacement_op circuit =
     (
       case nodes circuit node_id of
         Some (OperationNode old_op) \<Rightarrow>
           insert_node node_id (OperationNode replacement_op) circuit
       | _ \<Rightarrow>
           circuit
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

     The equality of op_qargs is essential because replace_operation changes
     only the operation stored at the node and leaves the edge set unchanged.

     Therefore, every incoming and outgoing edge incident on the selected node
     remains labelled by a qubit used by the replacement operation. Changing
     the qubit interface would require rewiring the graph and should instead
     be handled by a separate graph transformation.
  *)
  "valid_operation_replacement
      circuit operation_node_id replacement_op
   \<longleftrightarrow>
     (\<exists>original_op.
        nodes circuit operation_node_id =
          Some (OperationNode original_op)
      \<and> operation_in_circuit circuit replacement_op
      \<and> op_qargs replacement_op = op_qargs original_op)"

lemma replace_operation_selected_node:
  (* If operation_node_id currently stores an operation node, then after
     replacement the same node ID stores the replacement operation. *)
  assumes operation_exists:
    "nodes circuit operation_node_id =
       Some (OperationNode original_op)"
  shows
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       operation_node_id
     =
     Some (OperationNode replacement_op)"

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
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       operation_node_id
     =
     Some (OperationNode replacement_op)"

proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
    unfolding valid_operation_replacement_def
    by blast

  show ?thesis
    using operation_exists
    by (rule replace_operation_selected_node)
qed

lemma replacement_preserves_other_nodes:
  (* Replacing the operation stored at operation_node_id does not change
     the node stored at any different node ID. *)
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"
  shows
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       other_node_id
     =
     nodes circuit other_node_id"

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
  "edges
     (replace_operation operation_node_id replacement_op circuit)
   =
   edges circuit"

  unfolding
    replace_operation_def
    insert_node_def
  by (auto split: option.splits circuit_node.splits)

lemma replacement_preserves_num_qubits:
  (* Replacing an operation does not change the number of qubits. *)
  "num_qubits
     (replace_operation operation_node_id replacement_op circuit)
   =
   num_qubits circuit"

  unfolding
    replace_operation_def
    insert_node_def
  by (auto split: option.splits circuit_node.splits)

lemma replacement_preserves_next_id:
  (* Replacing an operation does not allocate or remove node IDs. *)
  "next_id
     (replace_operation operation_node_id replacement_op circuit)
   =
   next_id circuit"

  unfolding
    replace_operation_def
    insert_node_def

  by (auto split: option.splits circuit_node.splits)

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
    "(case
        nodes
          (replace_operation
             operation_node_id
             replacement_op
             circuit)
          node_id
      of
        None \<Rightarrow> False
      | Some node \<Rightarrow> node_uses_qubit node q)
     =
     (case nodes circuit node_id of
        None \<Rightarrow> False
      | Some node \<Rightarrow> node_uses_qubit node q)"

proof -

  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
  and
    same_qargs:
      "op_qargs replacement_op = op_qargs original_op"
    unfolding valid_operation_replacement_def
    by blast

  show ?thesis
  proof (cases "node_id = operation_node_id")

    case True

    have replacement_node:
      "nodes
         (replace_operation
            operation_node_id
            replacement_op
            circuit)
         operation_node_id
       =
       Some (OperationNode replacement_op)"
      using operation_exists
      by (rule replace_operation_selected_node)

    show ?thesis
      using
        True
        operation_exists
        replacement_node
        same_qargs
      by simp

  next

    case False

    have node_unchanged:
      "nodes
         (replace_operation
            operation_node_id
            replacement_op
            circuit)
         node_id
       =
       nodes circuit node_id"
      using False
      by (rule replacement_preserves_other_nodes)

    show ?thesis
      using node_unchanged
      by simp

  qed

qed

lemma replacement_preserves_well_formed_circuit:
  (* Replacing an operation with another valid operation using the same
     qubits preserves the circuit's well-formedness. *)
  assumes
    well_formed:
      "is_well_formed_circuit circuit"
  and
    valid_replacement:
      "valid_operation_replacement
         circuit
         operation_node_id
         replacement_op"
  shows
    "is_well_formed_circuit
       (replace_operation
          operation_node_id
          replacement_op
          circuit)"

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
      using are_well_formed_boundary_nodes_def
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
    "are_well_formed_edges
       (replace_operation
          operation_node_id
          replacement_op
          circuit)"

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
        "e \<in>
           edges
             (replace_operation
                operation_node_id
                replacement_op
                circuit)"

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
        "is_well_formed_edge
           (replace_operation
              operation_node_id
              replacement_op
              circuit)
           e"

        unfolding is_well_formed_edge_def
      proof (intro conjI)

        from original_edge_well_formed
        have original_source_exists:
          "node_exists circuit (edge_source e)"
          unfolding is_well_formed_edge_def
          by simp

        show
          "node_exists
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             (edge_source e)"
        proof (cases "edge_source e = operation_node_id")
          case True
          have replaced_source:
            "nodes
               (replace_operation
                  operation_node_id
                  replacement_op
                  circuit)
               (edge_source e)
             =
             Some (OperationNode replacement_op)"
            using
              True
              valid_replacement
              valid_replacement_selected_node
            by simp
          show ?thesis
            unfolding node_exists_def
            using replaced_source
            by simp
        next
          case False
          have source_unchanged:
            "nodes
               (replace_operation
                  operation_node_id
                  replacement_op
                  circuit)
               (edge_source e)
             =
             nodes circuit (edge_source e)"
            using False
            by (rule replacement_preserves_other_nodes)

          show ?thesis
            using original_source_exists source_unchanged
            unfolding node_exists_def
            by simp
        qed
      next

        from original_edge_well_formed
        have original_target_exists:
          "node_exists circuit (edge_target e)"
          unfolding is_well_formed_edge_def
          by simp

        show
          "node_exists
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             (edge_target e)"
        
        proof (cases "edge_target e = operation_node_id")
          case True

          have replaced_target:
            "nodes
               (replace_operation
                  operation_node_id
                  replacement_op
                  circuit)
               (edge_target e)
             =
             Some (OperationNode replacement_op)"
            using
              True
              valid_replacement
              valid_replacement_selected_node
            by simp

          show ?thesis
            unfolding node_exists_def
            using replaced_target
            by simp

        next
          case False

          have target_unchanged:
            "nodes
               (replace_operation
                  operation_node_id
                  replacement_op
                  circuit)
               (edge_target e)
             =
             nodes circuit (edge_target e)"
            using False
            by (rule replacement_preserves_other_nodes)

          show ?thesis
            using
              original_target_exists
              target_unchanged
            unfolding node_exists_def
            by simp
        qed
      
      next
        from original_edge_well_formed
        have original_wire_exists:
          "qubit_in_circuit circuit (edge_wire e)"
          unfolding is_well_formed_edge_def
          by simp

        show
          "qubit_in_circuit
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             (edge_wire e)"
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
              nodes
                (replace_operation
                   operation_node_id
                   replacement_op
                   circuit)
                (edge_source e)
            of
              None \<Rightarrow> False
            | Some source_node \<Rightarrow>
                node_uses_qubit source_node (edge_wire e))
           =
           (case nodes circuit (edge_source e) of
              None \<Rightarrow> False
            | Some source_node \<Rightarrow>
                node_uses_qubit source_node (edge_wire e))"
          using 
            valid_replacement
            valid_replacement_preserves_node_wire_usage
          by simp

        show
          "case
             nodes
               (replace_operation
                  operation_node_id
                  replacement_op
                  circuit)
               (edge_source e)
           of
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
          "(case
              nodes
                (replace_operation
                   operation_node_id
                   replacement_op
                   circuit)
                (edge_target e)
            of
              None \<Rightarrow> False
            | Some target_node \<Rightarrow>
                node_uses_qubit target_node (edge_wire e))
           =
           (case nodes circuit (edge_target e) of
              None \<Rightarrow> False
            | Some target_node \<Rightarrow>
                node_uses_qubit target_node (edge_wire e))"
          using
            valid_replacement
            valid_replacement_preserves_node_wire_usage
          by simp

        show
          "case
             nodes
               (replace_operation
                  operation_node_id
                  replacement_op
                  circuit)
               (edge_target e)
           of
             None \<Rightarrow> False
           | Some target_node \<Rightarrow>
               node_uses_qubit target_node (edge_wire e)"
          using
            original_target_uses_wire
            target_wire_usage_preserved
          by simp
      qed
    qed
  qed

next
  show well_formed_op_nodes:
    "are_well_formed_operation_nodes
        (replace_operation
             operation_node_id
             replacement_op
             circuit)"
    proof -      
      from well_formed have original_operation_nodes:
        "are_well_formed_operation_nodes circuit"
        unfolding is_well_formed_circuit_def
        by simp

    from valid_replacement obtain original_op where
      operation_exists:
        "nodes circuit operation_node_id =
           Some (OperationNode original_op)"
    and
      replacement_in_circuit:
        "operation_in_circuit circuit replacement_op"

      unfolding valid_operation_replacement_def
      by blast

    show ?thesis
      unfolding are_well_formed_operation_nodes_def
    proof (intro allI impI)
      fix node_id op

      assume updated_operation_node:
        "nodes
           (replace_operation
              operation_node_id
              replacement_op
              circuit)
           node_id
         =
         Some (OperationNode op)"

      show
        "operation_in_circuit
           (replace_operation
              operation_node_id
              replacement_op
              circuit)
           op"

      proof (cases "node_id = operation_node_id")
        case True

        have selected_node:
          "nodes
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             operation_node_id
           =
           Some (OperationNode replacement_op)"
          using valid_replacement
          by (rule valid_replacement_selected_node)

        have operation_is_replacement:
          "op = replacement_op"
          using
            updated_operation_node
            selected_node
            True
          by simp

        show ?thesis
          using
            replacement_in_circuit
            operation_is_replacement
            replacement_preserves_num_qubits
          unfolding
            operation_in_circuit_def
            qubit_in_circuit_def
          by simp

      next
        case False

        have original_operation_node:
          "nodes circuit node_id =
             Some (OperationNode op)"
          using
            False
            replacement_preserves_other_nodes
            updated_operation_node
          by auto

        from original_operation_nodes original_operation_node
        have original_operation_in_circuit:
          "operation_in_circuit circuit op"
          unfolding are_well_formed_operation_nodes_def
          by simp

        show ?thesis
          using
            original_operation_in_circuit
            replacement_preserves_num_qubits
          unfolding
            operation_in_circuit_def
            qubit_in_circuit_def
          by simp
      qed
    qed
  qed
qed

lemma replacement_preserves_acyclicity:
  (* Replacing an operation payload leaves the graph relation unchanged.
     Therefore, every directed path and every possible directed cycle is
     unchanged, and acyclicity is preserved. *)

  assumes acyclic:
    "is_acyclic_circuit circuit"

  shows
   "is_acyclic_circuit
     (replace_operation
         operation_node_id replacement_op circuit)"

  using
    assms
    replacement_preserves_edges
  unfolding
    is_acyclic_circuit_def
    edge_relation_def
  by simp

lemma replacement_preserves_wire_edge_relation:
  (* Replacing an operation does not change any wire-specific edge
     relation because the circuit's edge set is unchanged. *)
  "wire_edge_relation
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q
   =
   wire_edge_relation circuit q"

  unfolding wire_edge_relation_def
  using replacement_preserves_edges
  by simp

lemma replacement_preserves_wire_reaches:
  (* Since the wire edge relation is unchanged, reachability along every
     wire is unchanged. *)
  "wire_reaches
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_a node_b
   \<longleftrightarrow>
   wire_reaches circuit q node_a node_b"

  unfolding wire_reaches_def
  using replacement_preserves_wire_edge_relation
  by simp

lemma replacement_preserves_unique_wire_predecessor:
  "has_unique_wire_predecessor
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_id
   \<longleftrightarrow>
   has_unique_wire_predecessor circuit q node_id"

  unfolding has_unique_wire_predecessor_def
  using replacement_preserves_wire_edge_relation
  by simp

lemma replacement_preserves_unique_wire_successor:
  "has_unique_wire_successor
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_id
   \<longleftrightarrow>
   has_unique_wire_successor circuit q node_id"

  unfolding has_unique_wire_successor_def
  using replacement_preserves_wire_edge_relation
  by simp

lemma valid_replacement_preserves_nodes_comparable_on_wire:
  (* A valid replacement preserves the set of nodes using each wire and
     leaves wire reachability unchanged. Therefore, comparability of all
     nodes on a wire is preserved. *)
  assumes
    valid_replacement:
      "valid_operation_replacement
         circuit operation_node_id replacement_op"
  and
    original_comparable:
      "nodes_comparable_on_wire circuit q"
  shows
    "nodes_comparable_on_wire
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       q"

  unfolding nodes_comparable_on_wire_def
proof (intro allI impI)

  fix node_a node_b node_a_value node_b_value

  assume updated_node_a:
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       node_a
     =
     Some node_a_value"

  assume updated_node_b:
    "nodes
       (replace_operation
          operation_node_id
          replacement_op
          circuit)
       node_b
     =
     Some node_b_value"

  assume updated_node_a_uses_q:
    "node_uses_qubit node_a_value q"

  assume updated_node_b_uses_q:
    "node_uses_qubit node_b_value q"

  have original_node_a_uses_q:
    "case nodes circuit node_a of
       None \<Rightarrow> False
     | Some node \<Rightarrow> node_uses_qubit node q"

  proof -

    have updated_usage:
      "case
         nodes
           (replace_operation
              operation_node_id
              replacement_op
              circuit)
           node_a
       of
         None \<Rightarrow> False
       | Some node \<Rightarrow> node_uses_qubit node q"
      using
        updated_node_a
        updated_node_a_uses_q
      by simp

    show ?thesis
      using
        updated_node_a
        updated_node_a_uses_q
        valid_replacement
        valid_replacement_preserves_node_wire_usage
      by fastforce
  qed

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
     \<or> wire_reaches
         (replace_operation
            operation_node_id
            replacement_op
            circuit)
         q node_a node_b
     \<or> wire_reaches
         (replace_operation
            operation_node_id
            replacement_op
            circuit)
         q node_b node_a"
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
      "valid_operation_replacement
         circuit operation_node_id replacement_op"
  shows
    "all_wires_linear
       (replace_operation
          operation_node_id
          replacement_op
          circuit)"

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
      "qubit_in_circuit
         (replace_operation
            operation_node_id
            replacement_op
            circuit)
         q"

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

    from original_wire_linear
    have original_comparable:
      "nodes_comparable_on_wire circuit q"
      unfolding wire_is_linear_def
      by simp

    have updated_comparable:
      "nodes_comparable_on_wire
         (replace_operation
            operation_node_id
            replacement_op
            circuit)
         q"
      using
        valid_replacement
        original_comparable
      by (rule valid_replacement_preserves_nodes_comparable_on_wire)
    
    show "wire_is_linear (replace_operation operation_node_id replacement_op circuit) q"
      unfolding wire_is_linear_def
    proof (intro conjI)

      show
    "nodes_comparable_on_wire
           (replace_operation
              operation_node_id
              replacement_op
              circuit)
           q"
        using updated_comparable .

    next

      from original_wire_linear
      have original_input_has_no_predecessor:
        "\<nexists>predecessor_id.
           (predecessor_id, get_input_node_id q)
             \<in> wire_edge_relation circuit q"
        unfolding wire_is_linear_def
        by simp

      show
        "\<nexists>predecessor_id.
           (predecessor_id, get_input_node_id q)
             \<in> wire_edge_relation
                 (replace_operation
                    operation_node_id
                    replacement_op
                    circuit)
                 q"
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
        "has_unique_wire_successor
           (replace_operation
              operation_node_id
              replacement_op
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
        "has_unique_wire_predecessor
           circuit q (get_output_node_id q)"
        unfolding wire_is_linear_def
        by simp

      show
        "has_unique_wire_predecessor
           (replace_operation
              operation_node_id
              replacement_op
              circuit)
           q
           (get_output_node_id q)"
        using
          original_output_has_unique_predecessor
          replacement_preserves_unique_wire_predecessor
        by simp

    next

      from original_wire_linear
      have original_output_has_no_successor:
        "\<nexists>successor_id.
           (get_output_node_id q, successor_id)
             \<in> wire_edge_relation circuit q"
        unfolding wire_is_linear_def
        by simp

      show
        "\<nexists>successor_id.
           (get_output_node_id q, successor_id)
             \<in> wire_edge_relation
                 (replace_operation
                    operation_node_id
                    replacement_op
                    circuit)
                 q"
        using
          original_output_has_no_successor
          replacement_preserves_wire_edge_relation
        by simp

    next

      show
        "\<forall>node_id op.
           nodes
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             node_id
           =
           Some (OperationNode op)
           \<longrightarrow>
           node_uses_qubit (OperationNode op) q
           \<longrightarrow>
           has_unique_wire_predecessor
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             q node_id
           \<and>
           has_unique_wire_successor
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             q node_id"

      proof (intro allI impI)
        fix node_id op

        assume updated_operation_node:
          "nodes
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             node_id
           =
           Some (OperationNode op)"

        assume updated_operation_uses_q:
          "node_uses_qubit (OperationNode op) q"

        have original_node_uses_q:
          "case nodes circuit node_id of
             None \<Rightarrow> False
           | Some node \<Rightarrow> node_uses_qubit node q"

        proof -
          have updated_node_uses_q:
            "case
               nodes
                 (replace_operation
                    operation_node_id
                    replacement_op
                    circuit)
                 node_id
             of
               None \<Rightarrow> False
             | Some node \<Rightarrow> node_uses_qubit node q"
            using
              updated_operation_node
              updated_operation_uses_q
            by simp

          show ?thesis
            using
              updated_node_uses_q
              valid_replacement
              valid_replacement_preserves_node_wire_usage
            by simp
        qed

        then obtain original_node where
          original_node:
          "nodes circuit node_id = Some original_node"
          and
          original_node_uses_q:
          "node_uses_qubit original_node q"
          by (cases "nodes circuit node_id") auto

        have original_node_is_operation:
          "\<exists>original_op.
             original_node = OperationNode original_op"

        proof (cases "node_id = operation_node_id")

          case True

          from valid_replacement obtain selected_original_op where
            selected_operation_exists:
            "nodes circuit operation_node_id =
                 Some (OperationNode selected_original_op)"
            unfolding valid_operation_replacement_def
            by blast

          have
            "original_node = OperationNode selected_original_op"
            using
              original_node
              selected_operation_exists
              True
            by simp

          then show ?thesis
            by simp

        next
          case False

          have node_unchanged:
            "nodes
               (replace_operation
                  operation_node_id
                  replacement_op
                  circuit)
               node_id
             =
             nodes circuit node_id"
            using False
            by (rule replacement_preserves_other_nodes)

          have
            "original_node = OperationNode op"
            using
              original_node
              updated_operation_node
              node_unchanged
            by simp

          then show ?thesis
            by simp

        qed

        then obtain original_op where
          original_node_value:
          "original_node = OperationNode original_op"
          by auto

        have original_operation_node:
          "nodes circuit node_id =
             Some (OperationNode original_op)"
          using original_node original_node_value
          by simp

        have original_operation_uses_q:
          "node_uses_qubit (OperationNode original_op) q"
          using original_node_uses_q original_node_value
          by simp

        from original_wire_linear
        have original_operation_linear:
          "has_unique_wire_predecessor circuit q node_id
           \<and>
           has_unique_wire_successor circuit q node_id"
          unfolding wire_is_linear_def
          using
            original_operation_node
            original_operation_uses_q
          by simp

        show
          "has_unique_wire_predecessor
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             q node_id
           \<and>
           has_unique_wire_successor
             (replace_operation
                operation_node_id
                replacement_op
                circuit)
             q node_id"
          using
            original_operation_linear
            replacement_preserves_unique_wire_predecessor
            replacement_preserves_unique_wire_successor
          by simp
      qed
    qed
  qed
qed

lemma replacement_preserves_valid_circuit:
  (* Replacing an existing operation by a valid operation with the same
     qubit interface preserves the complete valid-circuit invariant.

     The transformation preserves local well-formedness, graph
     acyclicity, and linearity of every circuit wire.
  *)
  assumes
    valid_circuit:
    "is_valid_circuit circuit"
    and
    valid_replacement:
    "valid_operation_replacement
         circuit operation_node_id replacement_op"
  shows
    "is_valid_circuit
       (replace_operation
          operation_node_id
          replacement_op
          circuit)"
  using
    is_valid_circuit_def
    replacement_preserves_acyclicity
    replacement_preserves_well_formed_circuit
    replacement_preserves_wire_linearity
    valid_circuit
    valid_replacement
  by simp

end
