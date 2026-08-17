theory Quantum_Circuit_Subcircuit_Connect
  imports Quantum_Circuit_Subcircuit_Edit

begin

definition connect_subcircuit_input_on_wire ::
  "quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> qubit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> quantum_circuit"
where
  "connect_subcircuit_input_on_wire
      original_circuit
      operation_node
      replacement
      q
      current_circuit =
     (case
        (predecessor_on_wire
           original_circuit
           operation_node
           q,
         renamed_input_interface
           original_circuit
           replacement
           q)
      of
        (Some predecessor, Some input_node) \<Rightarrow>
          insert_edge
            (make_edge predecessor input_node q)
            current_circuit
      | _ \<Rightarrow> current_circuit)"

definition connect_subcircuit_inputs ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
  where
    (* Redirects every incoming wire of the removed operation to the
       corresponding renamed input interface node of the replacement
       subcircuit.
  
       After this step, every predecessor of the removed operation
       becomes a predecessor of the replacement fragment.
    *)

    "connect_subcircuit_inputs
      original_circuit
      current_circuit
      operation_node
      replacement =
     Finite_Set.fold
       (connect_subcircuit_input_on_wire
          original_circuit
          operation_node
          replacement)
       current_circuit
       (subcircuit_interface_qubits replacement)"

lemma connect_subcircuit_input_on_wire_preserves_nodes[simp]:
  (* Connecting one replacement input wire changes only the edge set.
     Therefore, every node-table entry remains unchanged. *)
  "nodes
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   nodes circuit"
  unfolding
    connect_subcircuit_input_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_inputs_preserve_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes
       (connect_subcircuit_inputs
          original_circuit
          circuit
          operation_node
          replacement)
     =
     nodes circuit"
proof -

  let ?connect_input =
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement"

  interpret connect_input: comp_fun_commute ?connect_input
  proof
    fix first_qubit second_qubit

    show
      "?connect_input second_qubit
         \<circ> ?connect_input first_qubit
       =
       ?connect_input first_qubit
         \<circ> ?connect_input second_qubit"
      unfolding
        connect_subcircuit_input_on_wire_def
        insert_edge_def
        fun_eq_iff
      apply (auto split: option.splits)
      by (simp add: insert_commute)
  qed

  have fold_preserves_nodes:
    "finite interface_qubits
     \<Longrightarrow>
     nodes
       (Finite_Set.fold
          ?connect_input
          current_circuit
          interface_qubits)
     =
     nodes current_circuit"
    for interface_qubits current_circuit
  proof (induction interface_qubits arbitrary: current_circuit
           rule: finite_induct)

    case empty

    show ?case
      by simp

  next

    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_input
         current_circuit
         (insert q interface_qubits)
       =
       ?connect_input q
         (Finite_Set.fold
            ?connect_input
            current_circuit
            interface_qubits)"
      using insert.hyps
      by (rule connect_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have folded_nodes:
    "nodes
       (Finite_Set.fold
          ?connect_input
          circuit
          (subcircuit_interface_qubits replacement))
     =
     nodes circuit"
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
  "num_qubits
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   num_qubits circuit"
  unfolding
    connect_subcircuit_input_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_input_on_wire_preserves_next_id[simp]:
  (* Connecting one replacement input wire inserts no nodes and
     therefore does not advance the host circuit's allocation
     boundary. *)
  "next_id
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   next_id circuit"
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
  "connect_subcircuit_input_on_wire
      original_circuit
      operation_node
      replacement
      q1
      (connect_subcircuit_input_on_wire
         original_circuit
         operation_node
         replacement
         q2
         circuit)
   =
   connect_subcircuit_input_on_wire
      original_circuit
      operation_node
      replacement
      q2
      (connect_subcircuit_input_on_wire
         original_circuit
         operation_node
         replacement
         q1
         circuit)"

  unfolding
    connect_subcircuit_input_on_wire_def
    insert_edge_def
  
  apply (auto split: option.splits prod.splits)
  by (simp add: insert_commute)

interpretation connect_subcircuit_input:
  comp_fun_commute
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement"
proof
  fix q1 q2

  show
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement
       q2
     \<circ>
     connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement
       q1
     =
     connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement
       q1
     \<circ>
     connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement
       q2"

    apply (rule ext)
    using
      connect_subcircuit_input_on_wire_commute[
        of original_circuit operation_node replacement q1 q2]
    by simp
qed

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
    "nodes
       (connect_subcircuit_inputs
          original_circuit
          current_circuit
          operation_node
          replacement)
     =
     nodes current_circuit"

  unfolding connect_subcircuit_inputs_def
proof -
  let ?connect =
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement"

  have fold_preserves_nodes:
    "finite interface_qubits
     \<Longrightarrow>
     nodes
       (Finite_Set.fold
          ?connect
          circuit
          interface_qubits)
     =
     nodes circuit"
    for interface_qubits circuit

  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_step:
      "Finite_Set.fold
         ?connect
         circuit
         (insert q interface_qubits)
       =
       ?connect q
         (Finite_Set.fold
            ?connect
            circuit
            interface_qubits)"
      using insert.hyps(1, 2)
      by (rule connect_subcircuit_input.fold_insert)

    have induction_result:
      "nodes
         (Finite_Set.fold
            ?connect
            circuit
            interface_qubits)
       =
       nodes circuit"
      using insert.IH
      by simp

    show ?case
      unfolding fold_step
      using induction_result
      by simp
  qed

  show
    "nodes
       (Finite_Set.fold
          ?connect
          current_circuit
          (subcircuit_interface_qubits replacement))
     =
     nodes current_circuit"
    using
      finite_interfaces
      fold_preserves_nodes
    by simp
qed

definition connect_subcircuit_output_on_wire ::
  "quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> qubit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> quantum_circuit"
  where
  (* Connects the renamed output interface node on one wire to the
     original successor of the removed operation on that wire.

     The predecessor/successor information is read from the original
     circuit because the removed operation and its incident edges are
     no longer present in the current intermediate circuit.
  *)
  "connect_subcircuit_output_on_wire
      original_circuit
      operation_node
      replacement
      q
      current_circuit =
     (case
        (successor_on_wire
           original_circuit
           operation_node
           q,
         renamed_output_interface
           original_circuit
           replacement
           q)
      of
        (Some successor, Some output_node) \<Rightarrow>
          insert_edge
            (make_edge output_node successor q)
            current_circuit
      | _ \<Rightarrow> current_circuit)"

definition connect_subcircuit_outputs ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
  where
    (* Redirects every outgoing wire of the removed operation to the
       corresponding renamed output interface node of the replacement
       subcircuit.
  
       After this step, every successor of the removed operation becomes
       a successor of the replacement fragment.
    *)
    "connect_subcircuit_outputs
      original_circuit
      current_circuit
      operation_node
      replacement =
     Finite_Set.fold
       (connect_subcircuit_output_on_wire
          original_circuit
          operation_node
          replacement)
       current_circuit
       (subcircuit_interface_qubits replacement)"

lemma connect_subcircuit_output_on_wire_preserves_nodes[simp]:
  (* Connecting one replacement output wire changes only the edge set.
     Therefore, every node-table entry remains unchanged. *)
  "nodes
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   nodes circuit"
  unfolding
    connect_subcircuit_output_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_outputs_preserve_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes
       (connect_subcircuit_outputs
          original_circuit circuit operation_node replacement)
     =
     nodes circuit"
proof -

  let ?connect_output =
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement"

  interpret connect_output: comp_fun_commute ?connect_output
  proof
    fix first_qubit second_qubit

    show
      "?connect_output second_qubit
         \<circ> ?connect_output first_qubit
       =
       ?connect_output first_qubit
         \<circ> ?connect_output second_qubit"
      unfolding
        connect_subcircuit_output_on_wire_def
        insert_edge_def
        fun_eq_iff
      apply (auto split: option.splits)
      by (simp add: insert_commute)
  qed

  have fold_preserves_nodes:
    "finite interface_qubits
     \<Longrightarrow>
     nodes
       (Finite_Set.fold
          ?connect_output
          current_circuit
          interface_qubits)
     =
     nodes current_circuit"
    for interface_qubits current_circuit
  proof (induction interface_qubits arbitrary: current_circuit
           rule: finite_induct)

    case empty

    show ?case
      by simp

  next

    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_output
         current_circuit
         (insert q interface_qubits)
       =
       ?connect_output q
         (Finite_Set.fold
            ?connect_output
            current_circuit
            interface_qubits)"
      using insert.hyps
      by (rule connect_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have folded_nodes:
    "nodes
       (Finite_Set.fold
          ?connect_output
          circuit
          (subcircuit_interface_qubits replacement))
     =
     nodes circuit"
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
  "num_qubits
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   num_qubits circuit"
  unfolding
    connect_subcircuit_output_on_wire_def
    insert_edge_def
  by (auto split: option.splits prod.splits)

lemma connect_subcircuit_output_on_wire_preserves_next_id[simp]:
  (* Connecting one replacement output wire inserts no nodes and
     therefore does not advance the host circuit's allocation
     boundary. *)
  "next_id
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   next_id circuit"
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
  "connect_subcircuit_output_on_wire
      original_circuit
      operation_node
      replacement
      q1
      (connect_subcircuit_output_on_wire
         original_circuit
         operation_node
         replacement
         q2
         circuit)
   =
   connect_subcircuit_output_on_wire
      original_circuit
      operation_node
      replacement
      q2
      (connect_subcircuit_output_on_wire
         original_circuit
         operation_node
         replacement
         q1
         circuit)"

  unfolding
    connect_subcircuit_output_on_wire_def
    insert_edge_def
  
  apply (auto split: option.splits prod.splits)
  by (simp add: insert_commute)

interpretation connect_subcircuit_output:
  comp_fun_commute
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement"
proof
  fix q1 q2

  show
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement
       q2
     \<circ>
     connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement
       q1
     =
     connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement
       q1
     \<circ>
     connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement
       q2"

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
    "nodes
       (connect_subcircuit_outputs
          original_circuit
          current_circuit
          operation_node
          replacement)
     =
     nodes current_circuit"

  unfolding connect_subcircuit_outputs_def
proof -
  let ?connect =
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement"

  have fold_preserves_nodes:
    "finite interface_qubits
     \<Longrightarrow>
     nodes
       (Finite_Set.fold
          ?connect
          circuit
          interface_qubits)
     =
     nodes circuit"
    for interface_qubits circuit

  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    show ?case
      by simp

  next
    case (insert q interface_qubits)

    have fold_step:
      "Finite_Set.fold
         ?connect
         circuit
         (insert q interface_qubits)
       =
       ?connect q
         (Finite_Set.fold
            ?connect
            circuit
            interface_qubits)"
      using insert.hyps(1, 2)
      by simp

    have induction_result:
      "nodes
         (Finite_Set.fold
            ?connect
            circuit
            interface_qubits)
       =
       nodes circuit"
      using insert.IH
      by simp

    show ?case
      unfolding fold_step
      using induction_result
      by simp
  qed

  show
    "nodes
       (Finite_Set.fold
          ?connect
          current_circuit
          (subcircuit_interface_qubits replacement))
     =
     nodes current_circuit"
    using
      finite_interfaces
      fold_preserves_nodes
    by simp
qed

definition update_frontier_after_subcircuit ::
  "quantum_circuit
    \<Rightarrow> frontier
    \<Rightarrow> subcircuit
    \<Rightarrow> frontier"
where
  (* Updates the construction frontier after replacing an operation by
     a subcircuit.

     On every qubit for which the replacement has an output interface,
     the new frontier is the renamed output-interface node.

     On every other qubit, the original frontier is preserved.

     The original host circuit is required because its next_id fixes the
     renaming offset used for all inserted subcircuit nodes.
  *)
  "update_frontier_after_subcircuit
      original_circuit
      current_frontier
      replacement =
     (\<lambda>q.
        case
          renamed_output_interface
            original_circuit
            replacement
            q
        of
          Some output_node \<Rightarrow> output_node
        | None \<Rightarrow> current_frontier q)"

lemma update_frontier_after_subcircuit_with_output:
  (* If the replacement has a renamed output-interface node on q, that
     node becomes the new frontier on q. *)
  assumes renamed_output:
    "renamed_output_interface
       original_circuit
       replacement
       q
     =
     Some output_node"

  shows
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     output_node"

  using renamed_output
  unfolding update_frontier_after_subcircuit_def
  by simp

lemma update_frontier_after_subcircuit_without_output:
  (* If the replacement has no output interface on q, the old frontier
     on q remains unchanged. *)
  assumes no_renamed_output:
    "renamed_output_interface
       original_circuit
       replacement
       q
     =
     None"

  shows
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     current_frontier q"

  using no_renamed_output
  unfolding update_frontier_after_subcircuit_def
  by simp

lemma update_frontier_after_subcircuit_output_interface:
  (* A local output-interface node becomes its renamed host-circuit node
     in the updated frontier. *)
  assumes output_interface:
    "output_interface replacement q = Some local_output_node"

  shows
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     rename_subcircuit_node_id
       original_circuit
       local_output_node"

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
    "update_frontier_after_subcircuit
       original_circuit
       current_frontier
       replacement
       q
     =
     current_frontier q"

  using no_output_interface
  unfolding
    update_frontier_after_subcircuit_def
    renamed_output_interface_def
  by simp

end
