theory Quantum_Circuit_Subcircuit_Replace_Core
  imports Quantum_Circuit_Subcircuit_Connect

begin

definition replace_operation_by_subcircuit ::
  "quantum_circuit
    \<Rightarrow> frontier
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit \<times> frontier"
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
  "replace_operation_by_subcircuit
      circuit
      frontier
      operation_node
      subcircuit =
     (let
        circuit1 =
          remove_operation_node
            circuit
            operation_node;

       circuit2 =
          insert_subcircuit_nodes
            circuit
            circuit1
            subcircuit;

       circuit3 =
          insert_subcircuit_internal_edges
            circuit
            circuit2
            subcircuit;

       circuit4 =
          connect_subcircuit_inputs
            circuit
            circuit3
            operation_node
            subcircuit;
        
       circuit5 =
          connect_subcircuit_outputs
            circuit
            circuit4
            operation_node
            subcircuit;

       frontier' =
          update_frontier_after_subcircuit
            circuit
            frontier
            subcircuit

      in
        (circuit5
           \<lparr>
             next_id :=
               NodeId
                 (node_id_to_nat (next_id circuit)
                  +
                  node_id_to_nat
                    (next_id (subgraph subcircuit)))
           \<rparr>, \<comment>\<open> The intermediate helpers preserve next_id so that the original allocation boundary can be used consistently for every renaming. Once all replacement nodes and edges have been installed, advance next_id beyond the copied local node namespace. \<close>
         frontier'))"

lemma replace_operation_by_subcircuit_next_id[simp]:
  (* After replacement, the allocation boundary lies beyond all copied
     replacement nodes. *)
  "next_id
      (fst
        (replace_operation_by_subcircuit
           circuit
           frontier
           operation_node
           replacement))
   =
   NodeId
     (node_id_to_nat (next_id circuit)
      +
      node_id_to_nat
        (next_id (subgraph replacement)))"

  unfolding replace_operation_by_subcircuit_def
  by simp

lemma replace_operation_by_subcircuit_frontier[simp]:
  (* The second component returned by replacement is precisely the
     updated construction frontier. *)
  "snd
      (replace_operation_by_subcircuit
         circuit
         frontier
         operation_node
         replacement)
   =
   update_frontier_after_subcircuit
     circuit
     frontier
     replacement"

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
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))
       operation_node_id
     = None"

proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
    and valid_subcircuit:
      "is_valid_subcircuit replacement"
    and same_num_qubits:
      "num_qubits (subgraph replacement) =
         num_qubits circuit"
    and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
    unfolding is_valid_subcircuit_replacement_def
    by auto

  have allocation_valid:
    "all_existing_node_ids_below_next_id circuit"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have operation_id_below_next_id:
    "node_id_to_nat operation_node_id
       < node_id_to_nat (next_id circuit)"
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

  let ?circuit1 =
    "remove_operation_node circuit operation_node_id"

  let ?circuit2 =
    "insert_subcircuit_nodes
       circuit
       ?circuit1
       replacement"

  let ?circuit3 =
    "insert_subcircuit_internal_edges
       circuit
       ?circuit2
       replacement"

  let ?circuit4 =
    "connect_subcircuit_inputs
       circuit
       ?circuit3
       operation_node_id
       replacement"

  let ?circuit5 =
    "connect_subcircuit_outputs
       circuit
       ?circuit4
       operation_node_id
       replacement"

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
    "nodes (subgraph replacement) local_node_id =
       Some (OperationNode op)"

  assumes allocated_local_node:
    "local_node_id
       \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))
       (rename_subcircuit_node_id
          original_circuit
          local_node_id)
     =
     Some (OperationNode op)"

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

  have copied:
    "nodes ?circuit2
       (rename_subcircuit_node_id
          original_circuit
          local_node_id)
     =
     Some (OperationNode op)"
    using
      insert_subcircuit_nodes_copies_operation
      local_operation
      allocated_local_node
    by simp

  show ?thesis
    using
      copied
      finite_interfaces
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
      insert_subcircuit_internal_edges_def
    by simp
qed

lemma replace_operation_by_subcircuit_preserves_unrelated_nodes:
  (* Every existing original circuit node other than the removed
     operation node remains unchanged after subcircuit replacement. *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  assumes original_node:
    "nodes circuit other_node_id = Some node"

  shows
    "nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))
       other_node_id
     =
     Some node"
proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
    unfolding is_valid_subcircuit_replacement_def
    by auto

  have allocation_valid:
    "all_existing_node_ids_below_next_id circuit"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have other_id_below_next_id:
    "node_id_to_nat other_node_id
       < node_id_to_nat (next_id circuit)"
    using allocation_valid original_node
    unfolding all_existing_node_ids_below_next_id_def
    by simp

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
      compatible_subcircuit_interface_qubits_finite
    by blast

  let ?circuit1 =
    "remove_operation_node circuit operation_node_id"

  let ?circuit2 =
    "insert_subcircuit_nodes
       circuit
       ?circuit1
       replacement"

  let ?circuit3 =
    "insert_subcircuit_internal_edges
       circuit
       ?circuit2
       replacement"

  let ?circuit4 =
    "connect_subcircuit_inputs
       circuit
       ?circuit3
       operation_node_id
       replacement"

  let ?circuit5 =
    "connect_subcircuit_outputs
       circuit
       ?circuit4
       operation_node_id
       replacement"

  have preserved_after_removal:
    "nodes ?circuit1 other_node_id = Some node"
    using different_node original_node
    by simp

  have preserved_after_node_insertion:
    "nodes ?circuit2 other_node_id = Some node"
    using
      insert_subcircuit_nodes_preserves_node_below_next_id[
        OF other_id_below_next_id,
        of "?circuit1" replacement]
      preserved_after_removal
    by simp

  have preserved_after_internal_edges:
    "nodes ?circuit3 other_node_id = Some node"
    using preserved_after_node_insertion
    by simp

  have preserved_after_input_connections:
    "nodes ?circuit4 other_node_id = Some node"
    using
      connect_subcircuit_inputs_preserves_nodes
      preserved_after_internal_edges
      finite_interfaces
    by simp

  have preserved_after_output_connections:
    "nodes ?circuit5 other_node_id = Some node"
    using
      finite_interfaces
      preserved_after_node_insertion
    by simp

  show ?thesis
    using preserved_after_output_connections
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    by simp
qed

lemma replace_operation_by_subcircuit_contains_renamed_internal_edges:
  (* Every internal edge of the replacement subcircuit appears in the
     resulting circuit after both endpoint IDs have been renamed into
     the surrounding circuit's node-ID space. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes internal_edge:
    "e \<in> subcircuit_internal_edges replacement"

  shows
    "rename_subcircuit_edge original_circuit e
       \<in>
       edges
         (fst
           (replace_operation_by_subcircuit
              original_circuit
              frontier
              operation_node_id
              replacement))"
proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id =
         Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
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

  have inserted_internal_edge:
    "?renamed_edge \<in> edges ?circuit3"
    using internal_edge
    by (rule insert_subcircuit_internal_edges_contains_internal_edge)

  have input_step_preserves_edge:
    "edge_to_preserve \<in> edges circuit
     \<Longrightarrow>
     edge_to_preserve
       \<in>
       edges
         (connect_subcircuit_input_on_wire
            original_circuit
            operation_node_id
            replacement
            q
            circuit)"
    for edge_to_preserve circuit q

    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have input_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow>
     edge_to_preserve \<in> edges circuit
     \<Longrightarrow>
     edge_to_preserve
       \<in>
       edges
         (Finite_Set.fold
            (connect_subcircuit_input_on_wire
               original_circuit
               operation_node_id
               replacement)
            circuit
            interface_qubits)"
    for interface_qubits circuit edge_to_preserve

  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    let ?connect =
      "connect_subcircuit_input_on_wire
         original_circuit
         operation_node_id
         replacement"

    have edge_after_remaining_wires:
      "edge_to_preserve
         \<in>
         edges
           (Finite_Set.fold
              ?connect
              circuit
              interface_qubits)"
      using
        insert.IH
        insert.prems
      by simp

    have edge_after_current_wire:
      "edge_to_preserve
         \<in>
         edges
           (?connect q
             (Finite_Set.fold
                ?connect
                circuit
                interface_qubits))"
      using
        edge_after_remaining_wires
        input_step_preserves_edge
      by blast

    have fold_insert:
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
     \<Longrightarrow>
     edge_to_preserve
       \<in>
       edges
         (connect_subcircuit_output_on_wire
            original_circuit
            operation_node_id
            replacement
            q
            circuit)"
    for edge_to_preserve circuit q

    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow>
     edge_to_preserve \<in> edges circuit
     \<Longrightarrow>
     edge_to_preserve
       \<in>
       edges
         (Finite_Set.fold
            (connect_subcircuit_output_on_wire
               original_circuit
               operation_node_id
               replacement)
            circuit
            interface_qubits)"
    for interface_qubits circuit edge_to_preserve

  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    let ?connect =
      "connect_subcircuit_output_on_wire
         original_circuit
         operation_node_id
         replacement"

    have edge_after_remaining_wires:
      "edge_to_preserve
         \<in>
         edges
           (Finite_Set.fold
              ?connect
              circuit
              interface_qubits)"
      using
        insert.IH
        insert.prems
      by simp

    have edge_after_current_wire:
      "edge_to_preserve
         \<in>
         edges
           (?connect q
             (Finite_Set.fold
                ?connect
                circuit
                interface_qubits))"
      using
        edge_after_remaining_wires
        output_step_preserves_edge
      by blast

    have fold_insert:
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
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes predecessor:
    "predecessor_on_wire
       original_circuit
       operation_node_id
       q
     =
     Some predecessor_node"

  assumes input_interface:
    "input_interface replacement q = Some local_input_node"

  shows
    "make_edge
       predecessor_node
       (rename_subcircuit_node_id
          original_circuit
          local_input_node)
       q
     \<in>
     edges
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))"
proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id =
         Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
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
    "renamed_input_interface
       original_circuit
       replacement
       q
     =
     Some
       (rename_subcircuit_node_id
          original_circuit
          local_input_node)"
    using input_interface
    unfolding renamed_input_interface_def
    by simp

  let ?new_edge =
    "make_edge
       predecessor_node
       (rename_subcircuit_node_id
          original_circuit
          local_input_node)
       q"

  let ?connect_input =
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node_id
       replacement"

  have input_step_preserves_edge:
    "e \<in> edges circuit
     \<Longrightarrow>
     e \<in> edges (?connect_input wire circuit)"
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
     \<Longrightarrow>
     q \<in> interface_qubits
     \<Longrightarrow>
     ?new_edge
       \<in>
       edges
         (Finite_Set.fold
            ?connect_input
            circuit
            interface_qubits)"
    for interface_qubits circuit
    using 
      connect_subcircuit_input.fold_rec
      selected_input_step_adds_edge
    by simp

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

  have edge_after_inputs:
    "?new_edge \<in> edges ?circuit4"
    unfolding connect_subcircuit_inputs_def
    using
      finite_interfaces
      q_in_interfaces
      input_fold_contains_edge
    by simp

  let ?connect_output =
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node_id
       replacement"

  have output_step_preserves_edge:
    "e \<in> edges circuit
     \<Longrightarrow>
     e \<in> edges (?connect_output wire circuit)"
    for e circuit wire
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow>
     e \<in> edges circuit
     \<Longrightarrow>
     e
       \<in>
       edges
         (Finite_Set.fold
            ?connect_output
            circuit
            interface_qubits)"
    for interface_qubits circuit e
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert wire interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_output
         circuit
         (insert wire interface_qubits)
       =
       ?connect_output wire
         (Finite_Set.fold
            ?connect_output
            circuit
            interface_qubits)"
      using insert.hyps(1, 2)
      by (rule connect_subcircuit_output.fold_insert)

    have edge_after_remaining:
      "e
        \<in>
        edges
          (Finite_Set.fold
             ?connect_output
             circuit
             interface_qubits)"
      using insert.IH insert.prems
      by simp

    have edge_after_current:
      "e
        \<in>
        edges
          (?connect_output wire
            (Finite_Set.fold
               ?connect_output
               circuit
               interface_qubits))"
      using edge_after_remaining
      by (rule output_step_preserves_edge)

    show ?case
      unfolding fold_insert
      using edge_after_current .
  qed

  let ?circuit5 =
    "connect_subcircuit_outputs
       original_circuit
       ?circuit4
       operation_node_id
       replacement"

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
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes successor:
    "successor_on_wire
       original_circuit
       operation_node_id
       q
     =
     Some successor_node"

  assumes output_interface:
    "output_interface replacement q = Some local_output_node"

  shows
    "make_edge
       (rename_subcircuit_node_id
          original_circuit
          local_output_node)
       successor_node
       q
     \<in>
     edges
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))"
proof -
  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id =
         Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
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
    "renamed_output_interface
       original_circuit
       replacement
       q
     =
     Some
       (rename_subcircuit_node_id
          original_circuit
          local_output_node)"
    using output_interface
    unfolding renamed_output_interface_def
    by simp

  let ?new_edge =
    "make_edge
       (rename_subcircuit_node_id
          original_circuit
          local_output_node)
       successor_node
       q"

  let ?connect_output =
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node_id
       replacement"

  have output_step_preserves_edge:
    "e \<in> edges circuit
     \<Longrightarrow>
     e \<in> edges (?connect_output wire circuit)"
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
     \<Longrightarrow>
     q \<in> interface_qubits
     \<Longrightarrow>
     ?new_edge
       \<in>
       edges
         (Finite_Set.fold
            ?connect_output
            circuit
            interface_qubits)"
    for interface_qubits circuit
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert wire interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_output
         circuit
         (insert wire interface_qubits)
       =
       ?connect_output wire
         (Finite_Set.fold
            ?connect_output
            circuit
            interface_qubits)"
      using insert.hyps(1, 2)
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
    proof (cases "wire = q")

      case True

      have edge_after_current:
        "?new_edge
          \<in>
          edges
            (?connect_output wire
              (Finite_Set.fold
                 ?connect_output
                 circuit
                 interface_qubits))"
        using True selected_output_step_adds_edge
        by simp

      show ?thesis
        unfolding fold_insert
        using edge_after_current .

    next

      case False

      have q_in_remaining:
        "q \<in> interface_qubits"
        using insert.prems False
        by simp

      have edge_after_remaining:
        "?new_edge
          \<in>
          edges
            (Finite_Set.fold
               ?connect_output
               circuit
               interface_qubits)"
        using insert.IH q_in_remaining
        by simp

      have edge_after_current:
        "?new_edge
          \<in>
          edges
            (?connect_output wire
              (Finite_Set.fold
                 ?connect_output
                 circuit
                 interface_qubits))"
        using edge_after_remaining
        by (rule output_step_preserves_edge)

      show ?thesis
        unfolding fold_insert
        using edge_after_current .
    qed
  qed

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

  have edge_after_outputs:
    "?new_edge \<in> edges ?circuit5"
    unfolding connect_subcircuit_outputs_def
    using
      finite_interfaces
      q_in_interfaces
      output_fold_contains_edge
    by blast

  show ?thesis
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    using edge_after_outputs
    by simp
qed

lemma replace_operation_by_subcircuit_preserves_unrelated_edges:
  (* Every edge that does not touch the removed operation is preserved by
     subcircuit replacement. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes unrelated_edge:
    "e \<in> edges original_circuit"

  assumes source_not_removed:
    "edge_source e \<noteq> operation_node_id"

  assumes target_not_removed:
    "edge_target e \<noteq> operation_node_id"

  shows
    "e \<in>
      edges
        (fst
          (replace_operation_by_subcircuit
             original_circuit
             frontier
             operation_node_id
             replacement))"
proof -

  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id =
        Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit
        (op_qargs original_op)
        replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

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
     \<Longrightarrow>
     edge_to_preserve
       \<in> edges
           (connect_subcircuit_input_on_wire
              original_circuit
              operation_node_id
              replacement
              q
              circuit)"
    for edge_to_preserve circuit q
    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have input_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow>
     edge_to_preserve \<in> edges circuit
     \<Longrightarrow>
     edge_to_preserve
       \<in> edges
           (Finite_Set.fold
              (connect_subcircuit_input_on_wire
                 original_circuit
                 operation_node_id
                 replacement)
              circuit
              interface_qubits)"
    for interface_qubits circuit edge_to_preserve
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    let ?connect =
      "connect_subcircuit_input_on_wire
         original_circuit
         operation_node_id
         replacement"

    have edge_after_remaining:
      "edge_to_preserve
         \<in> edges
             (Finite_Set.fold
                ?connect
                circuit
                interface_qubits)"
      using insert.IH insert.prems
      by blast

    have edge_after_q:
      "edge_to_preserve
         \<in> edges
             (?connect q
                (Finite_Set.fold
                   ?connect
                   circuit
                   interface_qubits))"
      using edge_after_remaining
      by (rule input_step_preserves_edge)

    have fold_insert:
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
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      using edge_after_q
      unfolding fold_insert .
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
     \<Longrightarrow>
     edge_to_preserve
       \<in> edges
           (connect_subcircuit_output_on_wire
              original_circuit
              operation_node_id
              replacement
              q
              circuit)"
    for edge_to_preserve circuit q
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_preserves_edge:
    "finite interface_qubits
     \<Longrightarrow>
     edge_to_preserve \<in> edges circuit
     \<Longrightarrow>
     edge_to_preserve
       \<in> edges
           (Finite_Set.fold
              (connect_subcircuit_output_on_wire
                 original_circuit
                 operation_node_id
                 replacement)
              circuit
              interface_qubits)"
    for interface_qubits circuit edge_to_preserve
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    let ?connect =
      "connect_subcircuit_output_on_wire
         original_circuit
         operation_node_id
         replacement"

    have edge_after_remaining:
      "edge_to_preserve
         \<in> edges
             (Finite_Set.fold
                ?connect
                circuit
                interface_qubits)"
      using
        insert.IH
        insert.prems
      by simp

    have edge_after_q:
      "edge_to_preserve
         \<in> edges
             (?connect q
                (Finite_Set.fold
                   ?connect
                   circuit
                   interface_qubits))"
      using edge_after_remaining
      by (rule output_step_preserves_edge)

    have fold_insert:
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
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes node_in_result:
    "nodes
       (fst
         (replace_operation_by_subcircuit
            original_circuit
            frontier
            operation_node_id
            replacement))
       node_id
     =
     Some node"

  shows
    "(node_id \<noteq> operation_node_id
      \<and> nodes original_circuit node_id = Some node)
     \<or>
     (\<exists>local_node_id.
        local_node_id \<in> subcircuit_operation_node_ids replacement
        \<and>
        node_id =
          rename_subcircuit_node_id
            original_circuit
            local_node_id
        \<and>
        nodes (subgraph replacement) local_node_id = Some node)"

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
    "is_valid_subcircuit_replacement
       original_circuit
       operation_node_id
       replacement"

  assumes edge_in_result:
    "e \<in>
       edges
         (fst
           (replace_operation_by_subcircuit
              original_circuit
              frontier
              operation_node_id
              replacement))"

  shows
    "(e \<in> edges original_circuit
      \<and> edge_source e \<noteq> operation_node_id
      \<and> edge_target e \<noteq> operation_node_id)

     \<or>

     e \<in> renamed_subcircuit_internal_edges
              original_circuit
              replacement

     \<or>

     (\<exists>q predecessor_node renamed_input_node.
        q \<in> subcircuit_interface_qubits replacement
        \<and>
        predecessor_on_wire
          original_circuit
          operation_node_id
          q
        =
        Some predecessor_node
        \<and>
        renamed_input_interface
          original_circuit
          replacement
          q
        =
        Some renamed_input_node
        \<and>
        e =
          make_edge
            predecessor_node
            renamed_input_node
            q)

     \<or>

     (\<exists>q renamed_output_node successor_node.
        q \<in> subcircuit_interface_qubits replacement
        \<and>
        renamed_output_interface
          original_circuit
          replacement
          q
        =
        Some renamed_output_node
        \<and>
        successor_on_wire
          original_circuit
          operation_node_id
          q
        =
        Some successor_node
        \<and>
        e =
          make_edge
            renamed_output_node
            successor_node
            q)"
proof -

  from valid_replacement obtain original_op where
    operation_exists:
      "nodes original_circuit operation_node_id =
         Some (OperationNode original_op)"
    and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"
    using compatible
    by (rule compatible_subcircuit_interface_qubits_finite)

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

  have edge_in_circuit5:
    "e \<in> edges ?circuit5"
    using edge_in_result
    unfolding
      replace_operation_by_subcircuit_def
      Let_def
    by simp

  let ?connect_input =
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node_id
       replacement"

  let ?connect_output =
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node_id
       replacement"

  have input_step_cases:
    "edge_to_classify \<in> edges (?connect_input q circuit)
     \<Longrightarrow>
     edge_to_classify \<in> edges circuit
       \<or>
       (\<exists>predecessor_node renamed_input_node.
          predecessor_on_wire
            original_circuit
            operation_node_id
            q
          =
          Some predecessor_node
          \<and>
          renamed_input_interface
            original_circuit
            replacement
            q
          =
          Some renamed_input_node
          \<and>
          edge_to_classify =
            make_edge
              predecessor_node
              renamed_input_node
              q)"
    for edge_to_classify circuit q
    unfolding
      connect_subcircuit_input_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have input_fold_cases:
    "finite interface_qubits
     \<Longrightarrow>
     edge_to_classify
       \<in>
       edges
         (Finite_Set.fold
            ?connect_input
            circuit
            interface_qubits)
     \<Longrightarrow>
     edge_to_classify \<in> edges circuit
       \<or>
       (\<exists>q predecessor_node renamed_input_node.
          q \<in> interface_qubits
          \<and>
          predecessor_on_wire
            original_circuit
            operation_node_id
            q
          =
          Some predecessor_node
          \<and>
          renamed_input_interface
            original_circuit
            replacement
            q
          =
          Some renamed_input_node
          \<and>
          edge_to_classify =
            make_edge
              predecessor_node
              renamed_input_node
              q)"
    for interface_qubits circuit edge_to_classify
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_input
         circuit
         (insert q interface_qubits)
       =
       ?connect_input q
         (Finite_Set.fold
            ?connect_input
            circuit
            interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    have edge_after_q:
      "edge_to_classify
         \<in>
         edges
           (?connect_input q
             (Finite_Set.fold
                ?connect_input
                circuit
                interface_qubits))"
      using insert.prems
      unfolding fold_insert .

    from input_step_cases[OF edge_after_q]
    show ?case
    proof

      assume edge_before_q:
        "edge_to_classify
           \<in>
           edges
             (Finite_Set.fold
                ?connect_input
                circuit
                interface_qubits)"

      from insert.IH[OF edge_before_q]
      show ?thesis
      proof

        assume base_edge:
          "edge_to_classify \<in> edges circuit"

        then show ?thesis
          by blast

      next

        assume earlier_input_edge:
          "\<exists>r predecessor_node renamed_input_node.
             r \<in> interface_qubits
             \<and>
             predecessor_on_wire
               original_circuit
               operation_node_id
               r
             =
             Some predecessor_node
             \<and>
             renamed_input_interface
               original_circuit
               replacement
               r
             =
             Some renamed_input_node
             \<and>
             edge_to_classify =
               make_edge
                 predecessor_node
                 renamed_input_node
                 r"

        then show ?thesis
          by blast
      qed

    next

      assume current_input_edge:
        "\<exists>predecessor_node renamed_input_node.
           predecessor_on_wire
             original_circuit
             operation_node_id
             q
           =
           Some predecessor_node
           \<and>
           renamed_input_interface
             original_circuit
             replacement
             q
           =
           Some renamed_input_node
           \<and>
           edge_to_classify =
             make_edge
               predecessor_node
               renamed_input_node
               q"

      then show ?thesis
        by blast
    qed
  qed

  have output_step_cases:
    "edge_to_classify \<in> edges (?connect_output q circuit)
     \<Longrightarrow>
     edge_to_classify \<in> edges circuit
       \<or>
       (\<exists>renamed_output_node successor_node.
          renamed_output_interface
            original_circuit
            replacement
            q
          =
          Some renamed_output_node
          \<and>
          successor_on_wire
            original_circuit
            operation_node_id
            q
          =
          Some successor_node
          \<and>
          edge_to_classify =
            make_edge
              renamed_output_node
              successor_node
              q)"
    for edge_to_classify circuit q
    unfolding
      connect_subcircuit_output_on_wire_def
      insert_edge_def
    by (auto split: option.splits prod.splits)

  have output_fold_cases:
    "finite interface_qubits
     \<Longrightarrow>
     edge_to_classify
       \<in>
       edges
         (Finite_Set.fold
            ?connect_output
            circuit
            interface_qubits)
     \<Longrightarrow>
     edge_to_classify \<in> edges circuit
       \<or>
       (\<exists>q renamed_output_node successor_node.
          q \<in> interface_qubits
          \<and>
          renamed_output_interface
            original_circuit
            replacement
            q
          =
          Some renamed_output_node
          \<and>
          successor_on_wire
            original_circuit
            operation_node_id
            q
          =
          Some successor_node
          \<and>
          edge_to_classify =
            make_edge
              renamed_output_node
              successor_node
              q)"
    for interface_qubits circuit edge_to_classify
  proof (induction interface_qubits arbitrary: circuit rule: finite_induct)
    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_output
         circuit
         (insert q interface_qubits)
       =
       ?connect_output q
         (Finite_Set.fold
            ?connect_output
            circuit
            interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    have edge_after_q:
      "edge_to_classify
         \<in>
         edges
           (?connect_output q
             (Finite_Set.fold
                ?connect_output
                circuit
                interface_qubits))"
      using insert.prems
      unfolding fold_insert .

    from output_step_cases[OF edge_after_q]
    show ?case
    proof

      assume edge_before_q:
        "edge_to_classify
           \<in>
           edges
             (Finite_Set.fold
                ?connect_output
                circuit
                interface_qubits)"

      from insert.IH[OF edge_before_q]
      show ?thesis
      proof

        assume base_edge:
          "edge_to_classify \<in> edges circuit"

        then show ?thesis
          by blast

      next

        assume earlier_output_edge:
          "\<exists>r renamed_output_node successor_node.
             r \<in> interface_qubits
             \<and>
             renamed_output_interface
               original_circuit
               replacement
               r
             =
             Some renamed_output_node
             \<and>
             successor_on_wire
               original_circuit
               operation_node_id
               r
             =
             Some successor_node
             \<and>
             edge_to_classify =
               make_edge
                 renamed_output_node
                 successor_node
                 r"

        then show ?thesis
          by blast
      qed

    next

      assume current_output_edge:
        "\<exists>renamed_output_node successor_node.
           renamed_output_interface
             original_circuit
             replacement
             q
           =
           Some renamed_output_node
           \<and>
           successor_on_wire
             original_circuit
             operation_node_id
             q
           =
           Some successor_node
           \<and>
           edge_to_classify =
             make_edge
               renamed_output_node
               successor_node
               q"

      then show ?thesis
        by blast
    qed
  qed

  have after_output_cases:
    "e \<in> edges ?circuit4
     \<or>
     (\<exists>q renamed_output_node successor_node.
        q \<in> subcircuit_interface_qubits replacement
        \<and>
        renamed_output_interface
          original_circuit
          replacement
          q
        =
        Some renamed_output_node
        \<and>
        successor_on_wire
          original_circuit
          operation_node_id
          q
        =
        Some successor_node
        \<and>
        e =
          make_edge
            renamed_output_node
            successor_node
            q)"

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
          \<and>
          predecessor_on_wire
            original_circuit
            operation_node_id
            q
          =
          Some predecessor_node
          \<and>
          renamed_input_interface
            original_circuit
            replacement
            q
          =
          Some renamed_input_node
          \<and>
          e =
            make_edge
              predecessor_node
              renamed_input_node
              q)"
      using
        connect_subcircuit_inputs_def
        edge_before_outputs
        finite_interfaces
        input_fold_cases
      unfolding connect_subcircuit_inputs_def
      by presburger

    from after_input_cases show ?thesis
    proof

      assume edge_before_inputs:
        "e \<in> edges ?circuit3"

      have internal_or_old:
        "e \<in> edges ?circuit2
         \<or>
         e \<in>
           renamed_subcircuit_internal_edges
             original_circuit
             replacement"
        using edge_before_inputs
        unfolding insert_subcircuit_internal_edges_def
        by auto

      from internal_or_old show ?thesis
      proof

        assume edge_before_internal_insertion:
          "e \<in> edges ?circuit2"

        have edge_after_removal:
          "e \<in> edges ?circuit1"
          using edge_before_internal_insertion
          unfolding insert_subcircuit_nodes_def
          by simp

        have original_unrelated:
          "e \<in> edges original_circuit
           \<and>
           edge_source e \<noteq> operation_node_id
           \<and>
           edge_target e \<noteq> operation_node_id"
          using edge_after_removal
          unfolding remove_operation_node_def
          by auto

        then show ?thesis
          by blast

      next

        assume internal_edge:
          "e \<in>
            renamed_subcircuit_internal_edges
              original_circuit
              replacement"

        then show ?thesis
          by blast
      qed

    next

      assume input_edge:
        "\<exists>q predecessor_node renamed_input_node.
           q \<in> subcircuit_interface_qubits replacement
           \<and>
           predecessor_on_wire
             original_circuit
             operation_node_id
             q
           =
           Some predecessor_node
           \<and>
           renamed_input_interface
             original_circuit
             replacement
             q
           =
           Some renamed_input_node
           \<and>
           e =
             make_edge
               predecessor_node
               renamed_input_node
               q"

      then show ?thesis
        by simp
    qed

  next

    assume output_edge:
      "\<exists>q renamed_output_node successor_node.
         q \<in> subcircuit_interface_qubits replacement
         \<and>
         renamed_output_interface
           original_circuit
           replacement
           q
         =
         Some renamed_output_node
         \<and>
         successor_on_wire
           original_circuit
           operation_node_id
           q
         =
         Some successor_node
         \<and>
         e =
           make_edge
             renamed_output_node
             successor_node
             q"

    then show ?thesis
      by blast
  qed
qed

lemma replace_operation_by_subcircuit_preserves_boundary_nodes:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "are_well_formed_boundary_nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
proof -

  let ?result =
    "fst
       (replace_operation_by_subcircuit
          circuit
          frontier
          operation_node_id
          replacement)"

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
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
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
    "remove_operation_node
       circuit
       operation_node_id"

  let ?circuit2 =
    "insert_subcircuit_nodes
       circuit
       ?circuit1
       replacement"

  let ?circuit3 =
    "insert_subcircuit_internal_edges
       circuit
       ?circuit2
       replacement"

  let ?connect_input =
    "connect_subcircuit_input_on_wire
       circuit
       operation_node_id
       replacement"

  let ?connect_output =
    "connect_subcircuit_output_on_wire
       circuit
       operation_node_id
       replacement"

  have input_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow>
     num_qubits
       (Finite_Set.fold
          ?connect_input
          base_circuit
          interface_qubits)
     =
     num_qubits base_circuit"
    for interface_qubits base_circuit
  proof (induction interface_qubits arbitrary: base_circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_input
         base_circuit
         (insert q interface_qubits)
       =
       ?connect_input q
         (Finite_Set.fold
            ?connect_input
            base_circuit
            interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have output_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow>
     num_qubits
       (Finite_Set.fold
          ?connect_output
          base_circuit
          interface_qubits)
     =
     num_qubits base_circuit"
    for interface_qubits base_circuit
  proof (induction interface_qubits arbitrary: base_circuit rule: finite_induct)

    case empty

    then show ?case
      by simp

  next

    case (insert q interface_qubits)

    have fold_insert:
      "Finite_Set.fold
         ?connect_output
         base_circuit
         (insert q interface_qubits)
       =
       ?connect_output q
         (Finite_Set.fold
            ?connect_output
            base_circuit
            interface_qubits)"
      using insert.hyps
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have inputs_preserve_num_qubits:
    "num_qubits
       (connect_subcircuit_inputs
          circuit
          ?circuit3
          operation_node_id
          replacement)
     =
     num_qubits ?circuit3"
    unfolding connect_subcircuit_inputs_def
    using
      finite_interfaces
      input_fold_preserves_num_qubits
    by blast

  let ?circuit4 =
    "connect_subcircuit_inputs
       circuit
       ?circuit3
       operation_node_id
       replacement"

  have outputs_preserve_num_qubits:
    "num_qubits
       (connect_subcircuit_outputs
          circuit
          ?circuit4
          operation_node_id
          replacement)
     =
     num_qubits ?circuit4"
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
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "are_well_formed_operation_nodes
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
proof -

  let ?result =
    "fst
       (replace_operation_by_subcircuit
          circuit
          frontier
          operation_node_id
          replacement)"

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
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
  and replacement_valid:
      "is_valid_subcircuit replacement"
  and same_num_qubits:
      "num_qubits (subgraph replacement) =
         num_qubits circuit"
  and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
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

  let ?connect_input =
    "connect_subcircuit_input_on_wire
       circuit
       operation_node_id
       replacement"

  have input_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow>
     num_qubits
       (Finite_Set.fold
          ?connect_input
          current_circuit
          interface_qubits)
     =
     num_qubits current_circuit"
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
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  let ?connect_output =
    "connect_subcircuit_output_on_wire
       circuit
       operation_node_id
       replacement"

  have output_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow>
     num_qubits
       (Finite_Set.fold
          ?connect_output
          current_circuit
          interface_qubits)
     =
     num_qubits current_circuit"
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
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have result_num_qubits:
    "num_qubits ?result = num_qubits circuit"
  proof -

    let ?circuit1 =
      "remove_operation_node
         circuit
         operation_node_id"

    let ?circuit2 =
      "insert_subcircuit_nodes
         circuit
         ?circuit1
         replacement"

    let ?circuit3 =
      "insert_subcircuit_internal_edges
         circuit
         ?circuit2
         replacement"

    let ?circuit4 =
      "connect_subcircuit_inputs
         circuit
         ?circuit3
         operation_node_id
         replacement"

    let ?circuit5 =
      "connect_subcircuit_outputs
         circuit
         ?circuit4
         operation_node_id
         replacement"

    have inputs_preserve_num_qubits:
      "num_qubits ?circuit4 =
         num_qubits ?circuit3"
      unfolding connect_subcircuit_inputs_def
      using
        finite_interfaces
        input_fold_preserves_num_qubits
      by blast

    have outputs_preserve_num_qubits:
      "num_qubits ?circuit5 =
         num_qubits ?circuit4"
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

  show ?thesis
    unfolding are_well_formed_operation_nodes_def
  proof (intro allI impI)

    fix node_id op

    assume result_operation_node:
      "nodes ?result node_id =
         Some (OperationNode op)"

    from replace_operation_by_subcircuit_node_cases[
        OF
          valid_state
          valid_replacement
          result_operation_node]
    consider
      (original)
        "node_id \<noteq> operation_node_id"
        "nodes circuit node_id =
           Some (OperationNode op)"
    |
      (copied) local_node_id where
        "local_node_id
           \<in> subcircuit_operation_node_ids replacement"
        "node_id =
           rename_subcircuit_node_id
             circuit
             local_node_id"
        "nodes
           (subgraph replacement)
           local_node_id
         =
         Some (OperationNode op)"
      by blast

    then show
      "operation_in_circuit ?result op"
      by (metis
          are_well_formed_operation_nodes_def
          operation_in_circuit_def
          original_operation_nodes
          qubit_in_circuit_def
          replacement_operation_nodes
          result_num_qubits
          same_num_qubits)
  qed
qed

lemma valid_subcircuit_input_interface_uses_qubit:
  assumes valid_subcircuit:
    "is_valid_subcircuit replacement"

  assumes input_interface:
    "input_interface replacement q = Some node_id"

  assumes operation_node:
    "nodes
       (subgraph replacement)
       node_id
     =
     Some (OperationNode op)"

  shows
    "q \<in> set (op_qargs op)"
proof -

  from valid_subcircuit input_interface
  have first_operation:
    "is_first_operation_on_subcircuit_wire
       replacement
       q
       node_id"
    unfolding is_valid_subcircuit_def
    by blast

  from first_operation have input_edge:
    "(get_input_node_id q, node_id)
       \<in> wire_edge_relation
            (subgraph replacement)
            q"
    unfolding is_first_operation_on_subcircuit_wire_def
    by blast

  then have edge_in_subgraph:
    "make_edge
       (get_input_node_id q)
       node_id
       q
     \<in> edges (subgraph replacement)"
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
    "is_well_formed_edge
       (subgraph replacement)
       (make_edge
          (get_input_node_id q)
          node_id
          q)"
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
    "nodes
       (subgraph replacement)
       node_id
     =
     Some (OperationNode op)"

  shows
    "q \<in> set (op_qargs op)"
proof -

  from valid_subcircuit output_interface
  have last_operation:
    "is_last_operation_on_subcircuit_wire
       replacement
       q
       node_id"
    unfolding is_valid_subcircuit_def
    by blast

  from last_operation have output_edge:
    "(node_id, get_output_node_id q)
       \<in> wire_edge_relation
            (subgraph replacement)
            q"
    unfolding is_last_operation_on_subcircuit_wire_def
    by blast

  then have edge_in_subgraph:
    "make_edge
       node_id
       (get_output_node_id q)
       q
     \<in> edges (subgraph replacement)"
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
    "is_well_formed_edge
       (subgraph replacement)
       (make_edge
          node_id
          (get_output_node_id q)
          q)"
    unfolding are_well_formed_edges_def
    by blast

  from well_formed_output_edge operation_node
  have
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
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "are_well_formed_edges
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
proof -

  let ?result =
    "fst
       (replace_operation_by_subcircuit
          circuit
          frontier
          operation_node_id
          replacement)"

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
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
  and replacement_valid:
      "is_valid_subcircuit replacement"
  and same_num_qubits:
      "num_qubits (subgraph replacement) =
         num_qubits circuit"
  and compatible:
      "is_compatible_subcircuit
         (op_qargs original_op)
         replacement"
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

  let ?connect_input =
    "connect_subcircuit_input_on_wire
       circuit
       operation_node_id
       replacement"

  let ?connect_output =
    "connect_subcircuit_output_on_wire
       circuit
       operation_node_id
       replacement"

  have input_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow>
     num_qubits
       (Finite_Set.fold
          ?connect_input
          current_circuit
          interface_qubits)
     =
     num_qubits current_circuit"
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
      by (rule connect_subcircuit_input.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have output_fold_preserves_num_qubits:
    "finite interface_qubits
     \<Longrightarrow>
     num_qubits
       (Finite_Set.fold
          ?connect_output
          current_circuit
          interface_qubits)
     =
     num_qubits current_circuit"
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
      by (rule connect_subcircuit_output.fold_insert)

    show ?case
      unfolding fold_insert
      using insert.IH
      by simp
  qed

  have result_num_qubits:
    "num_qubits ?result = num_qubits circuit"
  proof -

    let ?circuit1 =
      "remove_operation_node
         circuit
         operation_node_id"

    let ?circuit2 =
      "insert_subcircuit_nodes
         circuit
         ?circuit1
         replacement"

    let ?circuit3 =
      "insert_subcircuit_internal_edges
         circuit
         ?circuit2
         replacement"

    let ?circuit4 =
      "connect_subcircuit_inputs
         circuit
         ?circuit3
         operation_node_id
         replacement"

    let ?circuit5 =
      "connect_subcircuit_outputs
         circuit
         ?circuit4
         operation_node_id
         replacement"

    have inputs_preserve_num_qubits:
      "num_qubits ?circuit4 =
         num_qubits ?circuit3"
      unfolding connect_subcircuit_inputs_def
      using
        finite_interfaces
        input_fold_preserves_num_qubits
      by blast

    have outputs_preserve_num_qubits:
      "num_qubits ?circuit5 =
         num_qubits ?circuit4"
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
     \<Longrightarrow>
     edge_source e \<noteq> operation_node_id
     \<Longrightarrow>
     edge_target e \<noteq> operation_node_id
     \<Longrightarrow>
     is_well_formed_edge ?result e"
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
    "renamed_edge
       \<in>
       renamed_subcircuit_internal_edges
         circuit
         replacement
     \<Longrightarrow>
     is_well_formed_edge ?result renamed_edge"
    for renamed_edge
  proof -

    assume renamed_edge:
      "renamed_edge
         \<in>
         renamed_subcircuit_internal_edges
           circuit
           replacement"

    then obtain local_edge where
      local_edge:
        "local_edge
           \<in> subcircuit_internal_edges replacement"
    and renamed_edge_eq:
        "renamed_edge =
           rename_subcircuit_edge circuit local_edge"
      unfolding renamed_subcircuit_internal_edges_def
      by blast

    from local_edge have local_edge_in_graph:
      "local_edge \<in> edges (subgraph replacement)"
      unfolding subcircuit_internal_edges_def
      by simp

    from replacement_edges_well_formed local_edge_in_graph
    have local_edge_well_formed:
      "is_well_formed_edge
         (subgraph replacement)
         local_edge"
      unfolding are_well_formed_edges_def
      by blast

    from local_edge have source_allocated:
      "edge_source local_edge
         \<in> subcircuit_operation_node_ids replacement"
    and target_allocated:
      "edge_target local_edge
         \<in> subcircuit_operation_node_ids replacement"
      unfolding subcircuit_internal_edges_def
      by auto

    from local_edge_well_formed obtain source_node target_node where
      local_source:
        "nodes
           (subgraph replacement)
           (edge_source local_edge)
         =
         Some source_node"
    and local_target:
        "nodes
           (subgraph replacement)
           (edge_target local_edge)
         =
         Some target_node"
    and local_valid_wire:
        "qubit_in_circuit
           (subgraph replacement)
           (edge_wire local_edge)"
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
        "nodes
           (subgraph replacement)
           (edge_source local_edge)
         =
         Some (OperationNode source_op)"
      unfolding
        subcircuit_operation_node_ids_def
        operation_node_ids_def
      by blast

    from target_allocated obtain target_op where
      target_operation:
        "nodes
           (subgraph replacement)
           (edge_target local_edge)
         =
         Some (OperationNode target_op)"
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
      "nodes
         ?result
         (rename_subcircuit_node_id
            circuit
            (edge_source local_edge))
       =
       Some (OperationNode source_op)"
      using
         finite_interfaces
         replace_operation_by_subcircuit_contains_renamed_nodes
         source_allocated
         source_operation
      by simp

    have renamed_target:
      "nodes
         ?result
         (rename_subcircuit_node_id
            circuit
            (edge_target local_edge))
       =
       Some (OperationNode target_op)"
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
     \<Longrightarrow>
     predecessor_on_wire
       circuit
       operation_node_id
       q
     =
     Some predecessor_node
     \<Longrightarrow>
     renamed_input_interface
       circuit
       replacement
       q
     =
     Some renamed_input_node
     \<Longrightarrow>
     is_well_formed_edge
       ?result
       (make_edge predecessor_node renamed_input_node q)"
    for q predecessor_node renamed_input_node
  proof -

    assume interface_qubit:
      "q \<in> subcircuit_interface_qubits replacement"

    assume predecessor:
      "predecessor_on_wire
         circuit
         operation_node_id
         q
       =
       Some predecessor_node"

    assume renamed_input:
      "renamed_input_interface
         circuit
         replacement
         q
       =
       Some renamed_input_node"

    from predecessor_on_wire_correct[OF predecessor]
    have predecessor_edge:
      "make_edge predecessor_node operation_node_id q
         \<in> edges circuit" .

    from original_edges_well_formed predecessor_edge
    have predecessor_edge_well_formed:
      "is_well_formed_edge
         circuit
         (make_edge predecessor_node operation_node_id q)"
      unfolding are_well_formed_edges_def
      by blast

    from predecessor_edge_well_formed obtain predecessor_node_value where
      predecessor_node_value:
        "nodes circuit predecessor_node =
           Some predecessor_node_value"
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
    proof

      assume equality:
        "predecessor_node = operation_node_id"

      have self_edge:
        "make_edge
           operation_node_id
           operation_node_id
           q
         \<in> edges circuit"
        using predecessor_edge equality
        by simp

      have self_relation:
        "(operation_node_id, operation_node_id)
           \<in> edge_relation circuit"
        using self_edge
        unfolding
          edge_relation_def
          make_edge_def
        by force

      have self_reachable:
        "(operation_node_id, operation_node_id)
           \<in> (edge_relation circuit)\<^sup>+"
        using self_relation
        by (rule trancl.r_into_trancl)

      from acyclic_circuit have
        "(operation_node_id, operation_node_id)
           \<notin> (edge_relation circuit)\<^sup>+"
        unfolding
          is_acyclic_circuit_def
          acyclic_def
        by blast

      with self_reachable show False
        by contradiction
    qed

    have result_predecessor:
      "nodes ?result predecessor_node =
         Some predecessor_node_value"
      using
        replace_operation_by_subcircuit_preserves_unrelated_nodes[
          OF valid_state
             valid_replacement
             predecessor_not_removed
             predecessor_node_value]
      by simp

    from renamed_input obtain local_input_node where
      input_interface:
        "input_interface replacement q =
           Some local_input_node"
    and renamed_input_node_eq:
        "renamed_input_node =
           rename_subcircuit_node_id
             circuit
             local_input_node"
      unfolding renamed_input_interface_def
      by (cases "input_interface replacement q") auto

    from replacement_valid input_interface
    obtain input_op where
      input_operation:
        "nodes
           (subgraph replacement)
           local_input_node
         =
         Some (OperationNode input_op)"
      unfolding
        is_valid_subcircuit_def
        is_first_operation_on_subcircuit_wire_def
      by blast

    have input_allocated:
      "local_input_node
         \<in> subcircuit_operation_node_ids replacement"
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
      "nodes ?result renamed_input_node =
         Some (OperationNode input_op)"
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
     \<Longrightarrow>
     renamed_output_interface
       circuit
       replacement
       q
     =
     Some renamed_output_node
     \<Longrightarrow>
     successor_on_wire
       circuit
       operation_node_id
       q
     =
     Some successor_node
     \<Longrightarrow>
     is_well_formed_edge
       ?result
       (make_edge renamed_output_node successor_node q)"
    for q renamed_output_node successor_node
  proof -

    assume interface_qubit:
      "q \<in> subcircuit_interface_qubits replacement"

    assume renamed_output:
      "renamed_output_interface
         circuit
         replacement
         q
       =
       Some renamed_output_node"

    assume successor:
      "successor_on_wire
         circuit
         operation_node_id
         q
       =
       Some successor_node"

    from successor_on_wire_correct[OF successor]
    have successor_edge:
      "make_edge operation_node_id successor_node q
         \<in> edges circuit" .

    from original_edges_well_formed successor_edge
    have successor_edge_well_formed:
      "is_well_formed_edge
         circuit
         (make_edge operation_node_id successor_node q)"
      unfolding are_well_formed_edges_def
      by blast

    from successor_edge_well_formed
    obtain successor_node_value where
      successor_node_value:
        "nodes circuit successor_node =
           Some successor_node_value"
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
    proof

      assume equality:
        "successor_node = operation_node_id"

      have self_edge:
        "make_edge
           operation_node_id
           operation_node_id
           q
         \<in> edges circuit"
        using successor_edge equality
        by simp

      have self_relation:
        "(operation_node_id, operation_node_id)
           \<in> edge_relation circuit"
        using self_edge
        unfolding
          edge_relation_def
          make_edge_def
        by force

      have self_reachable:
        "(operation_node_id, operation_node_id)
           \<in> (edge_relation circuit)\<^sup>+"
        using self_relation
        by (rule trancl.r_into_trancl)

      from acyclic_circuit have
        "(operation_node_id, operation_node_id)
           \<notin> (edge_relation circuit)\<^sup>+"
        unfolding
          is_acyclic_circuit_def
          acyclic_def
        by blast

      with self_reachable show False
        by contradiction
    qed

    have result_successor:
      "nodes ?result successor_node =
         Some successor_node_value"
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
        "output_interface replacement q =
           Some local_output_node"
    and renamed_output_node_eq:
        "renamed_output_node =
           rename_subcircuit_node_id
             circuit
             local_output_node"
      unfolding renamed_output_interface_def
      by (cases "output_interface replacement q") auto

    from replacement_valid output_interface
    obtain output_op where
      output_operation:
        "nodes
           (subgraph replacement)
           local_output_node
         =
         Some (OperationNode output_op)"
      unfolding
        is_valid_subcircuit_def
        is_last_operation_on_subcircuit_wire_def
      by blast

    have output_allocated:
      "local_output_node
         \<in> subcircuit_operation_node_ids replacement"
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
      "nodes ?result renamed_output_node =
         Some (OperationNode output_op)"
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
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "is_well_formed_circuit
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"
proof -
  let ?result =
    "fst
       (replace_operation_by_subcircuit
          circuit
          frontier
          operation_node_id
          replacement)"

  have well_formed_boundary_nodes:
    "are_well_formed_boundary_nodes ?result"
    using
      replace_operation_by_subcircuit_preserves_boundary_nodes
      valid_state valid_replacement
    by simp

  have well_formed_edges:
    "are_well_formed_edges ?result"
    using
      replace_operation_by_subcircuit_preserves_well_formed_edges
      valid_state
      acyclic_circuit
      valid_replacement
    by simp

  have well_formed_operation_nodes:
    "are_well_formed_operation_nodes ?result"
    using
      replace_operation_by_subcircuit_preserves_well_formed_operation_nodes
      valid_replacement
      valid_state
    by simp

  show ?thesis
    unfolding is_well_formed_circuit_def
    using
      well_formed_boundary_nodes
      well_formed_edges
      well_formed_operation_nodes
    by simp
qed

end
