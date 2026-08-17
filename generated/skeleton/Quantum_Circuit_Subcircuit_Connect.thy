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
  "nodes
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   nodes circuit"
  sorry

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
sorry

lemma connect_subcircuit_input_on_wire_preserves_num_qubits[simp]:
  "num_qubits
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   num_qubits circuit"
  sorry

lemma connect_subcircuit_input_on_wire_preserves_next_id[simp]:
  "next_id
     (connect_subcircuit_input_on_wire
        original_circuit operation_node replacement q circuit)
   =
   next_id circuit"
  sorry


lemma connect_subcircuit_input_on_wire_commute:
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

  sorry

interpretation connect_subcircuit_input:
  comp_fun_commute
    "connect_subcircuit_input_on_wire
       original_circuit
       operation_node
       replacement"
  sorry

lemma compatible_subcircuit_interface_qubits_finite:
  assumes compatible:
    "is_compatible_subcircuit qubits replacement"

  shows
    "finite (subcircuit_interface_qubits replacement)"

  sorry

lemma connect_subcircuit_inputs_preserves_nodes[simp]:
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

  sorry


definition connect_subcircuit_output_on_wire ::
  "quantum_circuit
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> qubit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> quantum_circuit"
  where
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
  "nodes
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   nodes circuit"
  sorry

lemma connect_subcircuit_outputs_preserve_nodes[simp]:
  assumes finite_interfaces:
    "finite (subcircuit_interface_qubits replacement)"

  shows
    "nodes
       (connect_subcircuit_outputs
          original_circuit circuit operation_node replacement)
     =
     nodes circuit"
sorry

lemma connect_subcircuit_output_on_wire_preserves_num_qubits[simp]:
  "num_qubits
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   num_qubits circuit"
  sorry

lemma connect_subcircuit_output_on_wire_preserves_next_id[simp]:
  "next_id
     (connect_subcircuit_output_on_wire
        original_circuit operation_node replacement q circuit)
   =
   next_id circuit"
  sorry


lemma connect_subcircuit_output_on_wire_commute:
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

  sorry

interpretation connect_subcircuit_output:
  comp_fun_commute
    "connect_subcircuit_output_on_wire
       original_circuit
       operation_node
       replacement"
  sorry

lemma connect_subcircuit_outputs_preserves_nodes[simp]:
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

  sorry

definition update_frontier_after_subcircuit ::
  "quantum_circuit
    \<Rightarrow> frontier
    \<Rightarrow> subcircuit
    \<Rightarrow> frontier"
where
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

  sorry

lemma update_frontier_after_subcircuit_without_output:
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

  sorry

lemma update_frontier_after_subcircuit_output_interface:
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

  sorry

lemma update_frontier_after_subcircuit_no_output_interface:
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

  sorry

end
