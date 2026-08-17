theory Quantum_Circuit_Subcircuit_Model
  imports Quantum_Circuit_Operation_Replace

begin



section \<open>Subcircuit Replacement\<close>

record subcircuit =
  subgraph :: quantum_circuit

  input_interface :: "qubit \<Rightarrow> node_id option"

  output_interface :: "qubit \<Rightarrow> node_id option"

definition subcircuit_uses_qubit ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> bool"
  where
    "subcircuit_uses_qubit subcircuit q \<longleftrightarrow>
        input_interface subcircuit q \<noteq> None
     \<or> output_interface subcircuit q \<noteq> None"


definition subcircuit_interface_qubits ::
  "subcircuit \<Rightarrow> qubit set"
  where
    "subcircuit_interface_qubits subcircuit =
       {q. input_interface subcircuit q \<noteq> None}"

definition interface_node_uses_qubit ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "interface_node_uses_qubit subcircuit q node_id \<longleftrightarrow>
       (\<exists>node.
          nodes (subgraph subcircuit) node_id = Some node
        \<and> node_uses_qubit node q)"

definition is_input_interface_node ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_input_interface_node subcircuit q node_id \<longleftrightarrow>
         input_interface subcircuit q = Some node_id
       \<and> interface_node_uses_qubit subcircuit q node_id"

definition is_output_interface_node ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_output_interface_node subcircuit q node_id \<longleftrightarrow>
         output_interface subcircuit q = Some node_id
       \<and> interface_node_uses_qubit subcircuit q node_id"


definition is_first_operation_on_subcircuit_wire ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_first_operation_on_subcircuit_wire subcircuit q node_id \<longleftrightarrow>
         (\<exists>op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op))
       \<and> (get_input_node_id q, node_id)
            \<in> wire_edge_relation (subgraph subcircuit) q"


definition is_last_operation_on_subcircuit_wire ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    "is_last_operation_on_subcircuit_wire subcircuit q node_id \<longleftrightarrow>
         (\<exists>op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op))
       \<and> (node_id, get_output_node_id q)
            \<in> wire_edge_relation (subgraph subcircuit) q"

definition subcircuit_operation_qubits ::
  "subcircuit \<Rightarrow> qubit set"
  where
    "subcircuit_operation_qubits subcircuit =
       {q.
          \<exists>node_id op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op)
          \<and> q \<in> set (op_qargs op)}"


definition is_valid_subcircuit ::
  "subcircuit \<Rightarrow> bool"
  where
    "is_valid_subcircuit subcircuit \<longleftrightarrow>
         is_valid_circuit (subgraph subcircuit)
  
       \<and> (\<forall>q.
            (input_interface subcircuit q = None)
            =
            (output_interface subcircuit q = None))
          
        \<and> (\<forall>q input_node_id.
             input_interface subcircuit q = Some input_node_id
             \<longrightarrow>
             is_first_operation_on_subcircuit_wire
               subcircuit q input_node_id)
        
        \<and> (\<forall>q output_node_id.
             output_interface subcircuit q = Some output_node_id
             \<longrightarrow>
             is_last_operation_on_subcircuit_wire
               subcircuit q output_node_id)

        \<and> subcircuit_interface_qubits subcircuit
          = subcircuit_operation_qubits subcircuit
  
       \<and> (\<forall>q input_node_id output_node_id.
            input_interface subcircuit q = Some input_node_id
            \<longrightarrow>
            output_interface subcircuit q = Some output_node_id
            \<longrightarrow>
            (input_node_id, output_node_id)
              \<in> (wire_edge_relation
                   (subgraph subcircuit) q)\<^sup>*)"

definition is_compatible_subcircuit ::
  "qubit list \<Rightarrow> subcircuit \<Rightarrow> bool"
where
  "is_compatible_subcircuit qubits subcircuit \<longleftrightarrow>
       distinct qubits
     \<and> subcircuit_interface_qubits subcircuit = set qubits
     \<and> (\<forall>q \<in> set qubits.
          input_interface subcircuit q \<noteq> None
        \<and> output_interface subcircuit q \<noteq> None)"


definition is_valid_subcircuit_replacement ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> subcircuit \<Rightarrow> bool"
  where
    "is_valid_subcircuit_replacement
        circuit operation_node_id subcircuit
     \<longleftrightarrow>
       (\<exists>op.
          nodes circuit operation_node_id =
            Some (OperationNode op)
        \<and> is_valid_subcircuit subcircuit
        \<and> num_qubits (subgraph subcircuit) =
            num_qubits circuit
        \<and> is_compatible_subcircuit
            (op_qargs op)
            subcircuit)"

definition operation_node_ids ::
  "quantum_circuit \<Rightarrow> node_id set"
  where
    "operation_node_ids circuit =
       {node_id.
          \<exists>op.
            nodes circuit node_id =
              Some (OperationNode op)}"

definition subcircuit_operation_node_ids ::
  "subcircuit \<Rightarrow> node_id set"
  where
    "subcircuit_operation_node_ids subcircuit =
       operation_node_ids (subgraph subcircuit)"

definition subcircuit_internal_edges ::
  "subcircuit \<Rightarrow> edge set"
  where
    "subcircuit_internal_edges subcircuit =
       {e \<in> edges (subgraph subcircuit).
          edge_source e
            \<in> subcircuit_operation_node_ids subcircuit
        \<and> edge_target e
            \<in> subcircuit_operation_node_ids subcircuit}"

definition rename_subcircuit_node_id ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> node_id"
  where
    "rename_subcircuit_node_id circuit local_node_id =
       NodeId
         (node_id_to_nat (next_id circuit)
          + node_id_to_nat local_node_id)"

definition rename_subcircuit_edge ::
  "quantum_circuit \<Rightarrow> edge \<Rightarrow> edge"
where
  "rename_subcircuit_edge circuit e =
     make_edge
       (rename_subcircuit_node_id
          circuit (edge_source e))
       (rename_subcircuit_node_id
          circuit (edge_target e))
       (edge_wire e)"


definition renamed_subcircuit_internal_edges ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> edge set"
where
  "renamed_subcircuit_internal_edges circuit subcircuit =
     rename_subcircuit_edge circuit
       ` subcircuit_internal_edges subcircuit"

definition renamed_input_interface ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> node_id option"
  where
    "renamed_input_interface circuit subcircuit q =
       map_option
         (rename_subcircuit_node_id circuit)
         (input_interface subcircuit q)"


definition renamed_output_interface ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> node_id option"
  where
    "renamed_output_interface circuit subcircuit q =
       map_option
         (rename_subcircuit_node_id circuit)
         (output_interface subcircuit q)"


lemma rename_subcircuit_node_id_injective:
  assumes renamed_equal:
    "rename_subcircuit_node_id circuit node_id1 =
     rename_subcircuit_node_id circuit node_id2"
  shows
    "node_id1 = node_id2"

  sorry


lemma renamed_subcircuit_node_id_is_unused:
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"
  shows
    "nodes circuit
       (rename_subcircuit_node_id circuit local_node_id)
     = None"

sorry

lemma rename_subcircuit_edge_preserves_wire:
  "edge_wire (rename_subcircuit_edge circuit e) = edge_wire e"

  sorry

lemma rename_subcircuit_edge_preserves_distinct_endpoints:
  assumes distinct_endpoints:
    "edge_source e \<noteq> edge_target e"

  shows
    "edge_source (rename_subcircuit_edge circuit e)
     \<noteq>
     edge_target (rename_subcircuit_edge circuit e)"

sorry

lemma renamed_subcircuit_internal_edge:
  assumes internal_edge:
    "e \<in> subcircuit_internal_edges subcircuit"

  shows
    "rename_subcircuit_edge circuit e
       \<in> renamed_subcircuit_internal_edges circuit subcircuit"

  sorry

lemma renamed_input_interface_node_is_unused:
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"

  and renamed_interface:
    "renamed_input_interface circuit subcircuit q =
       Some renamed_node_id"

  shows
    "nodes circuit renamed_node_id = None"

sorry

lemma renamed_output_interface_node_is_unused:
  assumes unused_above_next_id:
    "\<And>node_id.
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"

  and renamed_interface:
    "renamed_output_interface circuit subcircuit q =
       Some renamed_node_id"

  shows
    "nodes circuit renamed_node_id = None"

sorry

lemma renamed_subcircuit_edge_source:
  "edge_source (rename_subcircuit_edge circuit e) =
     rename_subcircuit_node_id circuit (edge_source e)"

  sorry

lemma renamed_subcircuit_edge_target:
  "edge_target (rename_subcircuit_edge circuit e) =
     rename_subcircuit_node_id circuit (edge_target e)"

  sorry

end
