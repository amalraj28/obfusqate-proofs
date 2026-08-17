theory Quantum_Circuit_Subcircuit_Model
  imports Quantum_Circuit_Operation_Replace

begin

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
         (\<exists>op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op))
       \<and> (get_input_node_id q, node_id)
            \<in> wire_edge_relation (subgraph subcircuit) q"

definition is_last_operation_on_subcircuit_wire ::
  "subcircuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool"
  where
    (* Checks whether node_id contains an operation and is the final
       operation node encountered before the canonical output boundary
       node on wire q. *)
    "is_last_operation_on_subcircuit_wire subcircuit q node_id \<longleftrightarrow>
         (\<exists>op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op))
       \<and> (node_id, get_output_node_id q)
            \<in> wire_edge_relation (subgraph subcircuit) q"

definition subcircuit_operation_qubits ::
  "subcircuit \<Rightarrow> qubit set"
  where
    (* Returns all qubits used by operation nodes inside the replacement
       fragment. Boundary nodes do not contribute to this set. *)
    "subcircuit_operation_qubits subcircuit =
       {q.
          \<exists>node_id op.
            nodes (subgraph subcircuit) node_id =
              Some (OperationNode op)
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
    (* Returns exactly the node IDs that store operation nodes.
       This definition depends only on the graph contents and not on a
       separate next_id allocation invariant. *)
    "operation_node_ids circuit =
       {node_id.
          \<exists>op.
            nodes circuit node_id =
              Some (OperationNode op)}"

definition subcircuit_operation_node_ids ::
  "subcircuit \<Rightarrow> node_id set"
  where
    (* Returns the operation nodes belonging to the replacement fragment.
       These are the nodes that will be copied into the host circuit. *)
    "subcircuit_operation_node_ids subcircuit =
       operation_node_ids (subgraph subcircuit)"

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
          edge_source e
            \<in> subcircuit_operation_node_ids subcircuit
        \<and> edge_target e
            \<in> subcircuit_operation_node_ids subcircuit}"

definition rename_subcircuit_node_id ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> node_id"
  where
    (* Renames a subcircuit-local node ID into a fresh host-circuit ID.
  
       Every renamed ID begins at or above next_id of the host circuit,
       so it cannot collide with any existing host node when the host
       satisfies its node-allocation invariant.
    *)
    "rename_subcircuit_node_id circuit local_node_id =
       NodeId
         (node_id_to_nat (next_id circuit)
          + node_id_to_nat local_node_id)"

definition rename_subcircuit_edge ::
  "quantum_circuit \<Rightarrow> edge \<Rightarrow> edge"
where
  (* Renames both endpoints of a subcircuit edge while preserving its
     wire label. *)
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
  (* Returns the internal edge set of the replacement fragment after
     translating every local node ID into the fresh host namespace. *)
  "renamed_subcircuit_internal_edges circuit subcircuit =
     rename_subcircuit_edge circuit
       ` subcircuit_internal_edges subcircuit"

definition renamed_input_interface ::
  "quantum_circuit \<Rightarrow> subcircuit \<Rightarrow> qubit \<Rightarrow> node_id option"
  where
    (* Returns the fresh host-circuit ID corresponding to the
       subcircuit's input interface node on wire q. *)
    "renamed_input_interface circuit subcircuit q =
       map_option
         (rename_subcircuit_node_id circuit)
         (input_interface subcircuit q)"

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
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"
  shows
    "nodes circuit
       (rename_subcircuit_node_id circuit local_node_id)
     = None"

proof (rule unused_above_next_id)
  show
    "node_id_to_nat
       (rename_subcircuit_node_id circuit local_node_id)
     \<ge> node_id_to_nat (next_id circuit)"

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
    "edge_source (rename_subcircuit_edge circuit e)
     \<noteq>
     edge_target (rename_subcircuit_edge circuit e)"

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
    "rename_subcircuit_edge circuit e
       \<in> renamed_subcircuit_internal_edges circuit subcircuit"

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
       node_id_to_nat node_id
         \<ge> node_id_to_nat (next_id circuit)
       \<Longrightarrow> nodes circuit node_id = None"

  and renamed_interface:
    "renamed_input_interface circuit subcircuit q =
       Some renamed_node_id"

  shows
    "nodes circuit renamed_node_id = None"

proof (cases "input_interface subcircuit q")

  case None

  then show ?thesis
    using renamed_interface
    unfolding renamed_input_interface_def
    by simp

next

  case (Some local_node_id)

  have renamed_node_id:
    "renamed_node_id =
       rename_subcircuit_node_id circuit local_node_id"

    using renamed_interface Some
    unfolding renamed_input_interface_def
    by simp

  show ?thesis
    unfolding renamed_node_id
    using unused_above_next_id
    by (rule renamed_subcircuit_node_id_is_unused)

qed

lemma renamed_output_interface_node_is_unused:
  (* If a renamed output interface contains node_id, then node_id is
     unused in the host circuit.

     As with the input interface, the output interface node is mapped
     through rename_subcircuit_node_id and is therefore placed at or
     above next_id of the host circuit.
  *)
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

proof (cases "output_interface subcircuit q")

  case None

  then show ?thesis
    using renamed_interface
    unfolding renamed_output_interface_def
    by simp

next

  case (Some local_node_id)

  have renamed_node_id:
    "renamed_node_id =
       rename_subcircuit_node_id circuit local_node_id"

    using renamed_interface Some
    unfolding renamed_output_interface_def
    by simp

  show ?thesis
    unfolding renamed_node_id
    using unused_above_next_id
    by (rule renamed_subcircuit_node_id_is_unused)

qed

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

end
