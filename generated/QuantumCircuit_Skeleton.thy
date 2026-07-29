theory QuantumCircuit_Skeleton
  imports Complex_Main

begin

datatype qubit = Qubit nat
datatype node_id = NodeId nat

datatype gate =
  Gate_H
  | Gate_X
  | Gate_Y
  | Gate_Z
  | Gate_CNOT
  | Gate_CCNOT
  | Gate_RZ real

record operation =
  op_gate :: gate
  op_qargs :: "qubit list"

fun gate_arity :: "gate \<Rightarrow> nat" where
  "gate_arity Gate_H = 1"
| "gate_arity Gate_X = 1"
| "gate_arity Gate_Y = 1"
| "gate_arity Gate_Z = 1"
| "gate_arity (Gate_RZ \<Theta>) = 1"
| "gate_arity Gate_CNOT = 2"
| "gate_arity Gate_CCNOT = 3"

definition is_valid_operation :: "operation \<Rightarrow> bool" where

"is_valid_operation op \<longleftrightarrow>
     length (op_qargs op) = gate_arity (op_gate op) \<and>
     distinct (op_qargs op)"


datatype circuit_node =
  InputNode qubit
  | OutputNode qubit
  | OperationNode operation

record edge =
  edge_source :: node_id
  edge_target :: node_id
  edge_wire :: qubit

definition make_edge :: "node_id \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> edge" where
  "make_edge u v q = \<lparr> edge_source = u, edge_target = v, edge_wire = q \<rparr>"

record quantum_circuit =
  num_qubits :: nat
  nodes :: "node_id \<Rightarrow> circuit_node option"
  edges :: "edge set"
  next_id :: node_id

fun get_qubit_index :: "qubit \<Rightarrow> nat" where
  "get_qubit_index (Qubit n) = n"

fun node_id_to_nat :: "node_id \<Rightarrow> nat" where
  "node_id_to_nat (NodeId n) = n"




definition get_input_node_id :: "qubit \<Rightarrow> node_id" where
  "get_input_node_id q = NodeId (2 * get_qubit_index q)"

definition get_output_node_id :: "qubit \<Rightarrow> node_id" where
  "get_output_node_id q = NodeId (2 * get_qubit_index q + 1)"

definition get_first_operation_id :: "nat \<Rightarrow> node_id" where
  "get_first_operation_id n = NodeId (2 * n)"

lemma input_output_ids_distinct[simp]:
  "get_input_node_id q \<noteq> get_output_node_id r"
  sorry

lemma input_node_id_injective:
  "get_input_node_id q = get_input_node_id r \<Longrightarrow> q = r"
  sorry

lemma output_node_id_injective:
  "get_output_node_id q = get_output_node_id r \<Longrightarrow> q = r"
  sorry


definition initial_nodes :: "nat \<Rightarrow> node_id \<Rightarrow> circuit_node option" where
  "initial_nodes number_of_qubits node_number = 
    (let node_index = node_id_to_nat node_number in
      if node_index < 2 * number_of_qubits then
        if even node_index
        then Some (InputNode (Qubit (node_index div 2)))
        else Some (OutputNode (Qubit (node_index div 2)))
      else None
    )
  "

definition initial_edges :: "nat \<Rightarrow> edge set" where
  "initial_edges number_of_qubits =
     {
        make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)
        | qubit_number. qubit_number < number_of_qubits
     }
  "

definition initial_circuit :: "nat \<Rightarrow> quantum_circuit" where
  "initial_circuit number_of_qubits =
     \<lparr> num_qubits = number_of_qubits,
       nodes = initial_nodes number_of_qubits,
       edges = initial_edges number_of_qubits,
       next_id = get_first_operation_id number_of_qubits 
     \<rparr>
  "


lemma initial_circuit_num_qubits[simp]:
  "num_qubits (initial_circuit number_of_qubits) = number_of_qubits"
  sorry

lemma initial_circuit_next_id[simp]:
  "next_id (initial_circuit number_of_qubits) =
   get_first_operation_id number_of_qubits"
  sorry

lemma initial_circuit_input_node:
  assumes "qubit_number < number_of_qubits"
  shows "nodes (initial_circuit number_of_qubits)
          (get_input_node_id (Qubit qubit_number))
        = Some (InputNode (Qubit qubit_number))"
  sorry

lemma initial_circuit_output_node:
  assumes "qubit_number < number_of_qubits"
  shows "nodes (initial_circuit number_of_qubits)
          (get_output_node_id (Qubit qubit_number))
        = Some (OutputNode (Qubit qubit_number))"
  sorry

lemma initial_circuit_has_wire_edge:
  assumes "qubit_number < number_of_qubits"
  shows "make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)
        \<in> edges (initial_circuit number_of_qubits)"
  sorry

lemma make_edges_on_different_wires_unequal:
  assumes wires_different:
    "first_wire \<noteq> second_wire"
  shows
    "make_edge first_source first_target first_wire
     \<noteq>
     make_edge second_source second_target second_wire"
  sorry




definition node_exists :: "quantum_circuit \<Rightarrow> node_id \<Rightarrow> bool" where
  "node_exists circuit node_id \<longleftrightarrow>
     nodes circuit node_id \<noteq> None
  "

fun node_uses_qubit :: "circuit_node \<Rightarrow> qubit \<Rightarrow> bool" where
  "node_uses_qubit (InputNode q) r = (q = r)"
| "node_uses_qubit (OutputNode q) r = (q = r)"
| "node_uses_qubit (OperationNode op) r = (r \<in> set (op_qargs op))"



definition qubit_in_circuit :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> bool" where
  "qubit_in_circuit circuit q \<longleftrightarrow>
     get_qubit_index q < num_qubits circuit"

definition is_well_formed_edge :: "quantum_circuit \<Rightarrow> edge \<Rightarrow> bool" where
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
  "are_well_formed_edges circuit \<longleftrightarrow>
     (\<forall>e \<in> edges circuit. is_well_formed_edge circuit e
     )
  "

definition edge_relation :: "quantum_circuit \<Rightarrow> (node_id \<times> node_id) set" where
  "edge_relation circuit =
     {(source_id, target_id).
        \<exists>e \<in> edges circuit.
          edge_source e = source_id
        \<and> edge_target e = target_id}"

definition is_acyclic_circuit :: "quantum_circuit \<Rightarrow> bool" where
  "is_acyclic_circuit circuit \<longleftrightarrow> acyclic (edge_relation circuit)"

definition wire_edge_relation :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> (node_id \<times> node_id) set" where
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
  "has_unique_wire_predecessor circuit q node_id \<longleftrightarrow>
     (\<exists>! predecessor_id. \<comment>\<open>\<exists>! means exactly one\<close>
        (predecessor_id, node_id)
          \<in> wire_edge_relation circuit q)"

definition has_unique_wire_successor :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> bool" where
  "has_unique_wire_successor circuit q node_id \<longleftrightarrow>
     (\<exists>! successor_id. \<comment>\<open>\<exists>! means exactly one\<close>
        (node_id, successor_id)
          \<in> wire_edge_relation circuit q)"

lemma wire_edge_implies_wire_reaches:
  assumes direct_edge:
    "(source_id, target_id) \<in> wire_edge_relation circuit q"

shows
  "wire_reaches circuit q source_id target_id"

  sorry



definition nodes_comparable_on_wire :: "quantum_circuit \<Rightarrow> qubit \<Rightarrow> bool" where
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
  "all_wires_linear circuit \<longleftrightarrow>
     (\<forall>q.
        qubit_in_circuit circuit q
        \<longrightarrow> wire_is_linear circuit q)"

definition all_wire_nodes_comparable :: "quantum_circuit \<Rightarrow> bool" where
  "all_wire_nodes_comparable circuit \<longleftrightarrow>
     (\<forall>q.
        qubit_in_circuit circuit q
        \<longrightarrow> nodes_comparable_on_wire circuit q)"

lemma initial_circuit_nodes_comparable_on_wire:
  assumes valid_qubit:
    "qubit_in_circuit (initial_circuit number_of_qubits) q"
  shows
    "nodes_comparable_on_wire
       (initial_circuit number_of_qubits)
       q"
  sorry

lemma initial_circuit_all_wire_nodes_comparable:
  "all_wire_nodes_comparable
     (initial_circuit number_of_qubits)"

  sorry

definition operation_in_circuit :: "quantum_circuit \<Rightarrow> operation \<Rightarrow> bool" where
  "operation_in_circuit circuit op \<longleftrightarrow>
      is_valid_operation op
    \<and> (\<forall>q \<in> set (op_qargs op). qubit_in_circuit circuit q)
  "

definition are_well_formed_operation_nodes :: "quantum_circuit \<Rightarrow> bool" where
  "are_well_formed_operation_nodes circuit \<longleftrightarrow>
     (\<forall>node_id op.
        nodes circuit node_id = Some (OperationNode op) \<longrightarrow>
        operation_in_circuit circuit op
     )
  "


definition are_well_formed_boundary_nodes :: "quantum_circuit \<Rightarrow> bool" where

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
  "is_well_formed_circuit circuit \<longleftrightarrow>
       are_well_formed_boundary_nodes circuit
     \<and> are_well_formed_edges circuit
     \<and> are_well_formed_operation_nodes circuit
  "

definition is_valid_circuit :: "quantum_circuit \<Rightarrow> bool" where
  "is_valid_circuit circuit \<longleftrightarrow>
      is_well_formed_circuit circuit
    \<and> is_acyclic_circuit circuit
    \<and> all_wires_linear circuit"

lemma initial_edges_cases:
  assumes "e \<in> edges (initial_circuit number_of_qubits)"
  obtains qubit_number where
    "qubit_number < number_of_qubits"
    "e = make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)"
  sorry

lemma initial_edge_relation_cases:
  assumes relation_pair:
    "(source_id, target_id) \<in> edge_relation (initial_circuit number_of_qubits)"

obtains qubit_number where
  "qubit_number < number_of_qubits"
  "source_id = get_input_node_id (Qubit qubit_number)"
  "target_id = get_output_node_id (Qubit qubit_number)"

sorry

lemma initial_edge_relation_cannot_compose:
  assumes first_edge:
    "(first_source, middle_node)
       \<in> edge_relation (initial_circuit number_of_qubits)"

assumes second_edge:
  "(middle_node, second_target)
       \<in> edge_relation (initial_circuit number_of_qubits)"

shows False

sorry

lemma initial_circuit_has_no_operation_nodes:
  "nodes (initial_circuit number_of_qubits) node_id \<noteq> Some (OperationNode op)"
  sorry

lemma initial_circuit_is_well_formed:
  "is_well_formed_circuit (initial_circuit number_of_qubits)"

sorry

lemma initial_circuit_is_acyclic:
  "is_acyclic_circuit (initial_circuit number_of_qubits)"

sorry

lemma initial_circuit_has_linear_wires:
  "all_wires_linear (initial_circuit number_of_qubits)"
  sorry





definition increment_node_id :: "node_id \<Rightarrow> node_id" where
  "increment_node_id current_node_id = NodeId (node_id_to_nat current_node_id + 1)"

lemma node_id_to_nat_increment_node_id[simp]:
  "node_id_to_nat (increment_node_id current_node_id) = node_id_to_nat current_node_id + 1"
  sorry

lemma increment_node_id_not_same[simp]:
  "increment_node_id current_node_id \<noteq> current_node_id"
  sorry



type_synonym frontier = "qubit \<Rightarrow> node_id"

definition initial_frontier :: frontier where
  "initial_frontier q = get_input_node_id q"

definition update_frontier :: "frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> frontier" where
  "update_frontier frontier q new_node_id = frontier(q := new_node_id)"

lemma update_frontier_same[simp]:
  "update_frontier frontier q new_node_id q = new_node_id"
  sorry

lemma update_frontier_other[simp]:
  assumes "other_q \<noteq> q"
  shows
    "update_frontier frontier q new_node_id other_q =
     frontier other_q"
  sorry



definition is_valid_frontier :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
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
  "next_id_is_unused circuit \<longleftrightarrow> nodes circuit (next_id circuit) = None"

definition all_existing_node_ids_below_next_id ::
  "quantum_circuit \<Rightarrow> bool"
  where
    "all_existing_node_ids_below_next_id circuit \<longleftrightarrow>
     (\<forall>existing_node_id.
        nodes circuit existing_node_id \<noteq> None
        \<longrightarrow>
        node_id_to_nat existing_node_id
          < node_id_to_nat (next_id circuit))"

definition is_valid_construction_state :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  "is_valid_construction_state circuit frontier \<longleftrightarrow>
      is_well_formed_circuit circuit
        \<and> is_valid_frontier circuit frontier
        \<and> next_id_is_unused circuit
        \<and> all_existing_node_ids_below_next_id circuit"



definition insert_node :: "node_id \<Rightarrow> circuit_node \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  "insert_node node_id new_node circuit =
     circuit\<lparr>nodes := (nodes circuit)(node_id := Some new_node)\<rparr>"

definition insert_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  "insert_edge e circuit =
     circuit\<lparr>edges := insert e (edges circuit)\<rparr>"

definition delete_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  "delete_edge e circuit =
     circuit\<lparr>edges := edges circuit - {e}\<rparr>"

lemma nodes_insert_node_same[simp]:
  "nodes (insert_node node_id node circuit) node_id = Some node"
  sorry

lemma valid_frontier_has_unique_successor:
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

assumes valid_q:
  "qubit_in_circuit circuit q"

shows
  "has_unique_wire_successor circuit q (frontier q)"
  sorry

lemma nodes_insert_node_other[simp]:
  assumes "other_node_id \<noteq> node_id"
  shows "nodes (insert_node node_id node circuit) other_node_id =
         nodes circuit other_node_id"
  sorry

lemma insert_node_at_unused_id_preserves_valid_frontier:
  assumes valid_frontier: "is_valid_frontier circuit frontier"

assumes node_id_unused: "nodes circuit new_node_id = None"

shows
  "is_valid_frontier 
         (insert_node new_node_id new_node circuit)
         frontier"

sorry

lemma update_next_id_preserves_valid_frontier:

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

shows 
  "is_valid_frontier (circuit \<lparr> next_id := new_next_id \<rparr>) frontier"

  sorry

lemma edges_insert_edge[simp]:
  "edges (insert_edge e circuit) = insert e (edges circuit)"
  sorry

lemma edges_delete_edge[simp]:
  "edges (delete_edge e circuit) = edges circuit - {e}"
  sorry



lemma initial_frontier_is_valid:
  "is_valid_frontier (initial_circuit number_of_qubits) initial_frontier"

sorry

lemma initial_next_id_is_unused:
  "next_id_is_unused (initial_circuit number_of_qubits)"
  sorry

lemma initial_existing_node_ids_are_below_next_id:
  "all_existing_node_ids_below_next_id (initial_circuit number_of_qubits)"

  sorry


definition splice_wire_without_updating_frontier ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> quantum_circuit" where
  "splice_wire_without_updating_frontier circuit frontier q new_node_id =
     (let old_node_id = frontier q;
          out_node_id = get_output_node_id q;
          old_edge = make_edge old_node_id out_node_id q;
          new_in_edge = make_edge old_node_id new_node_id q;
          new_out_edge = make_edge new_node_id out_node_id q
      in
        insert_edge new_out_edge
          (insert_edge new_in_edge
            (delete_edge old_edge circuit)))"

definition splice_wire ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> quantum_circuit \<times> frontier"
  where
    "splice_wire circuit frontier q new_node_id = (
         splice_wire_without_updating_frontier circuit frontier q new_node_id,
         update_frontier frontier q new_node_id
  )"

lemma fst_splice_wire:
  "fst (splice_wire circuit frontier q new_node_id) =
   splice_wire_without_updating_frontier circuit frontier q new_node_id"
  sorry

lemma snd_splice_wire:
  "snd (splice_wire circuit frontier q new_node_id) =
   update_frontier frontier q new_node_id"
  sorry

lemma edges_splice_wire_without_updating_frontier:
  "edges
      (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
   =
   insert
      (make_edge new_node_id (get_output_node_id q) q)
      (insert
          (make_edge (frontier q) new_node_id q)
          (edges circuit -
             {make_edge
                (frontier q)
                (get_output_node_id q)
                q}))"
  sorry

lemma splice_wire_contains_new_output_edge:
  "make_edge
      new_node_id
      (get_output_node_id q)
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  sorry

lemma splice_wire_contains_new_input_edge:
  "make_edge
      (frontier q)
      new_node_id
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  sorry

lemma splice_wire_preserves_output_edge_on_other_wire:
  assumes different_wires:
    "other_q \<noteq> q"

assumes old_output_edge_exists:
  "make_edge
       (frontier other_q)
       (get_output_node_id other_q)
       other_q
     \<in> edges circuit"

shows
  "make_edge
       (frontier other_q)
       (get_output_node_id other_q)
       other_q
     \<in> edges
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)"

  sorry

lemma splice_wire_preserves_nodes[simp]:
  "nodes (fst (splice_wire circuit frontier q new_node_id)) node_id = nodes circuit node_id"
  sorry

lemma splice_wire_without_updating_frontier_preserves_num_qubits[simp]:
  "num_qubits 
     (splice_wire_without_updating_frontier circuit frontier q new_node_id)
   =
   num_qubits circuit"
  sorry

lemma splice_wire_preserves_num_qubits[simp]:
  "num_qubits (fst (splice_wire circuit frontier q new_node_id)) = num_qubits circuit"
  sorry

lemma splice_wire_preserves_other_wire_relation:
  assumes "q \<noteq> current_wire"
  shows
    "wire_edge_relation
       (fst
         (splice_wire
           circuit frontier current_wire new_node_id))
       q
     =
     wire_edge_relation circuit q"

  sorry

lemma splice_wire_preserves_valid_frontier:

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

assumes new_node_exists:
  "nodes circuit new_node_id = Some new_node"

assumes new_node_uses_wire:
  "node_uses_qubit new_node q"

assumes new_node_not_frontier:
  "new_node_id \<noteq> frontier q"

assumes new_node_has_no_other_successor:
  "\<And>successor_id.
       (new_node_id, successor_id)
         \<in> wire_edge_relation circuit q
       \<Longrightarrow> successor_id = get_output_node_id q"

shows
  "is_valid_frontier
       (fst (splice_wire circuit frontier q new_node_id))
       (snd (splice_wire circuit frontier q new_node_id))"

sorry

lemma wire_edge_relation_update_next_id[simp]:
  "wire_edge_relation (circuit\<lparr>next_id := new_next_id\<rparr>) q
   =
   wire_edge_relation circuit q"

  sorry

lemma wire_edge_relation_after_splice_same_wire:
  "wire_edge_relation
     (splice_wire_without_updating_frontier
      circuit frontier q new_node_id)
     q
   =
   (wire_edge_relation circuit q
      - {(frontier q, get_output_node_id q)})
      \<union> {(frontier q, new_node_id),
      (new_node_id, get_output_node_id q)}"

sorry

lemma wire_edge_relation_after_splice_other_wire:
  assumes different_wire:
    "other_q \<noteq> q"

shows
  "wire_edge_relation
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       other_q
     =
     wire_edge_relation circuit other_q"

sorry

lemma old_wire_edge_reaches_after_splice:
  assumes old_edge:
    "(source_id, target_id)
       \<in> wire_edge_relation circuit q"

shows
  "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       source_id
       target_id"

sorry

lemma old_wire_reaches_after_splice:
  assumes old_reachability:
    "wire_reaches circuit q source_id target_id"

shows
  "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       source_id
       target_id"

sorry

lemma old_nodes_comparable_after_splice:
  assumes old_nodes_comparable:
    "nodes_comparable_on_wire circuit q"

assumes node_a_lookup:
  "nodes circuit node_a = Some node_a_value"

assumes node_b_lookup:
  "nodes circuit node_b = Some node_b_value"

assumes node_a_uses_q:
  "node_uses_qubit node_a_value q"

assumes node_b_uses_q:
  "node_uses_qubit node_b_value q"

shows
  "node_a = node_b
     \<or> wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_a node_b
     \<or> wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_b node_a"

sorry

fun splice_wires ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> qubit list \<Rightarrow> node_id \<Rightarrow>
   quantum_circuit \<times> frontier" where
  "splice_wires circuit frontier [] new_node_id = (circuit, frontier)"
| "splice_wires circuit frontier (q # qs) new_node_id =
      (
        let (updated_circuit, updated_frontier) = 
            splice_wire circuit frontier q new_node_id in
                splice_wires updated_circuit updated_frontier qs new_node_id
      )
  "


definition insert_operation ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> operation \<Rightarrow> quantum_circuit \<times> frontier"
  where
    "insert_operation circuit frontier op =
     (let new_node_id = next_id circuit;

          circuit_with_node =
            insert_node new_node_id (OperationNode op) circuit;
            \<comment>\<open>Insert the new operation node into the node table (nodes field of the quantum_circuit record) using the fresh node ID\<close>

          spliced_result =
            splice_wires
              circuit_with_node
              frontier
              (op_qargs op)
              new_node_id;
            \<comment>\<open>Rewire every qubit used by the operation around the new node\<close>

          spliced_circuit = fst spliced_result;
          updated_frontier = snd spliced_result;
            \<comment>\<open>Extract the rewired circuit and updated frontier map\<close>

          final_circuit =
            spliced_circuit
              \<lparr>next_id := increment_node_id new_node_id\<rparr>
            \<comment>\<open>Advance next_id to the next unused global node ID\<close>

      in
        (final_circuit, updated_frontier))"

lemma splice_wires_preserve_nodes[simp]:
  "nodes
     (fst (splice_wires circuit frontier qs new_node_id))
     node_id
   = nodes circuit node_id"

sorry

lemma splice_wires_preserves_unaffected_wire_relation:
  assumes unaffected_wire:
    "q \<notin> set qs"

shows
  "wire_edge_relation
       (fst (splice_wires circuit frontier qs new_node_id))
       q
     =
     wire_edge_relation circuit q"

  sorry

lemma splice_wires_updates_affected_wire_relation:
  assumes distinct_wires:
    "distinct qs"

assumes affected_wire:
  "q \<in> set qs"

shows
  "wire_edge_relation
         (fst (splice_wires circuit frontier qs new_node_id))
         q
       =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
          (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

  sorry

lemma edges_splice_wires_cases:
  assumes distinct_wires:
    "distinct qs"

assumes edge_in_result:
  "e \<in> edges
       (fst (splice_wires circuit frontier qs new_node_id))"

shows
  "e \<in> edges circuit
     \<or> (\<exists>q \<in> set qs.
          e = make_edge (frontier q) new_node_id q)
     \<or> (\<exists>q \<in> set qs.
          e = make_edge
                new_node_id
                (get_output_node_id q)
                q)"

  sorry

lemma splice_wires_preserve_valid_frontier:
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

assumes new_node_exists:
  "nodes circuit new_node_id = Some new_node"

assumes new_node_uses_all_wires:
  "\<forall>q \<in> set qs. node_uses_qubit new_node q"

assumes distinct_wires:
  "distinct qs"

assumes new_node_not_frontiers:
  "\<forall>q \<in> set qs. new_node_id \<noteq> frontier q"

assumes new_node_has_no_other_successors:
  "\<forall>q \<in> set qs.
         (\<forall>successor_id.
            (new_node_id, successor_id)
              \<in> wire_edge_relation circuit q
            \<longrightarrow> successor_id = get_output_node_id q)"

shows
  "is_valid_frontier \<comment>\<open>The final frontier correctly describes the final circuit\<close>
         (fst (splice_wires circuit frontier qs new_node_id))
         (snd (splice_wires circuit frontier qs new_node_id))"

  sorry

lemma insert_operation_preserves_valid_frontier:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

assumes operation_valid_for_circuit:
  "operation_in_circuit circuit op"

shows "is_valid_frontier
    (fst (insert_operation circuit frontier op))
    (snd (insert_operation circuit frontier op))"

sorry

lemma insert_operation_new_node:
  "nodes (fst (insert_operation circuit frontier op))
         (next_id circuit)
   = Some (OperationNode op)"

sorry

lemma insert_operation_preserves_other_nodes:
  assumes different_node_id:
    "other_node_id \<noteq> next_id circuit"

shows
  "nodes
       (fst (insert_operation circuit frontier op))
       other_node_id
     =
     nodes circuit other_node_id"
sorry

lemma insert_operation_next_id[simp]:
  "next_id (fst (insert_operation circuit frontier op)) =
   increment_node_id (next_id circuit)"

sorry

lemma insert_operation_preserves_node_id_allocation:
  assumes valid_allocation:
    "all_existing_node_ids_below_next_id circuit"

shows
  "all_existing_node_ids_below_next_id
       (fst (insert_operation circuit frontier op))"

sorry

lemma insert_operation_num_qubits[simp]:
  "num_qubits (fst (insert_operation circuit frontier op)) =
   num_qubits circuit"

sorry

lemma insert_operation_preserves_well_formed_circuit:
  assumes circuit_well_formed:
    "is_well_formed_circuit circuit"

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

assumes next_id_unused:
  "next_id_is_unused circuit"

assumes valid_allocation:
  "all_existing_node_ids_below_next_id circuit"

assumes operation_valid_for_circuit:
  "operation_in_circuit circuit op"

shows
  "is_well_formed_circuit
       (fst (insert_operation circuit frontier op))"

sorry

lemma insert_operation_preserves_valid_construction_state:

assumes valid_state:
  "is_valid_construction_state circuit frontier"

assumes valid_operation:
  "operation_in_circuit circuit op"

shows
  "is_valid_construction_state
        (fst (insert_operation circuit frontier op))
        (snd (insert_operation circuit frontier op))"

sorry

lemma wire_node_reaches_frontier_or_is_output:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes frontier_valid:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes node_lookup:
  "nodes circuit node_id = Some node_value"

assumes node_uses_q:
  "node_uses_qubit node_value q"

assumes frontier_unique_successor:
  "has_unique_wire_successor circuit q (frontier q)"

shows
  "node_id = get_output_node_id q
       \<or> node_id = frontier q
       \<or> wire_reaches circuit q node_id (frontier q)"

sorry

lemma subdividing_final_edge_preserves_old_reachability:
  assumes old_reachability:
    "wire_reaches circuit q node_a node_b"

assumes output_has_no_successor:
  "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "wire_reaches updated_circuit q node_a node_b"

sorry

lemma subdividing_final_edge_preserves_wire_comparability:
  assumes comparable_before:
    "nodes_comparable_on_wire circuit q"

assumes circuit_well_formed:
  "is_well_formed_circuit circuit"

assumes linear_before:
  "wire_is_linear circuit q"

assumes frontier_valid:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused:
  "nodes circuit new_node_id = None"

assumes new_node_exists_after:
  "nodes updated_circuit new_node_id = Some new_node"

assumes new_node_uses_q:
  "node_uses_qubit new_node q"

assumes old_nodes_unchanged:
  "\<And>node_id.
         node_id \<noteq> new_node_id
         \<Longrightarrow> nodes updated_circuit node_id =
             nodes circuit node_id"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
         insert
           (new_node_id, get_output_node_id q)
           (insert
             (frontier q, new_node_id)
             (wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}))"

shows
  "nodes_comparable_on_wire updated_circuit q"

sorry

lemma subdividing_final_edge_preserves_input_boundary:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused_before:
  "nodes circuit new_node_id = None"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
           insert
             (new_node_id, get_output_node_id q)
             (insert
               (frontier q, new_node_id)
               (wire_edge_relation circuit q -
                  {(frontier q, get_output_node_id q)}))"

assumes new_node_not_input:
  "new_node_id \<noteq> get_input_node_id q"

shows
  "(\<nexists>predecessor_id.
            (predecessor_id, get_input_node_id q)
              \<in> wire_edge_relation updated_circuit q)
         \<and>
         has_unique_wire_successor
           updated_circuit q (get_input_node_id q)"

sorry

lemma subdividing_final_edge_preserves_output_no_successor:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_not_output:
  "new_node_id \<noteq> get_output_node_id q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation updated_circuit q"

sorry

lemma subdividing_final_edge_preserves_output_predecessor:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_not_output:
  "new_node_id \<noteq> get_output_node_id q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "has_unique_wire_predecessor
       updated_circuit q (get_output_node_id q)"

sorry

lemma subdividing_final_edge_preserves_operation_node_degrees:
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused_before:
  "nodes circuit new_node_id = None"

assumes new_node_exists_after:
  "nodes updated_circuit new_node_id =
         Some (OperationNode new_op)"

assumes new_node_uses_q:
  "node_uses_qubit (OperationNode new_op) q"

assumes circuit_well_formed:
  "is_well_formed_circuit circuit"

assumes old_nodes_unchanged:
  "\<And>node_id.
         node_id \<noteq> new_node_id
         \<Longrightarrow> nodes updated_circuit node_id =
             nodes circuit node_id"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
         insert
           (new_node_id, get_output_node_id q)
           (insert
             (frontier q, new_node_id)
             (wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}))"

shows
  "\<forall>node_id stored_op.
         nodes updated_circuit node_id =
           Some (OperationNode stored_op)
         \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
         \<longrightarrow> has_unique_wire_predecessor
               updated_circuit q node_id
           \<and> has_unique_wire_successor
               updated_circuit q node_id"

sorry

lemma insert_operation_preserves_wire_linearity:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

assumes linear_before:
  "all_wires_linear circuit"

shows
  "all_wires_linear
           (fst (insert_operation circuit frontier op))"

  sorry

lemma insert_operation_preserves_acyclicity:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"
    and operation_valid:
    "operation_in_circuit circuit op"
    and acyclic:
    "is_acyclic_circuit circuit"
    and linear_before:
    "all_wires_linear circuit"
  shows
    "is_acyclic_circuit
       (fst (insert_operation circuit frontier op))"

sorry

lemma insert_operation_preserves_valid_quantum_circuit:
  assumes valid_circuit:
    "is_valid_circuit circuit"

assumes valid_state:
  "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

shows
  "is_valid_circuit
       (fst (insert_operation circuit frontier op))"
  sorry

lemma initial_construction_state_is_valid:
  "is_valid_construction_state (initial_circuit number_of_qubits) initial_frontier"

  sorry


definition incoming_edge ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> edge option"
  where
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
  "predecessor_on_wire circuit node_id q =
     map_option edge_source
       (incoming_edge circuit node_id q)"

definition successor_on_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> node_id option"
where
  "successor_on_wire circuit node_id q =
     map_option edge_target
       (outgoing_edge circuit node_id q)"

lemma incoming_edge_correct:
  "incoming_edge circuit node_id q = Some e
   \<Longrightarrow> e \<in> edges circuit
     \<and> edge_target e = node_id
     \<and> edge_wire e = q"
  sorry

lemma outgoing_edge_correct:
  "outgoing_edge circuit node_id q = Some e
   \<Longrightarrow> e \<in> edges circuit
     \<and> edge_source e = node_id
     \<and> edge_wire e = q"

sorry

lemma predecessor_on_wire_correct:
  "predecessor_on_wire circuit node_id q = Some predecessor
   \<Longrightarrow> make_edge predecessor node_id q \<in> edges circuit"

sorry

lemma successor_on_wire_correct:
  "successor_on_wire circuit node_id q = Some successor
   \<Longrightarrow> make_edge node_id successor q \<in> edges circuit"

sorry

lemma predecessor_on_wire_not_self:
  assumes acyclic:
    "is_acyclic_circuit circuit"

  assumes predecessor:
    "predecessor_on_wire circuit node_id q =
       Some predecessor_node"

  shows
    "predecessor_node \<noteq> node_id"
sorry

lemma successor_on_wire_not_self:
  assumes acyclic:
    "is_acyclic_circuit circuit"

  assumes successor:
    "successor_on_wire circuit node_id q =
       Some successor_node"

  shows
    "successor_node \<noteq> node_id"
sorry


definition reconnect_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
where
  "reconnect_wire original_circuit node_id q current_circuit =
     (case
        (predecessor_on_wire original_circuit node_id q,
         successor_on_wire original_circuit node_id q)
      of
        (Some predecessor, Some successor) \<Rightarrow>
          insert_edge
            (make_edge predecessor successor q)
            (delete_edge
              (make_edge node_id successor q)
              (delete_edge
                (make_edge predecessor node_id q)
                current_circuit))
      | _ \<Rightarrow> current_circuit)"

definition delete_operation ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> quantum_circuit"
where
  "delete_operation circuit node_id =
     (case nodes circuit node_id of
        Some (OperationNode op) \<Rightarrow>
          (let
             reconnected_circuit =
               fold
                 (reconnect_wire circuit node_id)
                 (op_qargs op)
                 circuit
           in
             reconnected_circuit
               \<lparr>nodes :=
                  (nodes reconnected_circuit)
                    (node_id := None)\<rparr>)
      | _ \<Rightarrow> circuit)"

lemma reconnect_wire_preserves_nodes[simp]:
  "nodes
     (reconnect_wire original_circuit operation_node_id q circuit)
     node_id
   =
   nodes circuit node_id"

  sorry

lemma fold_reconnect_wire_preserves_nodes[simp]:
  "nodes
     (fold
        (reconnect_wire original_circuit operation_node_id)
        qs
        circuit)
     node_id
   =
   nodes circuit node_id"

sorry

lemma delete_operation_nodes:
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "nodes
       (delete_operation circuit operation_node_id)
     =
     (nodes circuit)(operation_node_id := None)"

sorry

lemma delete_operation_other_node[simp]:
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    different_node:
      "other_node_id \<noteq> operation_node_id"
  shows
    "nodes
       (delete_operation circuit operation_node_id)
       other_node_id
     =
     nodes circuit other_node_id"

  sorry

lemma reconnect_wire_edges_characterisation:
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q =
         Some successor_id"
  shows
    "edges
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
     =
     insert
       (make_edge predecessor_id successor_id q)
       (edges current_circuit
          - { make_edge predecessor_id operation_node_id q,
              make_edge operation_node_id successor_id q })"

  sorry

lemma reconnect_wire_successor_predecessor_characterisation:
  assumes
    predecessor:
      "predecessor_on_wire original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire original_circuit operation_node_id q =
         Some successor_id"
  shows
    "wire_edge_relation
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
     =
     insert
       (predecessor_id, successor_id)
       (wire_edge_relation current_circuit q
          - {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"

sorry

lemma reconnect_wire_preserves_input_boundary:
  assumes
    no_input_predecessor:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_id"
  shows
    "(\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation
                (reconnect_wire
                   circuit
                   operation_node_id
                   q
                   circuit)
                q)
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
       (get_input_node_id q)"

sorry

lemma reconnect_wire_preserves_input_boundary_from_same_relation:
  assumes
    no_input_predecessor:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation current_circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         current_circuit q (get_input_node_id q)"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
         wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
         Some successor_id"
  shows
    "(\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation
                (reconnect_wire
                   original_circuit
                   operation_node_id
                   q
                   current_circuit)
                q)
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       (get_input_node_id q)"

sorry

lemma reconnect_wire_preserves_other_wire_relation:
  assumes
    different_wire:
      "r \<noteq> q"
  shows
    "wire_edge_relation
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       r
     =
     wire_edge_relation current_circuit r"

  sorry

lemma fold_reconnect_preserves_other_wire_relation:
  fixes r
  assumes other_wire:
    "r \<notin> set qs"
  shows
    "wire_edge_relation
       (fold
          (reconnect_wire
             original_circuit
             operation_node_id)
          qs
          current_circuit)
       r
     =
     wire_edge_relation current_circuit r"
  sorry

lemma fold_reconnect_preserves_input_boundary:
  assumes
    no_input_predecessor:
      "\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation circuit q"
  and
    unique_input_successor:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
  and
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire
         circuit operation_node_id q =
         Some successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "(\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation
                (fold
                   (reconnect_wire circuit operation_node_id)
                   qs
                   circuit)
                q)
     \<and>
     has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       (get_input_node_id q)"

sorry

lemma delete_operation_removes_operation_node[simp]:

  assumes operation_node:
    "nodes circuit node_id = Some (OperationNode op)"

  shows
    "nodes (delete_operation circuit node_id) node_id = None"

sorry

lemma reconnect_wire_preserves_num_qubits:
  "num_qubits
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   num_qubits current_circuit"
  
  sorry

lemma reconnect_wire_edge_cases:
  assumes
    edge_after:
      "e \<in>
       edges
         (reconnect_wire
           original_circuit
           operation_node_id
           q
           current_circuit)"
  shows
    "e \<in> edges current_circuit
     \<or>
     (\<exists>predecessor successor. predecessor_on_wire original_circuit operation_node_id q
        = Some predecessor
      \<and>
        successor_on_wire original_circuit operation_node_id q
        = Some successor
      \<and>
        e = make_edge predecessor successor q)"
sorry

lemma fold_reconnect_wire_edge_cases:
  assumes
    edge_after:
      "e \<in>
       edges
         (fold
           (reconnect_wire original_circuit operation_node_id)
           qs
           current_circuit)"
  shows
    "e \<in> edges current_circuit
     \<or>
     (\<exists>q \<in> set qs.
        \<exists>predecessor successor.
          predecessor_on_wire
            original_circuit operation_node_id q
            = Some predecessor
        \<and>
          successor_on_wire
            original_circuit operation_node_id q
            = Some successor
        \<and>
          e = make_edge predecessor successor q)"
  
  sorry

lemma reconnect_wire_inserted_edge_well_formed:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_node_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_node_id"
  shows
    "is_well_formed_edge
       (reconnect_wire circuit operation_node_id q circuit)
       (make_edge predecessor_node_id successor_node_id q)"

sorry

lemma fold_reconnect_wire_preserves_num_qubits:
  "num_qubits
     (fold
       (reconnect_wire original_circuit node_id)
       qs
       current_circuit)
   =
   num_qubits current_circuit"

sorry

lemma operation_incident_edge_on_wire_cases:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    operation_uses_wire:
      "q \<in> set (op_qargs op)"
  and
    incident_edge:
      "e \<in> edges circuit"
  and
    edge_on_wire:
      "edge_wire e = q"
  and
    incident:
      "edge_source e = operation_node_id
       \<or> edge_target e = operation_node_id"
  shows
    "(\<exists>predecessor.
        predecessor_on_wire circuit operation_node_id q =
          Some predecessor
      \<and>
        e = make_edge predecessor operation_node_id q)
     \<or>
     (\<exists>successor.
        successor_on_wire circuit operation_node_id q =
          Some successor
      \<and>
        e = make_edge operation_node_id successor q)"
sorry

lemma fold_reconnect_wire_removes_incident_edges:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in>
       edges
         (fold
           (reconnect_wire circuit operation_node_id)
           (op_qargs op)
           circuit)"
  shows
    "edge_source e \<noteq> operation_node_id
     \<and> edge_target e \<noteq> operation_node_id"
sorry

lemma delete_operation_preserves_num_qubits:

  shows
    "num_qubits (delete_operation circuit node_id) = num_qubits circuit"

sorry

lemma reconnect_wire_preserves_next_id:
  "next_id
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   next_id current_circuit"

  sorry

lemma fold_reconnect_wire_preserves_next_id:
  "next_id
     (fold
        (reconnect_wire original_circuit node_id)
        qs
        current_circuit)
   =
   next_id current_circuit"

sorry

lemma delete_operation_preserves_next_id:
  "next_id (delete_operation circuit node_id) = next_id circuit"

sorry

lemma delete_operation_preserves_boundary_nodes:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_boundary_nodes
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_preserves_operation_nodes:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_operation_nodes
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_edge_preserves_reachability:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    edge_after:
      "(source_id, target_id)
       \<in>
       edge_relation
         (delete_operation circuit operation_node_id)"
  shows
    "(source_id, target_id)
     \<in>
     (edge_relation circuit)\<^sup>+"
sorry

lemma delete_operation_remaining_edges_not_incident:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    remaining_edge:
      "e \<in> edges
         (delete_operation circuit operation_node_id)"
  shows
    "edge_source e \<noteq> operation_node_id
     \<and> edge_target e \<noteq> operation_node_id"

sorry

lemma delete_operation_preserves_well_formed_edges:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "are_well_formed_edges
       (delete_operation circuit operation_node_id)"


sorry

lemma delete_operation_preserves_well_formed_circuit:
  assumes
    valid_state:
      "is_valid_construction_state circuit frontier"
  and
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "is_well_formed_circuit
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_reachability_preserved:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "(edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+
       \<subseteq>
     (edge_relation circuit)\<^sup>+"
sorry

lemma reconnect_wire_successor_has_unique_predecessor:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor
         current_circuit q successor_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
         wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       successor_id"

sorry

lemma reconnect_wire_predecessor_has_unique_successor:
  assumes
    unique_successor:
      "has_unique_wire_successor
         current_circuit q predecessor_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
         wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  shows
    "has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       predecessor_id"

sorry

lemma reconnect_wire_other_node_has_unique_predecessor:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor
         current_circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_successor:
      "node_id \<noteq> successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_id"

sorry

lemma reconnect_wire_other_node_has_unique_successor:
  assumes
    unique_successor:
      "has_unique_wire_successor
         current_circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    not_deleted:
      "node_id \<noteq> operation_node_id"
  and
    not_predecessor:
      "node_id \<noteq> predecessor_id"
  shows
    "has_unique_wire_successor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_id"

sorry

lemma reconnect_wire_preserves_remaining_node_degrees:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor current_circuit q node_id"
  and
    unique_successor:
      "has_unique_wire_successor current_circuit q node_id"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
       wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    remaining_node:
      "node_id \<noteq> operation_node_id"
  and
    predecessor_not_deleted:
      "predecessor_id \<noteq> operation_node_id"
  and
    successor_not_deleted:
      "successor_id \<noteq> operation_node_id"
  and
    predecessor_not_successor:
      "predecessor_id \<noteq> successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit operation_node_id q current_circuit)
       q node_id
     \<and>
     has_unique_wire_successor
       (reconnect_wire
          original_circuit operation_node_id q current_circuit)
       q node_id"
  sorry

lemma fold_reconnect_preserves_operation_degrees:
  assumes
    unique_predecessor:
      "has_unique_wire_predecessor circuit q node_id"
  and
    unique_successor:
      "has_unique_wire_successor circuit q node_id"
  and
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         circuit operation_node_id q =
       Some successor_id"
  and
    remaining_node:
      "node_id \<noteq> operation_node_id"
  and
    predecessor_not_deleted:
      "predecessor_id \<noteq> operation_node_id"
  and
    successor_not_deleted:
      "successor_id \<noteq> operation_node_id"
  and
    predecessor_not_successor:
      "predecessor_id \<noteq> successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_id
     \<and>
     has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_id"

sorry

lemma delete_operation_preserves_acyclicity:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "is_acyclic_circuit
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_preserves_unused_wire_relation:
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation circuit q"

sorry

lemma delete_operation_preserves_linear_unused_wire:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    unused_wire:
      "q \<notin> set (op_qargs op)"
  shows
    "wire_is_linear circuit q
     \<Longrightarrow>
     wire_is_linear
       (delete_operation circuit operation_node_id)
       q"

sorry

lemma reconnect_wire_preserves_surviving_reachability:
  assumes
    same_relation:
      "wire_edge_relation current_circuit q =
       wire_edge_relation original_circuit q"
  and
    unique_operation_predecessor:
      "has_unique_wire_predecessor
         current_circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor
         current_circuit q operation_node_id"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
       Some successor_id"
  and
    old_reachability:
      "wire_reaches current_circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  shows
    "wire_reaches
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       node_a
       node_b"

sorry

lemma fold_reconnect_preserves_surviving_reachability:
  assumes
    unique_operation_predecessor:
      "has_unique_wire_predecessor
         circuit q operation_node_id"
  and
    unique_operation_successor:
      "has_unique_wire_successor
         circuit q operation_node_id"
  and
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
       Some predecessor_id"
  and
    successor:
      "successor_on_wire
         circuit operation_node_id q =
       Some successor_id"
  and
    old_reachability:
      "wire_reaches circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "wire_reaches
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       node_a
       node_b"

sorry

lemma delete_operation_preserves_surviving_wire_reachability:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  and
    old_reachability:
      "wire_reaches circuit q node_a node_b"
  and
    source_survives:
      "node_a \<noteq> operation_node_id"
  and
    target_survives:
      "node_b \<noteq> operation_node_id"
  shows
    "wire_reaches
       (delete_operation circuit operation_node_id)
       q
       node_a
       node_b"

sorry

lemma delete_operation_used_wire_preserves_comparability:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "nodes_comparable_on_wire
       (delete_operation circuit operation_node_id)
       q"

sorry

lemma delete_operation_used_wire_preserves_input_boundary:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)
     \<and>
     has_unique_wire_successor
       (delete_operation circuit operation_node_id)
       q
       (get_input_node_id q)"

sorry

lemma reconnect_wire_preserves_output_boundary:
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
  and
    predecessor:
      "predecessor_on_wire circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire circuit operation_node_id q =
         Some successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (reconnect_wire
                  circuit
                  operation_node_id
                  q
                  circuit)
               q)"

sorry

lemma reconnect_wire_preserves_output_boundary_from_same_relation:
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         current_circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation current_circuit q"
  and
    same_relation:
      "wire_edge_relation current_circuit q =
         wire_edge_relation original_circuit q"
  and
    predecessor:
      "predecessor_on_wire
         original_circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire
         original_circuit operation_node_id q =
         Some successor_id"
  shows
    "has_unique_wire_predecessor
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (reconnect_wire
                  original_circuit
                  operation_node_id
                  q
                  current_circuit)
               q)"

sorry

lemma fold_reconnect_preserves_output_boundary:
  assumes
    unique_output_predecessor:
      "has_unique_wire_predecessor
         circuit q (get_output_node_id q)"
  and
    no_output_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
  and
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
         Some predecessor_id"
  and
    successor:
      "successor_on_wire
         circuit operation_node_id q =
         Some successor_id"
  and
    distinct_wires:
      "distinct qs"
  and
    used_wire:
      "q \<in> set qs"
  shows
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          qs
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (fold
                  (reconnect_wire circuit operation_node_id)
                  qs
                  circuit)
               q)"

sorry

lemma delete_operation_used_wire_preserves_output_boundary:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "has_unique_wire_predecessor
       (delete_operation circuit operation_node_id)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (delete_operation circuit operation_node_id)
               q)"

sorry

lemma delete_operation_used_wire_preserves_operation_degrees:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  and
    original_linear:
      "wire_is_linear circuit q"
  shows
    "\<forall>node_id remaining_op.
       nodes
         (delete_operation circuit operation_node_id)
         node_id
       =
       Some (OperationNode remaining_op)
       \<longrightarrow>
       node_uses_qubit (OperationNode remaining_op) q
       \<longrightarrow>
       has_unique_wire_predecessor
         (delete_operation circuit operation_node_id)
         q
         node_id
       \<and>
       has_unique_wire_successor
         (delete_operation circuit operation_node_id)
         q
         node_id"

sorry

lemma delete_operation_preserves_linear_used_wire:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    used_wire:
      "q \<in> set (op_qargs op)"
  shows
    "wire_is_linear circuit q
     \<Longrightarrow>
     wire_is_linear
       (delete_operation circuit operation_node_id)
       q"

sorry

lemma delete_operation_preserves_wire_is_linear:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  and
    valid_wire_after:
      "qubit_in_circuit
         (delete_operation circuit operation_node_id)
         q"
  shows
    "wire_is_linear
       (delete_operation circuit operation_node_id)
       q"
  sorry

lemma delete_operation_preserves_wire_linearity:
  assumes
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "all_wires_linear
       (delete_operation circuit operation_node_id)"

sorry

lemma delete_operation_preserves_valid_circuit:
  assumes
    valid_state:
      "is_valid_construction_state circuit frontier"
  and
    valid_circuit:
      "is_valid_circuit circuit"
  and
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "is_valid_circuit
       (delete_operation circuit operation_node_id)"

sorry


definition is_operation_node_id ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> bool"
where
  "is_operation_node_id circuit node_id \<longleftrightarrow>
     (\<exists>op. nodes circuit node_id = Some (OperationNode op))"

definition replace_operation ::
  "node_id \<Rightarrow> operation \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
where
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
  "valid_operation_replacement
      circuit operation_node_id replacement_op
   \<longleftrightarrow>
     (\<exists>original_op.
        nodes circuit operation_node_id =
          Some (OperationNode original_op)
      \<and> operation_in_circuit circuit replacement_op
      \<and> op_qargs replacement_op = op_qargs original_op)"


lemma replace_operation_selected_node:
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

  sorry

lemma valid_replacement_selected_node:
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

sorry

lemma replacement_preserves_other_nodes:
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

sorry

lemma replacement_preserves_edges:
  "edges
     (replace_operation operation_node_id replacement_op circuit)
   =
   edges circuit"

  sorry
  
lemma replacement_preserves_num_qubits:
  "num_qubits
     (replace_operation operation_node_id replacement_op circuit)
   =
   num_qubits circuit"

  sorry

lemma replacement_preserves_next_id:
  "next_id
     (replace_operation operation_node_id replacement_op circuit)
   =
   next_id circuit"

  sorry

lemma valid_replacement_preserves_node_wire_usage:
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

sorry

lemma replacement_preserves_well_formed_circuit:
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

  sorry

lemma replacement_preserves_acyclicity:

  assumes acyclic:
    "is_acyclic_circuit circuit"

  shows
   "is_acyclic_circuit
     (replace_operation
         operation_node_id replacement_op circuit)"

  sorry

lemma replacement_preserves_wire_edge_relation:
  "wire_edge_relation
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q
   =
   wire_edge_relation circuit q"

  sorry

lemma replacement_preserves_wire_reaches:
  "wire_reaches
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_a node_b
   \<longleftrightarrow>
   wire_reaches circuit q node_a node_b"

  sorry

lemma replacement_preserves_unique_wire_predecessor:
  "has_unique_wire_predecessor
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_id
   \<longleftrightarrow>
   has_unique_wire_predecessor circuit q node_id"

  sorry

lemma replacement_preserves_unique_wire_successor:
  "has_unique_wire_successor
     (replace_operation
        operation_node_id
        replacement_op
        circuit)
     q node_id
   \<longleftrightarrow>
   has_unique_wire_successor circuit q node_id"

  sorry

lemma valid_replacement_preserves_nodes_comparable_on_wire:
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

  sorry

lemma replacement_preserves_wire_linearity:
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

sorry

lemma replacement_preserves_valid_circuit:
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
  sorry


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

definition remove_operation_node ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> quantum_circuit"
  where
    "remove_operation_node circuit operation_node_id =
       circuit
         \<lparr>
           nodes :=
             (nodes circuit)
               (operation_node_id := None),
  
           edges :=
             {e \<in> edges circuit.
                edge_source e \<noteq> operation_node_id
              \<and> edge_target e \<noteq> operation_node_id}
         \<rparr>"

lemma remove_operation_node_selected[simp]:
  "nodes
     (remove_operation_node circuit operation_node_id)
     operation_node_id
   = None"

  sorry

lemma remove_operation_node_other[simp]:
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  shows
    "nodes
       (remove_operation_node circuit operation_node_id)
       other_node_id
     =
     nodes circuit other_node_id"

  sorry

lemma edges_remove_operation_node[simp]:
  "edges
     (remove_operation_node circuit operation_node_id)
   =
   {e \<in> edges circuit.
      edge_source e \<noteq> operation_node_id
    \<and> edge_target e \<noteq> operation_node_id}"

  sorry

lemma remove_operation_node_has_no_outgoing_edge:
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  shows
    "edge_source e \<noteq> operation_node_id"

  sorry

lemma remove_operation_node_has_no_incoming_edge:
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  shows
    "edge_target e \<noteq> operation_node_id"

  sorry

lemma remove_operation_node_preserves_unrelated_edge:
  assumes edge_exists:
    "e \<in> edges circuit"

  assumes source_different:
    "edge_source e \<noteq> operation_node_id"

  assumes target_different:
    "edge_target e \<noteq> operation_node_id"

  shows
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  sorry

lemma remove_operation_node_preserves_num_qubits[simp]:
  "num_qubits
     (remove_operation_node circuit operation_node_id)
   =
   num_qubits circuit"

  sorry

lemma remove_operation_node_preserves_next_id[simp]:
  "next_id
     (remove_operation_node circuit operation_node_id)
   =
   next_id circuit"

  sorry

definition insert_subcircuit_nodes ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
where
  "insert_subcircuit_nodes
      original_circuit
      current_circuit
      replacement =
     current_circuit
       \<lparr>
         nodes :=
           (\<lambda>host_node_id.
              let
                renaming_offset =
                  node_id_to_nat (next_id original_circuit);

                host_node_number =
                  node_id_to_nat host_node_id;

                local_node_id =
                  NodeId
                    (host_node_number - renaming_offset)
              in
                if renaming_offset \<le> host_node_number
                   \<and> local_node_id
                       \<in> subcircuit_operation_node_ids replacement
                then
                  nodes
                    (subgraph replacement)
                    local_node_id
                else
                  nodes current_circuit host_node_id)
       \<rparr>"

lemma insert_subcircuit_nodes_node_cases:
  assumes inserted_node:
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          circuit
          replacement)
       node_id
     =
     Some node"
  shows
    "nodes circuit node_id = Some node
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


sorry

lemma insert_subcircuit_nodes_copies_operation_node:
  assumes local_operation_node:
    "local_node_id
       \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          current_circuit
          replacement)
       (rename_subcircuit_node_id
          original_circuit
          local_node_id)
     =
     nodes (subgraph replacement) local_node_id"

  sorry

lemma insert_subcircuit_nodes_copies_operation:
  assumes local_operation:
    "nodes (subgraph replacement) local_node_id =
       Some (OperationNode op)"

  assumes allocated_local_node:
    "local_node_id
       \<in> subcircuit_operation_node_ids replacement"

  shows
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          current_circuit
          replacement)
       (rename_subcircuit_node_id
          original_circuit
          local_node_id)
     =
     Some (OperationNode op)"

  sorry

lemma insert_subcircuit_nodes_preserves_node_below_next_id:
  assumes existing_namespace:
    "node_id_to_nat node_id
       < node_id_to_nat (next_id original_circuit)"

  shows
    "nodes
       (insert_subcircuit_nodes
          original_circuit
          current_circuit
          replacement)
       node_id
     =
     nodes current_circuit node_id"

  sorry

lemma insert_subcircuit_nodes_preserves_edges[simp]:
  "edges
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   edges current_circuit"

  sorry

lemma insert_subcircuit_nodes_preserves_num_qubits[simp]:
  "num_qubits
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  sorry

lemma insert_subcircuit_nodes_preserves_next_id[simp]:
  "next_id
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  sorry

definition insert_subcircuit_internal_edges ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
where
  "insert_subcircuit_internal_edges
      original_circuit
      current_circuit
      replacement =
     current_circuit
       \<lparr>
         edges :=
           edges current_circuit
           \<union>
           renamed_subcircuit_internal_edges
             original_circuit
             replacement
       \<rparr>"

lemma edges_insert_subcircuit_internal_edges[simp]:
  "edges
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   edges current_circuit
   \<union>
   renamed_subcircuit_internal_edges
     original_circuit
     replacement"

  sorry

lemma insert_subcircuit_internal_edges_preserves_existing_edge:
  assumes existing_edge:
    "e \<in> edges current_circuit"

  shows
    "e \<in>
       edges
         (insert_subcircuit_internal_edges
            original_circuit
            current_circuit
            replacement)"

  sorry

lemma insert_subcircuit_internal_edges_contains_renamed_edge:
  assumes renamed_edge:
    "e \<in>
       renamed_subcircuit_internal_edges
         original_circuit
         replacement"

  shows
    "e \<in>
       edges
         (insert_subcircuit_internal_edges
            original_circuit
            current_circuit
            replacement)"

  sorry

lemma insert_subcircuit_internal_edges_contains_internal_edge:
  assumes internal_edge:
    "e \<in> subcircuit_internal_edges replacement"

  shows
    "rename_subcircuit_edge original_circuit e
       \<in>
       edges
         (insert_subcircuit_internal_edges
            original_circuit
            current_circuit
            replacement)"

  sorry

lemma insert_subcircuit_internal_edges_preserves_nodes[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   nodes current_circuit"

  sorry

lemma insert_subcircuit_internal_edges_preserves_node[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
     node_id
   =
   nodes current_circuit node_id"

  sorry

lemma insert_subcircuit_internal_edges_preserves_num_qubits[simp]:
  "num_qubits
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  sorry

lemma insert_subcircuit_internal_edges_preserves_next_id[simp]:
  "next_id
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  sorry

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

definition replace_operation_by_subcircuit ::
  "quantum_circuit
    \<Rightarrow> frontier
    \<Rightarrow> node_id
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit \<times> frontier"
where
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

  sorry

lemma replace_operation_by_subcircuit_frontier[simp]:
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

  sorry



lemma replace_operation_by_subcircuit_removes_old_operation:
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

sorry


lemma replace_operation_by_subcircuit_contains_renamed_nodes:

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

sorry

lemma replace_operation_by_subcircuit_preserves_unrelated_nodes:
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
sorry

lemma replace_operation_by_subcircuit_contains_renamed_internal_edges:
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
sorry

lemma replace_operation_by_subcircuit_connects_inputs:
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
sorry

lemma replace_operation_by_subcircuit_connects_outputs:
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
sorry

lemma replace_operation_by_subcircuit_preserves_unrelated_edges:
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
sorry

lemma replace_operation_by_subcircuit_node_cases:
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

sorry


lemma replace_operation_by_subcircuit_edge_cases:
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
sorry

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
sorry

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
sorry

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
sorry

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
sorry

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
sorry


lemma replace_operation_by_subcircuit_preserves_well_formed_circuit:
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
sorry


lemma valid_subcircuit_replacement_is_acyclic:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "is_acyclic_circuit (subgraph replacement)"
  sorry


lemma injective_renaming_trancl_reflects_cycle:
  assumes rename_injective:
    "inj rename"

  assumes renamed_cycle:
    "(renamed_node, renamed_node)
       \<in>
       {(rename source, rename target) |
          source target.
          (source, target) \<in> relation}\<^sup>+"

  shows
    "\<exists>local_node.
       (local_node, local_node) \<in> relation\<^sup>+"
sorry

lemma renamed_internal_cycle_implies_subcircuit_cycle:
  assumes internal_cycle:
    "(renamed_node, renamed_node)
       \<in>
       {(edge_source e, edge_target e) |
          e.
          e \<in>
            renamed_subcircuit_internal_edges
              circuit
              replacement}\<^sup>+"

  shows
    "\<exists>local_node.
       (local_node, local_node)
         \<in>
         (edge_relation (subgraph replacement))\<^sup>+"

sorry

lemma replacement_cycle_internal_or_original:
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  assumes result_cycle:
    "(node, node)
       \<in>
       (edge_relation
          (fst
            (replace_operation_by_subcircuit
               circuit
               frontier
               operation_node_id
               replacement)))\<^sup>+"

  shows
    "(\<exists>original_node.
        (original_node, original_node)
          \<in> (edge_relation circuit)\<^sup>+)
     \<or>
     (\<exists>renamed_node.
        (renamed_node, renamed_node)
          \<in>
          {(edge_source e, edge_target e) |
             e.
             e \<in>
               renamed_subcircuit_internal_edges
                 circuit
                 replacement}\<^sup>+)"

  sorry

lemma replacement_cycle_cases:
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes result_cycle:
    "(node, node)
       \<in>
       (edge_relation
          (fst
            (replace_operation_by_subcircuit
               circuit
               frontier
               operation_node_id
               replacement)))\<^sup>+"

  shows
    "(\<exists>original_node.
        (original_node, original_node)
          \<in> (edge_relation circuit)\<^sup>+)
     \<or>
     (\<exists>replacement_node.
        (replacement_node, replacement_node)
          \<in>
          (edge_relation (subgraph replacement))\<^sup>+)"

sorry


lemma replace_operation_by_subcircuit_preserves_acyclicity:

  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes original_acyclic:
    "is_acyclic_circuit circuit"

  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

  shows
    "is_acyclic_circuit
       (fst
         (replace_operation_by_subcircuit
            circuit
            frontier
            operation_node_id
            replacement))"

sorry



definition ex_h_q0 :: operation where
  "ex_h_q0 = \<lparr>op_gate = Gate_H, op_qargs = [Qubit 0]\<rparr>"

definition ex_cnot_q0_q1 :: operation where
  "ex_cnot_q0_q1 =
     \<lparr>op_gate = Gate_CNOT, op_qargs = [Qubit 0, Qubit 1]\<rparr>"

value "ex_cnot_q0_q1"

end