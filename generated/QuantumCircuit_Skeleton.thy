theory QuantumCircuit_Skeleton
  imports Complex_Main

begin

datatype qubit = Qubit nat (* The wire identity (q0, q1, q2, \<dots>) *)
datatype node_id = NodeId nat (* The graph vertex identity (input node, output node, \<dots>) *)

datatype gate = (* Symbolic list of gates *)
  Gate_H
  | Gate_X
  | Gate_Y
  | Gate_Z
  | Gate_CNOT
  | Gate_CCNOT
  | Gate_RZ real

record operation = (* Each operation has a gate name and list of qubits it is acting on*)
  op_gate :: gate
  op_qargs :: "qubit list"

fun gate_arity :: "gate \<Rightarrow> nat" where
  (* Returns the number of qubits a given gate acts on *)
  "gate_arity Gate_H = 1"
| "gate_arity Gate_X = 1"
| "gate_arity Gate_Y = 1"
| "gate_arity Gate_Z = 1"
| "gate_arity (Gate_RZ \<Theta>) = 1"
| "gate_arity Gate_CNOT = 2"
| "gate_arity Gate_CCNOT = 3"

definition is_valid_operation :: "operation \<Rightarrow> bool" where
  (* Defines a valid operation. An operation is valid iff
      1. Number of elements in q_args is equal to arity of the gate
      2. All elements in q_args are distinct
  *)

"is_valid_operation op \<longleftrightarrow>
     length (op_qargs op) = gate_arity (op_gate op) \<and>
     distinct (op_qargs op)"

(* datatype \<Rightarrow> alternatives/cases
   record \<Rightarrow> Structured object with named fields (like struct in C++)
*)

datatype circuit_node = (* Node of a DAG can be InputNode, OutputNode or OperationNode (gate) *)
  InputNode qubit
  | OutputNode qubit
  | OperationNode operation

record edge = (* A DAG edge would need source, target and the wire name (qubit) it represents*)
  edge_source :: node_id
  edge_target :: node_id
  edge_wire :: qubit

definition make_edge :: "node_id \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> edge" where
  (* Create an edge between source u, target v on wire (qubit) q *)
  "make_edge u v q = \<lparr> edge_source = u, edge_target = v, edge_wire = q \<rparr>"

record quantum_circuit = (* Quantum circuit DAG has these 4 parameters *)
  num_qubits :: nat (* Number of qubits in the circuit  *)
  nodes :: "node_id \<Rightarrow> circuit_node option" (* Node table mapping node ID to actual node; it means "either Some circuit_node or None" *)
  edges :: "edge set" (* Set of wire-labelled connections (source node to target node along this wire) *)
  next_id :: node_id (* Next unused node ID for inserting a new operation node *)

(* Extract the qubit index from Qubit type (for example, 0 from q0) *)
fun get_qubit_index :: "qubit \<Rightarrow> nat" where
  "get_qubit_index (Qubit n) = n"

(* Extract the node index from node_id *)
fun node_id_to_nat :: "node_id \<Rightarrow> nat" where
  "node_id_to_nat (NodeId n) = n"


(* --- Defines a fixed way to assign IDs to the special boundary nodes (inputs and outputs) --- *)
(* We follow canonical numbering for now:
   ID of input_node of qubit q = 2 * q
   ID of output_node of qubit q = 2 * q + 1
   ID of first operation node (when there are n qubits) = 2 * n
*)

(* If we have to move away from canonical numbering, just change these definitions *)

definition get_input_node_id :: "qubit \<Rightarrow> node_id" where
  "get_input_node_id q = NodeId (2 * get_qubit_index q)"

definition get_output_node_id :: "qubit \<Rightarrow> node_id" where
  "get_output_node_id q = NodeId (2 * get_qubit_index q + 1)"

definition get_first_operation_id :: "nat \<Rightarrow> node_id" where
  "get_first_operation_id n = NodeId (2 * n)"
  (* can later on replace nat with quantum_circuit since it already has num_qubits as a parameter*)

lemma input_output_ids_distinct[simp]: (* No input node ID is ever equal to an output node ID (even and odd numbers) *)
  "get_input_node_id q \<noteq> get_output_node_id r"
  sorry

lemma input_node_id_injective: (* 2 different input nodes cannot have same node ID *)
  "get_input_node_id q = get_input_node_id r \<Longrightarrow> q = r"
  sorry

lemma output_node_id_injective: (* 2 different output nodes cannot have same node ID *)
  "get_output_node_id q = get_output_node_id r \<Longrightarrow> q = r"
  sorry

(* Create an empty circuit with n qubits (The initial DAG) *)

definition initial_nodes :: "nat \<Rightarrow> node_id \<Rightarrow> circuit_node option" where
  (* Given the number of qubits in the circuit and a node ID, create the corresponding node *)
  (* Id of InputNode is even, while that of OutputNode is odd *)
  (* If node_number \<ge> 2 * num_qubits, then it is unused in the initial circuit. Operation nodes will be added later. *)
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
  (* Given the number of qubits in the circuit, make an edge from each InputNode Input_i (ranging from 0 to num_qubits-1) to each OutputNode Output_i *)
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
  (* Given the number of qubits in the circuit (say nq), create an empty quantum circuit that has num_qubits = nq, and nq InputNodes and nq OutputNodes, and each InputNode connected to corresponding OutputNode by an edge *)
  "initial_circuit number_of_qubits =
     \<lparr> num_qubits = number_of_qubits,
       nodes = initial_nodes number_of_qubits,
       edges = initial_edges number_of_qubits,
       next_id = get_first_operation_id number_of_qubits 
     \<rparr>
  "

(* --- Some lemmas to prove basic properties of empty circuits --- *)

lemma initial_circuit_num_qubits[simp]:
  (* Number of qubits in initial circuit = whatever natural number was passed to initial_circuit *)
  "num_qubits (initial_circuit number_of_qubits) = number_of_qubits"
  sorry

lemma initial_circuit_next_id[simp]:
  (* After initialization, the next available ID is the first operation-node ID. *)
  "next_id (initial_circuit number_of_qubits) =
   get_first_operation_id number_of_qubits"
  sorry

lemma initial_circuit_input_node:
  (* For any valid qubit number, the canonical input node ID stores the corresponding InputNode. *)
  assumes "qubit_number < number_of_qubits"
  shows "nodes (initial_circuit number_of_qubits)
          (get_input_node_id (Qubit qubit_number))
        = Some (InputNode (Qubit qubit_number))" (* nodes is a record selector, meaning since it is defined inside the record, we have to pass the record itself as the first parameter *)
  sorry

lemma initial_circuit_output_node:
  (* For any valid qubit number, the canonical output node ID stores the corresponding OutputNode. *)
  assumes "qubit_number < number_of_qubits"
  shows "nodes (initial_circuit number_of_qubits)
          (get_output_node_id (Qubit qubit_number))
        = Some (OutputNode (Qubit qubit_number))" (* nodes is a record selector, meaning since it is defined inside the record, we have to pass the record itself as the first parameter *)
  sorry

lemma initial_circuit_has_wire_edge:
  (* For any valid qubit number, the initial circuit contains the direct wire edge from input to output. *)
  assumes "qubit_number < number_of_qubits"
  shows "make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)
        \<in> edges (initial_circuit number_of_qubits)" (* edges is a record selector, meaning since it is defined inside the record, we have to pass the record itself as the first parameter *)
  sorry

lemma make_edges_on_different_wires_unequal:
  (* Two edges carrying different qubit-wire labels cannot be equal,
     regardless of their source and target node IDs. *)
  assumes wires_different:
    "first_wire \<noteq> second_wire"
  shows
    "make_edge first_source first_target first_wire
     \<noteq>
     make_edge second_source second_target second_wire"
  sorry


(* ------- Basic properties' lemma completed ----------- *)

(* ----------- Simple query helpers ----------- *)

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

(* --------- Simple query helpers ends --------- *)

(* ------ Edge well-formedness definitions begin --------- *)

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

  sorry

(* -------- Edge well-formedness definitions end --------- *)

(* ---- Check validity of OperationNodes in the circuit ---------- *)

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
  sorry

lemma initial_circuit_all_wire_nodes_comparable:
  (* Every valid wire in the initial circuit contains only its input and output nodes, connected by the canonical input-to-output edge. Therefore, all nodes using every valid wire are comparable. *)
  "all_wire_nodes_comparable
     (initial_circuit number_of_qubits)"

  sorry

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

(* ---- Validity check (Well-formedness check) for entire circuit begins ---- *)

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

definition is_valid_quantum_circuit :: "quantum_circuit \<Rightarrow> bool" where
  (* A structurally valid quantum circuit satisfies every invariant
     established for the DAG representation. *)
  "is_valid_quantum_circuit circuit \<longleftrightarrow>
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
  sorry

lemma initial_edge_relation_cases:
  (* Every source-target pair in the initial circuit relation comes
     from one canonical input-to-output edge of a valid qubit. *)
  assumes relation_pair:
    "(source_id, target_id) \<in> edge_relation (initial_circuit number_of_qubits)"

obtains qubit_number where
  "qubit_number < number_of_qubits"
  "source_id = get_input_node_id (Qubit qubit_number)"
  "target_id = get_output_node_id (Qubit qubit_number)"

sorry

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

sorry

lemma initial_circuit_has_no_operation_nodes:(* helper lemma *)
  (* Proves that an initial circuit does not have any operation node  *)
  "nodes (initial_circuit number_of_qubits) node_id \<noteq> Some (OperationNode op)"
  sorry

lemma initial_circuit_is_well_formed:
  (* Proving that the initial empty circuit is a well-formed (valid) circuit *)
  "is_well_formed_circuit (initial_circuit number_of_qubits)"

sorry

lemma initial_circuit_is_acyclic:
  (* The initial circuit is acyclic because every edge goes directly
     from an input boundary node to an output boundary node, and output
     nodes have no outgoing edges. *)
  "is_acyclic_circuit (initial_circuit number_of_qubits)"

sorry

lemma initial_circuit_has_linear_wires:
  (* Every valid wire in the initial circuit consists of exactly one
     directed edge from its canonical input node to its canonical
     output node. Therefore, every initial wire is linear. *)
  "all_wires_linear (initial_circuit number_of_qubits)"
  sorry


(* ----- Validity check (Well-formedness check) for entire circuit ends ----- *)

(* -------- Fresh node ID helpers begin -------- *)


definition increment_node_id :: "node_id \<Rightarrow> node_id" where
  (* Given a node ID, return the next node ID (Add 1 to it) *)
  "increment_node_id current_node_id = NodeId (node_id_to_nat current_node_id + 1)"

lemma node_id_to_nat_increment_node_id[simp]:
  (* The next node id is 1 more than the present node id *)
  "node_id_to_nat (increment_node_id current_node_id) = node_id_to_nat current_node_id + 1"
  sorry

lemma increment_node_id_not_same[simp]:
  (* Node id before and after increment are not same *)
  "increment_node_id current_node_id \<noteq> current_node_id"
  sorry

(* -------- Fresh node ID helpers end -------- *)

(* ---------------- Frontier definition begins ------------------ *)

type_synonym frontier = "qubit \<Rightarrow> node_id" (* Frontier is a mapping from qubit \<Rightarrow> node_id, where node_id means the last operation encountered on this qubit *)

definition initial_frontier :: frontier where
  (* Initially, frontier (map) would be from qubit to its input node (since circuit is empty) *)
  "initial_frontier q = get_input_node_id q"

definition update_frontier :: "frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> frontier" where
  (* Updating frontier for a qubit q means that we are updating the existing entry of the qubit q in the map with the id of the new node *)
  "update_frontier frontier q new_node_id = frontier(q := new_node_id)"

lemma update_frontier_same[simp]:
  (* If you look up qubit q after updating the frontier entry for q, you will get the newly supplied node ID *)
  "update_frontier frontier q new_node_id q = new_node_id"
  sorry

lemma update_frontier_other[simp]:
  (* Updating the frontier for q does not change the frontier entry
     of any different qubit other_q. *)
  assumes "other_q \<noteq> q"
  shows
    "update_frontier frontier q new_node_id other_q =
     frontier other_q"
  sorry

(* ---------------- Frontier definition ends ------------------ *)

(* -------- Construction-state validity definitions begin -------- *)

definition is_valid_frontier :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  (* A frontier is valid when, for every valid qubit:
       1. the frontier points to an existing node on that wire, and
       2. that node is connected directly to the output node on that wire.
       3. the frontier node must have a unique successor, which is the output node
  *)
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
  (* The circuit's next_id is unused when no node is currently stored at that ID. This prevents the next insertion from overwriting an existing node *)
  "next_id_is_unused circuit \<longleftrightarrow> nodes circuit (next_id circuit) = None"

definition all_existing_node_ids_below_next_id ::
  "quantum_circuit \<Rightarrow> bool"
  where
    (* Every node currently stored in the circuit has a numerical node ID
     strictly smaller than the circuit's next_id.

     This expresses sequential node-ID allocation:
       - IDs below next_id may already be allocated;
       - next_id and every greater ID are not yet allocated.

     This property is stronger than saying that next_id is unused.
  *)
    "all_existing_node_ids_below_next_id circuit \<longleftrightarrow>
     (\<forall>existing_node_id.
        nodes circuit existing_node_id \<noteq> None
        \<longrightarrow>
        node_id_to_nat existing_node_id
          < node_id_to_nat (next_id circuit))"

definition is_valid_construction_state :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  (* A circuit and frontier form a valid construction state when:
       1. the circuit is structurally well formed;
       2. the frontier correctly describes the current end of every wire;
       3. next_id is unused and can safely identify the next operation node.
       4. every allocated node ID lies strictly below next_id.
  *)
  "is_valid_construction_state circuit frontier \<longleftrightarrow>
      is_well_formed_circuit circuit
        \<and> is_valid_frontier circuit frontier
        \<and> next_id_is_unused circuit
        \<and> all_existing_node_ids_below_next_id circuit"

(* -------- Construction-state validity definitions end -------- *)

(* -------- Graph update helpers begin -------- *)

definition insert_node :: "node_id \<Rightarrow> circuit_node \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  (* Add or replace the node stored at the given node ID. *)
  "insert_node node_id new_node circuit =
     circuit\<lparr>nodes := (nodes circuit)(node_id := Some new_node)\<rparr>" (* create a new function exactly like "nodes circuit", except at "NodeId 2", return "Some new_node" *)

definition insert_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  (* Add an edge to the circuit. *)
  "insert_edge e circuit =
     circuit\<lparr>edges := insert e (edges circuit)\<rparr>" (* Circuit where everything else is same, except that edges is now the union of old edge set with the new edge inserted *)

definition delete_edge :: "edge \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit" where
  (* Remove an edge from the circuit. *)
  "delete_edge e circuit =
     circuit\<lparr>edges := edges circuit - {e}\<rparr>" (* Circuit where everything else is same, except that edges is the difference of old edges and set (new edge) *)

lemma nodes_insert_node_same[simp]: (* helper lemma *)
  (* After insertion, if you lookup at the inserted node id, you would get the new inserted node *)
  "nodes (insert_node node_id node circuit) node_id = Some node"
  sorry

lemma valid_frontier_has_unique_successor:
  (* A valid frontier is the final node immediately before the output
     node, so it has exactly one successor on its wire. *)
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

assumes valid_q:
  "qubit_in_circuit circuit q"

shows
  "has_unique_wire_successor circuit q (frontier q)"
  sorry

lemma nodes_insert_node_other[simp]: (* helper lemma *)
  (* All other node ids apart from the one where insertion happen, remain unchanged *)
  assumes "other_node_id \<noteq> node_id"
  shows "nodes (insert_node node_id node circuit) other_node_id =
         nodes circuit other_node_id"
  sorry

lemma insert_node_at_unused_id_preserves_valid_frontier:
  (* Storing a new node at an unused node ID preserves frontier validity.

     Since the ID was unused, it cannot be the ID of any existing frontier node. Therefore, every existing frontier lookup remains unchanged. insert_node also leaves the edge set and qubit count unchanged.
  *)
  assumes valid_frontier: "is_valid_frontier circuit frontier"
    (* Assume the circuit already has a correct frontier. This is the property we want to preserve. *)

assumes node_id_unused: "nodes circuit new_node_id = None"
  (* Assume this node ID is currently unused. We are inserting into an empty location, not replacing an existing node. *)

shows
  "is_valid_frontier 
         (insert_node new_node_id new_node circuit)
         frontier"
  (* Shows that after inserting the new node, the exact same frontier is still valid. *)

sorry

lemma update_next_id_preserves_valid_frontier:
  (* Updating only the next_id field preserves frontier validity.

     The frontier invariant depends on the circuit's qubit count, node mapping, and edge set. Updating next_id changes none of these fields.
  *)

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

shows 
  "is_valid_frontier (circuit \<lparr> next_id := new_next_id \<rparr>) frontier"

  sorry

lemma edges_insert_edge[simp]: (* helper lemma *)
  (* Edge set after insertion is just union of edge set prior to insertion and the newly added edge *)
  "edges (insert_edge e circuit) = insert e (edges circuit)"
  sorry

lemma edges_delete_edge[simp]: (* helper lemma *)
  (* Edge set after deletion is just difference of edge set prior to deletion and the deleted edge *)
  "edges (delete_edge e circuit) = edges circuit - {e}"
  sorry

(* -------- Graph update helpers end -------- *)

(* -------- Initial construction-state lemmas begin -------- *)

lemma initial_frontier_is_valid:
  (* The initial frontier correctly points from each qubit to its input boundary node. *)
  "is_valid_frontier (initial_circuit number_of_qubits) initial_frontier"

sorry

lemma initial_next_id_is_unused:
  (* The first operation-node ID is unused in the initial circuit. *)
  "next_id_is_unused (initial_circuit number_of_qubits)"
  sorry

lemma initial_existing_node_ids_are_below_next_id:
  (* Every node stored in the initial circuit is a boundary node whose
     numerical ID is strictly smaller than the first operation-node ID.

     The initial node table stores nodes only at IDs below
     2 * number_of_qubits, while next_id is exactly
     NodeId (2 * number_of_qubits).*)
  "all_existing_node_ids_below_next_id (initial_circuit number_of_qubits)"

  sorry

(* -------- Initial construction-state lemmas end -------- *)

definition splice_wire_without_updating_frontier ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> quantum_circuit" where
  (* Insert new_node_id on wire q between the current frontier node and the output node. Does not update frontier, for sake of simplicity *)
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
    (* Insert new_node_id on wire q and update the frontier for q in the same step. *)
    "splice_wire circuit frontier q new_node_id = (
         splice_wire_without_updating_frontier circuit frontier q new_node_id,
         update_frontier frontier q new_node_id
  )"

lemma fst_splice_wire:
  (* Says that the first part of splice_wire response is the updated circuit *)
  "fst (splice_wire circuit frontier q new_node_id) =
   splice_wire_without_updating_frontier circuit frontier q new_node_id"
  sorry

lemma snd_splice_wire:
  (* Says that the second part of splice_wire response is the updated frontier map *)
  "snd (splice_wire circuit frontier q new_node_id) =
   update_frontier frontier q new_node_id"
  sorry

lemma edges_splice_wire_without_updating_frontier:
  (* The edge set after splicing is obtained by removing the old edge
     from the current frontier to the output node and inserting the two
     new edges through the newly inserted operation node. *)
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
  (* After splicing new_node_id into wire q, the resulting circuit
     contains the new edge from new_node_id to the output node of q. *)
  "make_edge
      new_node_id
      (get_output_node_id q)
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  sorry

lemma splice_wire_contains_new_input_edge:
  (* After splicing new_node_id into wire q, the resulting circuit
     contains the new edge from previous frontier node to new_node_id *)
  "make_edge
      (frontier q)
      new_node_id
      q
   \<in> edges
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)"
  sorry

lemma splice_wire_preserves_output_edge_on_other_wire:
  (* Splicing wire q does not remove the final frontier-to-output edge belonging to a different wire "other_q".

     The only edge removed by the splice has wire label q. Since other_q and q are different, the other wire's edge cannot be the removed edge and therefore remains in the updated circuit.  *)
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
  (* Splicing a single wire only modifies the edge set and the frontier. The node table remains unchanged. *)
  "nodes (fst (splice_wire circuit frontier q new_node_id)) node_id = nodes circuit node_id"
  sorry

lemma splice_wire_without_updating_frontier_preserves_num_qubits[simp]:
  (* Rewiring one qubit wire without updating the frontier changes only the circuit's edges field. The number of qubits remains unchanged. *)
  "num_qubits 
     (splice_wire_without_updating_frontier circuit frontier q new_node_id)
   =
   num_qubits circuit"
  sorry

lemma splice_wire_preserves_num_qubits[simp]:
  (* Splicing a single wire only modifies the edge set and the frontier. The number of qubits remain unchanged *)
  "num_qubits (fst (splice_wire circuit frontier q new_node_id)) = num_qubits circuit"
  sorry

lemma splice_wire_preserves_other_wire_relation:
  (* Splicing current_wire changes only edges labelled current_wire.
     Therefore, the edge relation of a distinct wire q is unchanged. *)
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
  (* Splicing an existing node into a valid qubit wire preserves the
     frontier invariant, provided the inserted node belongs to that wire. *)

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

assumes new_node_exists:
  "nodes circuit new_node_id = Some new_node"

assumes new_node_uses_wire:
  "node_uses_qubit new_node q"

assumes new_node_not_frontier:
  (* The node being spliced is different from the current frontier
       node. Otherwise, the newly inserted frontier-to-node edge would
       become a self-loop and violate unique-successor validity. *)
  "new_node_id \<noteq> frontier q"

assumes new_node_has_no_other_successor:
  (* Before splicing, every existing q-labelled edge leaving the node
       being inserted, if any, already leads to the output node.
  
       This rules out another outgoing q-edge that would make the updated
       frontier branch after the new output edge is inserted.
    *)
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
  (* Updating only next_id does not change the wire-edge relation, since wire_edge_relation depends only on the edge set. *)
  "wire_edge_relation (circuit\<lparr>next_id := new_next_id\<rparr>) q
   =
   wire_edge_relation circuit q"

  sorry

lemma wire_edge_relation_after_splice_same_wire:
  (* Splicing new_node_id into wire q removes the old frontier-to-output relation pair and inserts frontier-to-new and new-to-output. *)
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
  (* Splicing wire q removes and inserts only q-labelled edges.
     Therefore, the relation of any different wire other_q is unchanged. *)
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
  (* If target_id was reachable from source_id along wire q before
     splicing, then it remains reachable afterward.

     The proof lifts old_wire_edge_reaches_after_splice from individual
     relation edges to arbitrary non-empty paths by induction over the
     transitive-closure derivation. *)
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
  (* Splicing a new node into wire q does not destroy the ordering between nodes that already existed in the circuit.

     If two old nodes were equal, or one reached the other before the splice, the same comparison remains valid afterward because every old wire path is preserved by old_wire_reaches_after_splice. *)
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
  (* Allows inserting multi-qubit gates into the circuit, by recursively adding new edges for each concerned qubit *)
  "splice_wires circuit frontier [] new_node_id = (circuit, frontier)"
| "splice_wires circuit frontier (q # qs) new_node_id =
      (
        let (updated_circuit, updated_frontier) = 
            splice_wire circuit frontier q new_node_id in
                splice_wires updated_circuit updated_frontier qs new_node_id
      )
  "

(* ---------------- Operation insertion begins ---------------- *)

definition insert_operation ::
  "quantum_circuit \<Rightarrow> frontier \<Rightarrow> operation \<Rightarrow> quantum_circuit \<times> frontier"
  where
    (* Insert an operation into the circuit:
      1. Use next_id as the ID of the new OperationNode
      2. Insert the OperationNode into the node table
      3. Splice the new node into every qubit wire used by the operation
      4. Advance next_id
      5. Return the updated circuit and frontier
  *)
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
  (* Recursively splicing a node into the wires listed in qs does not
     change the edge relation of a wire q that does not occur in qs.

     Each individual splice deletes and inserts only edges whose wire
     label is the wire currently being processed. Therefore, no edge
     labelled q is changed when q is absent from qs.
  *)
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
  (* When q occurs exactly once in the list qs, splice_wires replaces
     the current frontier-to-output edge on q by two edges passing
     through new_node_id.

     Splices performed on the other wires in qs do not affect the
     q-labelled edge relation.
  *)
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
  (* Characterize every edge that may occur after recursively splicing
     new_node_id into all wires listed in qs.

     Provided the wires in qs are distinct, every resulting edge is:
       1. an edge that already belonged to the original circuit;
       2. a newly inserted edge from the original frontier node of some
          affected wire to new_node_id; or
       3. a newly inserted edge from new_node_id to the output node of
          some affected wire.

     Some original edges may have been deleted by splicing. Therefore,
     the first case states only that a resulting edge may be old, not
     that every old edge remains present.
  *)
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
  (* Repeatedly splicing the same existing node into every wire in qs preserves frontier validity, provided that the node belongs to every wire being spliced. 

    The node is assumed to exist before splicing begins. Since splice_wire changes only edges and the frontier, it continues to exist throughout the recursive process.
  *)
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

assumes new_node_exists:
  "nodes circuit new_node_id = Some new_node"

assumes new_node_uses_all_wires:
  "\<forall>q \<in> set qs. node_uses_qubit new_node q"

assumes distinct_wires:
  (* Each wire is spliced at most once. *)
  "distinct qs"

assumes new_node_not_frontiers:
  (* The inserted node is different from the existing frontier node on
         every wire that will be spliced. *)
  "\<forall>q \<in> set qs. new_node_id \<noteq> frontier q"

assumes new_node_has_no_other_successors:
  (* Before splicing starts, the inserted node has no conflicting
         successor on any affected wire. *)
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
  (* Inserting an operation preserves the validity of the construction
     frontier.

     The proof follows the implementation of insert_operation:
       1. insert the new operation node,
       2. splice that node into every qubit wire used by the operation,
       3. advance next_id.

     Each individual step has already been shown to preserve the
     frontier invariant.
  *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

assumes operation_valid_for_circuit:
  "operation_in_circuit circuit op"

shows "is_valid_frontier
    (fst (insert_operation circuit frontier op))
    (snd (insert_operation circuit frontier op))"

sorry


lemma insert_operation_new_node:
  (* After insertion, looking up the node whose ID was the old "next_id" returns the newly inserted node *)
  "nodes (fst (insert_operation circuit frontier op))
         (next_id circuit)
   = Some (OperationNode op)"

sorry

lemma insert_operation_preserves_other_nodes:
  (* Inserting an operation changes the nodes field only at the node ID
     that was next_id in the original circuit.

     Therefore, looking up any different node ID in the returned circuit
     gives exactly the same result as looking it up in the original
     circuit.
  *)
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
  (* After insertion, next_id of the new circuit is 1 more than the next_id of the circuit before insertion *)
  "next_id (fst (insert_operation circuit frontier op)) =
   increment_node_id (next_id circuit)"

sorry

lemma insert_operation_preserves_node_id_allocation:
  (* Inserting one operation preserves sequential node-ID allocation.

     Before insertion, every existing node ID is smaller than next_id.

     During insertion:
       1. the new operation node is stored exactly at the old next_id;
       2. no other node-table entry is changed;
       3. the final circuit advances next_id by one.

     Therefore, every node in the resulting circuit has an ID strictly
     smaller than its new next_id.
  *)
  assumes valid_allocation:
    "all_existing_node_ids_below_next_id circuit"

shows
  "all_existing_node_ids_below_next_id
       (fst (insert_operation circuit frontier op))"

sorry

lemma insert_operation_num_qubits[simp]:
  (* Inserting an operation does not change the number of qubits in the circuit. *)
  "num_qubits (fst (insert_operation circuit frontier op)) =
   num_qubits circuit"

sorry

lemma insert_operation_preserves_well_formed_circuit:
  (* Inserting an operation into a valid construction state preserves
     the current circuit well-formedness invariant.

     The assumptions ensure that:
       1. the original circuit is well formed;
       2. the supplied frontier correctly identifies the final edge
          on every valid wire;
       3. the allocated node ID is unused;
       4. all existing node IDs lie below next_id, preventing collision
          with canonical boundary nodes;
       5. the inserted operation is valid for this circuit.

     The proof is divided according to the three components of is_well_formed_circuit:
       1. boundary nodes remain well formed;
       2. all edges remain well formed;
       3. all operation nodes remain well formed.
  *)
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
  (* Inserting an operation that is valid for the current circuit
     preserves the complete construction-state invariant.

     The original construction-state assumption supplies:
       1. circuit well-formedness;
       2. frontier validity;
       3. an unused next_id;
       4. sequential node-ID allocation.

     The insertion-preservation theorems already proved establish that
     the returned circuit and frontier satisfy these properties again.
     Therefore, another valid operation may safely be inserted into the
     returned construction state.
  *)

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
  (* On a linear wire with a valid frontier, every existing node using q
     is either:
       1. the output node;
       2. the frontier node itself; or
       3. ordered before the frontier and therefore reaches it.

     The alternative that the frontier reaches the chosen node is
     impossible unless that node is the output, because the frontier has
     a direct edge to the output and the output has no outgoing q-edge.
  *)
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
  (* The frontier-to-output edge is the frontier node's only immediate
       outgoing edge on q. *)
  "has_unique_wire_successor circuit q (frontier q)"

shows
  "node_id = get_output_node_id q
       \<or> node_id = frontier q
       \<or> wire_reaches circuit q node_id (frontier q)"

sorry


lemma subdividing_final_edge_preserves_old_reachability:
  (* Replacing frontier-to-output by frontier-to-new-to-output preserves
     every directed path that existed before subdivision.

     Any old path that did not use the removed edge remains unchanged.
     Any old path that used the removed edge can replace that edge by
     the two new edges.
  *)
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
  (* Subdividing the final frontier-to-output edge of a linear wire by
     one previously unused node preserves comparability of all nodes
     using that wire.

     Every old node retains its original ordering relative to every
     other old node. Any old path that previously ended with

         frontier_node \<rightarrow> output_node

     can instead use

         frontier_node \<rightarrow> new_node_id \<rightarrow> output_node.

     The inserted node is after every old non-output node on the wire
     and before the output boundary node.
  *)
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
  (* Subdividing the final frontier-to-output edge of a linear wire
     preserves both input-boundary conditions.

     The input node still has no predecessor on q.

     It also still has exactly one successor:
       - if the input node is not the frontier, its outgoing edge is
         unchanged;
       - if the input node is the frontier, its old edge to the output
         node is replaced by exactly one edge to new_node_id.
  *)
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
  (* The newly allocated internal node cannot use the canonical input
         boundary-node ID. *)
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
  (* Subdividing the final edge does not introduce any outgoing edge
     from the output node. Therefore, the output node continues to have
     no successor on q.

     The valid frontier supplies the old frontier-to-output edge.
     Since the output previously had no successor, the frontier cannot
     itself be the output node. The newly inserted node is also assumed
     to have a different ID from the output boundary node.
  *)
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
  (* Subdividing the final frontier-to-output edge preserves the unique
     predecessor of the output node.

     Before subdivision, frontier(q) is the unique predecessor of the
     output node.

     After subdivision, the old edge

         frontier(q) \<rightarrow> output(q)

     is removed and replaced by

         frontier(q) \<rightarrow> new_node_id
         new_node_id \<rightarrow> output(q).

     Therefore, new_node_id becomes the unique predecessor of the
     output node.
  *)
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
  (* Subdividing the final edge of a linear wire preserves the required
     predecessor and successor degrees of every operation node using q.

     For old operation nodes:
       - nodes other than the old frontier keep their q-labelled edges;
       - if the old frontier is an operation node, its old successor
         output(q) is replaced by the single successor new_node_id.

     For the newly inserted operation node:
       - frontier(q) is its unique predecessor;
       - output(q) is its unique successor.
  *)
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
  (* Inserting a valid operation at the current construction frontier
     preserves the linear-chain structure of every valid qubit wire.

     For each wire used by the new operation, the existing final edge

         frontier(q) \<rightarrow> output(q)

     is replaced by exactly two edges

         frontier(q) \<rightarrow> new_node
         new_node \<rightarrow> output(q).

     Therefore, the old frontier node still has one successor on q,
     the new operation node has one predecessor and one successor on q,
     and the output node still has one predecessor and no successor.

     Wires not used by the operation are unchanged.
  *)
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
  (* Inserting a valid operation at the current construction frontier
     preserves global graph acyclicity.

     On every affected wire, insertion removes the final edge

         frontier(q) \<rightarrow> output(q)

     and replaces it with

         frontier(q) \<rightarrow> new_node
         new_node \<rightarrow> output(q).

     The new operation node was previously unused, so no path can
     already pass through it. The new node is inserted strictly after
     each affected frontier node and strictly before the corresponding
     output node. Therefore, the new edges cannot introduce a directed
     cycle.
  *)
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
  (* Inserting a valid operation into a valid construction state
     preserves the complete structural validity of the quantum circuit.

     Before insertion:

       1. the circuit is well formed;
       2. the graph is acyclic;
       3. all nodes on each valid wire are comparable; and
       4. every valid wire satisfies the stronger linear-chain
          invariant required by the insertion proofs.

     The previously proved insertion theorems establish that the updated
     circuit remains well formed, acyclic, and wire-linear. Since wire
     linearity implies wire-node comparability, the updated circuit
     satisfies every component of is_valid_quantum_circuit.
  *)
  assumes valid_circuit:
    "is_valid_quantum_circuit circuit"

  assumes valid_state:
    "is_valid_construction_state circuit frontier"

  assumes operation_valid:
    "operation_in_circuit circuit op"

  shows
    "is_valid_quantum_circuit
       (fst (insert_operation circuit frontier op))"
  sorry

lemma initial_construction_state_is_valid:
  (* The initial circuit together with the initial frontier forms a
     valid starting state for repeated operation insertion. *)
  "is_valid_construction_state (initial_circuit number_of_qubits) initial_frontier"

  sorry

(* Example definitions to demonstrate gate and operation *)

definition ex_h_q0 :: operation where
  "ex_h_q0 = \<lparr>op_gate = Gate_H, op_qargs = [Qubit 0]\<rparr>"


definition ex_cnot_q0_q1 :: operation where
  "ex_cnot_q0_q1 =
     \<lparr>op_gate = Gate_CNOT, op_qargs = [Qubit 0, Qubit 1]\<rparr>"

value "ex_cnot_q0_q1"

end