theory QuantumCircuit
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
  | Gate_S
  | Gate_T
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
| "gate_arity Gate_S = 1"
| "gate_arity Gate_T = 1"
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
  unfolding get_input_node_id_def get_output_node_id_def
  apply (cases q; cases r; simp)
  by arith

lemma input_node_id_injective: (* 2 different input nodes cannot have same node ID *)
  "get_input_node_id q = get_input_node_id r \<Longrightarrow> q = r"
  unfolding get_input_node_id_def
  by (cases q; cases r; simp)

lemma output_node_id_injective: (* 2 different output nodes cannot have same node ID *)
  "get_output_node_id q = get_output_node_id r \<Longrightarrow> q = r"
  unfolding get_output_node_id_def
  by (cases q; cases r; simp)

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
  unfolding initial_circuit_def
  by simp

lemma initial_circuit_next_id[simp]:
  (* After initialization, the next available ID is the first operation-node ID. *)
  "next_id (initial_circuit number_of_qubits) =
   get_first_operation_id number_of_qubits"
  unfolding initial_circuit_def
  by simp

lemma initial_circuit_input_node:
  (* For any valid qubit number, the canonical input node ID stores the corresponding InputNode. *)
  assumes "qubit_number < number_of_qubits"
  shows "nodes (initial_circuit number_of_qubits)
          (get_input_node_id (Qubit qubit_number))
        = Some (InputNode (Qubit qubit_number))" (* nodes is a record selector, meaning since it is defined inside the record, we have to pass the record itself as the first parameter *)
  using assms
  unfolding initial_circuit_def initial_nodes_def get_input_node_id_def
  by simp

lemma initial_circuit_output_node:
  (* For any valid qubit number, the canonical output node ID stores the corresponding OutputNode. *)
  assumes "qubit_number < number_of_qubits"
  shows "nodes (initial_circuit number_of_qubits)
          (get_output_node_id (Qubit qubit_number))
        = Some (OutputNode (Qubit qubit_number))" (* nodes is a record selector, meaning since it is defined inside the record, we have to pass the record itself as the first parameter *)
  using assms
  unfolding initial_circuit_def initial_nodes_def get_output_node_id_def
  by simp

lemma initial_circuit_has_wire_edge:
  (* For any valid qubit number, the initial circuit contains the direct wire edge from input to output. *)
  assumes "qubit_number < number_of_qubits"
  shows "make_edge
          (get_input_node_id (Qubit qubit_number))
          (get_output_node_id (Qubit qubit_number))
          (Qubit qubit_number)
        \<in> edges (initial_circuit number_of_qubits)" (* edges is a record selector, meaning since it is defined inside the record, we have to pass the record itself as the first parameter *)
  using assms
  unfolding initial_circuit_def initial_edges_def
  by auto

lemma make_edges_on_different_wires_unequal:
  (* Two edges carrying different qubit-wire labels cannot be equal,
     regardless of their source and target node IDs. *)
  assumes wires_different:
    "first_wire \<noteq> second_wire"
  shows
    "make_edge first_source first_target first_wire
     \<noteq>
     make_edge second_source second_target second_wire"
  using wires_different
  unfolding make_edge_def
  by simp


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

  unfolding wire_reaches_def
  using direct_edge by simp

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


(* ----- Validity check (Well-formedness check) for entire circuit ends ----- *)

(* -------- Fresh node ID helpers begin -------- *)


definition increment_node_id :: "node_id \<Rightarrow> node_id" where
  (* Given a node ID, return the next node ID (Add 1 to it) *)
  "increment_node_id current_node_id = NodeId (node_id_to_nat current_node_id + 1)"

lemma node_id_to_nat_increment_node_id[simp]:
  (* The next node id is 1 more than the present node id *)
  "node_id_to_nat (increment_node_id current_node_id) = node_id_to_nat current_node_id + 1"
  unfolding increment_node_id_def
  by (cases current_node_id; simp)

lemma increment_node_id_not_same[simp]:
  (* Node id before and after increment are not same *)
  "increment_node_id current_node_id \<noteq> current_node_id"
  unfolding increment_node_id_def
  by (cases current_node_id; simp)

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
  unfolding update_frontier_def
  by simp

lemma update_frontier_other[simp]:
  (* Updating the frontier for q does not change the frontier entry
     of any different qubit other_q. *)
  assumes "other_q \<noteq> q"
  shows
    "update_frontier frontier q new_node_id other_q =
     frontier other_q"
  using assms
  unfolding update_frontier_def
  by simp

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
  unfolding insert_node_def
  by simp

lemma valid_frontier_has_unique_successor:
  (* A valid frontier is the final node immediately before the output
     node, so it has exactly one successor on its wire. *)
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

assumes valid_q:
  "qubit_in_circuit circuit q"

shows
  "has_unique_wire_successor circuit q (frontier q)"
  using valid_frontier valid_q
  unfolding is_valid_frontier_def
  by blast

lemma nodes_insert_node_other[simp]: (* helper lemma *)
  (* All other node ids apart from the one where insertion happen, remain unchanged *)
  assumes "other_node_id \<noteq> node_id"
  shows "nodes (insert_node node_id node circuit) other_node_id =
         nodes circuit other_node_id"
  using assms
  unfolding insert_node_def
  by simp

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

proof -
  show ?thesis
    unfolding is_valid_frontier_def
  proof (intro allI impI) (* Pick any valid qubit q. Prove the property for it *)
    fix q (* Arbitrary q *)

    assume valid_q_after: (* Assume this qubit belongs to the new circuit. *)
      "qubit_in_circuit
         (insert_node new_node_id new_node circuit)
         q"

    have valid_q_before:
      "qubit_in_circuit circuit q" (* q is a valid qubit prior to insertion *)
      using valid_q_after (* Use this assumption *)
      unfolding qubit_in_circuit_def insert_node_def (* First "use", then "unfold". So that whatever you are "using" also gets "unfolded" in the subsequent steps *)
      by simp

(* Because the old frontier is valid, and q is valid in the old circuit, there must be some node currently stored at "frontier q" (say frontier_node) 

      That node must:
        1. exist in the node mapping ("old_frontier_node" below)
        2. use wire q ("old_frontier_node_uses_q" below)
        3. have an edge to the output node of q ("old_frontier_edge" below)
    *)
    from valid_frontier valid_q_before
    obtain frontier_node where
      old_frontier_node: 
      "nodes circuit (frontier q) = Some frontier_node"

and old_frontier_node_uses_q:
"node_uses_qubit frontier_node q"

and old_frontier_edge:
"make_edge (frontier q) (get_output_node_id q) q \<in> edges circuit"

and old_frontier_unique_successor:
"has_unique_wire_successor circuit q (frontier q)"

      unfolding is_valid_frontier_def
      by auto

(* new_node_id is unused (main assumption of this lemma), so nodes circuit new_node_id = None 
       But frontier q stores "Some frontier_node"

       Combining these two, we can say that frontier q \<noteq> new_node_id. This is proven below.
    *)
    have frontier_id_not_new_node_id:
      "frontier q \<noteq> new_node_id"
    proof
      assume same_id:
        "frontier q = new_node_id" (* Proof by contradiction *)

      from old_frontier_node
      have "nodes circuit new_node_id = Some frontier_node"
        using same_id by simp

      with node_id_unused 
      show False
        by simp
    qed

    show 
      "\<exists>frontier_node.
            nodes (insert_node new_node_id new_node circuit) (frontier q) = Some frontier_node
            \<and> node_uses_qubit frontier_node q
            \<and> make_edge (frontier q) (get_output_node_id q) q
                 \<in> edges (insert_node new_node_id new_node circuit)
            \<and> has_unique_wire_successor
             (insert_node new_node_id new_node circuit) q (frontier q)"

    proof (intro exI[of _ frontier_node] conjI)
      (* Start the proof by applying the introduction rules exI and conjI
        
        exI \<longrightarrow> Introduction rule for an existential statement P x \<Rightarrow> \<exists>x. P x (Predicate P, witness x)
        
        exI[of _ frontier_node] \<longrightarrow> for the existential statement, figure out the predicate yourself and use frontier_node as the witness. This changes the goal from 
            \<exists>frontier_node. A \<and> B \<and> C
        into:
            A \<and> B \<and> C
          
        conjI \<longrightarrow> splits the conjuction A \<and> B \<and> C into three separate proof goals A, B and C

        Each following show statement proves one of those goals.
      *)
      show "nodes (insert_node new_node_id new_node circuit) (frontier q) = Some frontier_node"
        using frontier_id_not_new_node_id old_frontier_node
        by simp

      show "node_uses_qubit frontier_node q"
        using old_frontier_node_uses_q by simp

      show "make_edge (frontier q) (get_output_node_id q) q 
                \<in> edges (insert_node new_node_id new_node circuit)"

        using old_frontier_edge
        unfolding insert_node_def
        by simp

      show "has_unique_wire_successor
           (insert_node new_node_id new_node circuit) q (frontier q)"
        using old_frontier_unique_successor
        unfolding
          has_unique_wire_successor_def
          wire_edge_relation_def
          insert_node_def
        by simp
    qed
  qed
qed

lemma update_next_id_preserves_valid_frontier:
  (* Updating only the next_id field preserves frontier validity.

     The frontier invariant depends on the circuit's qubit count, node mapping, and edge set. Updating next_id changes none of these fields.
  *)

assumes valid_frontier:
  "is_valid_frontier circuit frontier"

shows 
  "is_valid_frontier (circuit \<lparr> next_id := new_next_id \<rparr>) frontier"

  unfolding is_valid_frontier_def

proof (intro allI impI)
  fix q

  assume valid_q:
    "qubit_in_circuit (circuit\<lparr>next_id := new_next_id\<rparr>) q"

  hence valid_q_before:
    "qubit_in_circuit circuit q"
    unfolding qubit_in_circuit_def
    by simp

  from valid_frontier valid_q_before
  obtain frontier_node where
    frontier_lookup:
    "nodes circuit (frontier q) = Some frontier_node"
    and frontier_uses_q:
    "node_uses_qubit frontier_node q"
    and frontier_edge:
    "make_edge (frontier q) (get_output_node_id q) q
         \<in> edges circuit"
    and frontier_unique_successor:
    "has_unique_wire_successor
         circuit q (frontier q)"
    unfolding is_valid_frontier_def
    by auto

  show
    "\<exists>frontier_node.
        nodes (circuit\<lparr>next_id := new_next_id\<rparr>) (frontier q)
          = Some frontier_node
      \<and> node_uses_qubit frontier_node q
      \<and> make_edge (frontier q) (get_output_node_id q) q
          \<in> edges (circuit\<lparr>next_id := new_next_id\<rparr>)
      \<and> has_unique_wire_successor
          (circuit\<lparr>next_id := new_next_id\<rparr>)
          q
          (frontier q)"
  proof (intro exI[of _ frontier_node] conjI)
    show
      "nodes (circuit\<lparr>next_id := new_next_id\<rparr>)
         (frontier q)
       = Some frontier_node"
      using frontier_lookup
      by simp

    show
      "node_uses_qubit frontier_node q"
      using frontier_uses_q
      by simp

    show
      "make_edge (frontier q) (get_output_node_id q) q
         \<in> edges (circuit\<lparr>next_id := new_next_id\<rparr>)"
      using frontier_edge
      by simp

    show
      "has_unique_wire_successor
         (circuit\<lparr>next_id := new_next_id\<rparr>)
         q
         (frontier q)"
      using frontier_unique_successor
      unfolding
        has_unique_wire_successor_def
        wire_edge_relation_def
      by simp
  qed
qed

lemma edges_insert_edge[simp]: (* helper lemma *)
  (* Edge set after insertion is just union of edge set prior to insertion and the newly added edge *)
  "edges (insert_edge e circuit) = insert e (edges circuit)"
  unfolding insert_edge_def
  by simp

lemma edges_delete_edge[simp]: (* helper lemma *)
  (* Edge set after deletion is just difference of edge set prior to deletion and the deleted edge *)
  "edges (delete_edge e circuit) = edges circuit - {e}"
  unfolding delete_edge_def
  by simp

(* -------- Graph update helpers end -------- *)

(* -------- Initial construction-state lemmas begin -------- *)

lemma initial_frontier_is_valid:
  (* The initial frontier correctly points from each qubit to its input boundary node. *)
  "is_valid_frontier (initial_circuit number_of_qubits) initial_frontier"

proof -
  show ?thesis
    unfolding is_valid_frontier_def
  proof clarify
    fix q
    assume valid_q:
      "qubit_in_circuit (initial_circuit number_of_qubits) q"

    obtain qubit_number where
      q_form: "q = Qubit qubit_number"
      by (cases q)

    from valid_q have q_lt:
      "qubit_number < number_of_qubits"
      unfolding qubit_in_circuit_def
      using q_form
      by simp

    show
      "\<exists>frontier_node.
         nodes (initial_circuit number_of_qubits)
           (initial_frontier q)
           = Some frontier_node
       \<and> node_uses_qubit frontier_node q
       \<and> make_edge
           (initial_frontier q)
           (get_output_node_id q)
           q
         \<in> edges (initial_circuit number_of_qubits)
      \<and> has_unique_wire_successor (initial_circuit number_of_qubits) q (initial_frontier q)"
      using
        q_lt q_form
        all_wires_linear_def
        initial_circuit_has_linear_wires
        initial_circuit_has_wire_edge
        initial_circuit_input_node
        valid_q wire_is_linear_def
      unfolding initial_frontier_def
      by simp
  qed
qed

lemma initial_next_id_is_unused:
  (* The first operation-node ID is unused in the initial circuit. *)
  "next_id_is_unused (initial_circuit number_of_qubits)"
  unfolding next_id_is_unused_def
    initial_circuit_def
    initial_nodes_def
    get_first_operation_id_def
  by simp

lemma initial_existing_node_ids_are_below_next_id:
  (* Every node stored in the initial circuit is a boundary node whose
     numerical ID is strictly smaller than the first operation-node ID.

     The initial node table stores nodes only at IDs below
     2 * number_of_qubits, while next_id is exactly
     NodeId (2 * number_of_qubits).*)
  "all_existing_node_ids_below_next_id (initial_circuit number_of_qubits)"

  unfolding
    all_existing_node_ids_below_next_id_def
    initial_circuit_def
    initial_nodes_def
    get_first_operation_id_def

  using if_False
  by fastforce

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
  unfolding splice_wire_def
  by simp

lemma snd_splice_wire:
  (* Says that the second part of splice_wire response is the updated frontier map *)
  "snd (splice_wire circuit frontier q new_node_id) =
   update_frontier frontier q new_node_id"
  unfolding splice_wire_def
  by simp

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
  unfolding splice_wire_without_updating_frontier_def Let_def
  by simp

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
  unfolding splice_wire_without_updating_frontier_def Let_def
  by simp

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
  unfolding splice_wire_without_updating_frontier_def Let_def
  by simp

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

  using assms
  by (simp add: edges_splice_wire_without_updating_frontier make_edge_def)  

lemma splice_wire_preserves_nodes[simp]:
  (* Splicing a single wire only modifies the edge set and the frontier. The node table remains unchanged. *)
  "nodes (fst (splice_wire circuit frontier q new_node_id)) node_id = nodes circuit node_id"
  unfolding 
    splice_wire_def
    splice_wire_without_updating_frontier_def
    insert_edge_def 
    delete_edge_def
    Let_def
  by simp

lemma splice_wire_without_updating_frontier_preserves_num_qubits[simp]:
  (* Rewiring one qubit wire without updating the frontier changes only the circuit's edges field. The number of qubits remains unchanged. *)
  "num_qubits 
     (splice_wire_without_updating_frontier circuit frontier q new_node_id)
   =
   num_qubits circuit"
  unfolding
    splice_wire_without_updating_frontier_def
    insert_edge_def
    delete_edge_def
    Let_def
  by simp

lemma splice_wire_preserves_num_qubits[simp]:
  (* Splicing a single wire only modifies the edge set and the frontier. The number of qubits remain unchanged *)
  "num_qubits (fst (splice_wire circuit frontier q new_node_id)) = num_qubits circuit"
  unfolding splice_wire_def
  by simp

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

  using assms
  unfolding
    wire_edge_relation_def
    splice_wire_def
    splice_wire_without_updating_frontier_def
    insert_edge_def
    delete_edge_def
    make_edge_def
    Let_def
  by simp

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

proof -
  let ?updated_circuit = "fst (splice_wire circuit frontier q new_node_id)"

  let ?updated_frontier = "snd (splice_wire circuit frontier q new_node_id)"

  show ?thesis
    unfolding is_valid_frontier_def

  proof (intro allI impI)
    fix queried_wire

    assume queried_wire_valid_after:
      "qubit_in_circuit ?updated_circuit queried_wire"

    show
      "\<exists>frontier_node.
         nodes ?updated_circuit (?updated_frontier queried_wire)
           = Some frontier_node
       \<and> node_uses_qubit frontier_node queried_wire
       \<and> make_edge
           (?updated_frontier queried_wire)
           (get_output_node_id queried_wire)
             queried_wire
           \<in> edges ?updated_circuit
       \<and> has_unique_wire_successor
              ?updated_circuit queried_wire
              (?updated_frontier queried_wire)"
    proof (cases "queried_wire = q")
      case True

      have updated_frontier_lookup: 
        "?updated_frontier queried_wire = new_node_id"
        using True
        by (simp add: snd_splice_wire)

      have new_node_exists_after_splice:
        (* splice_wire changes only edges and the frontier. Therefore, the node stored at new_node_id remains new_node *)
        "nodes ?updated_circuit new_node_id = Some new_node"
        unfolding
          splice_wire_def
          splice_wire_without_updating_frontier_def
          Let_def
          insert_edge_def
          delete_edge_def
        using new_node_exists
        by simp

      have new_node_uses_queried_wire:
        (* The inserted node uses q by assumption, and queried_wire = q in this branch. *)
        "node_uses_qubit new_node queried_wire"
        using new_node_uses_wire True
        by simp

      have new_output_edge_exists:
        (* The splice inserts the final edge from new_node_id to the output node of q. Since queried_wire = q, this is exactly the frontier edge required for queried_wire. *)
        "make_edge
           new_node_id
           (get_output_node_id queried_wire)
           queried_wire
         \<in> edges ?updated_circuit"
        unfolding
          splice_wire_def
          splice_wire_without_updating_frontier_def
          Let_def
          insert_edge_def
          delete_edge_def
        using True
        by simp

      have unique_successor:
        "has_unique_wire_successor
           ?updated_circuit
           queried_wire
           (?updated_frontier queried_wire)"
        unfolding has_unique_wire_successor_def
      proof (rule ex1I[of _ "get_output_node_id queried_wire"])

        show
          "(?updated_frontier queried_wire,
            get_output_node_id queried_wire)
           \<in> wire_edge_relation ?updated_circuit queried_wire"
          using
            updated_frontier_lookup
            new_output_edge_exists
          unfolding wire_edge_relation_def
          by simp

      next
        fix successor_id

        assume successor_edge_after:
          "(?updated_frontier queried_wire, successor_id)
             \<in> wire_edge_relation ?updated_circuit queried_wire"

        show
          "successor_id = get_output_node_id queried_wire"
          using
            successor_edge_after
            updated_frontier_lookup
            True
            new_node_not_frontier
            new_node_has_no_other_successor
          unfolding
            wire_edge_relation_def
            splice_wire_def
            splice_wire_without_updating_frontier_def
            insert_edge_def
            delete_edge_def
            make_edge_def
            Let_def
          by auto
      qed

      show ?thesis
        using
          updated_frontier_lookup
          new_node_exists_after_splice
          new_node_uses_queried_wire
          new_output_edge_exists
          unique_successor
        by simp

    next
      case False
      have updated_frontier_unchanged:
        (* Only the frontier entry for q was updated. Because queried_wire is different from q, its frontier entry remains exactly as it was before the splice. *)
        "?updated_frontier queried_wire = frontier queried_wire"
        using False
        by (simp add: snd_splice_wire)

      have queried_wire_valid_before:
        (* The queried wire was valid before the splice because splice_wire preserves the circuit's number of qubits. *)
        "qubit_in_circuit circuit queried_wire"
        using queried_wire_valid_after
        unfolding qubit_in_circuit_def
        by simp

      obtain old_frontier_node where
        old_frontier_node_exists:
        "nodes circuit (frontier queried_wire) = Some old_frontier_node"
        and old_frontier_node_uses_wire:
        "node_uses_qubit old_frontier_node queried_wire"
        and old_output_edge_exists:
        "make_edge
             (frontier queried_wire)
             (get_output_node_id queried_wire)
             queried_wire
           \<in> edges circuit"

and old_frontier_unique_successor:
"has_unique_wire_successor
             circuit
             queried_wire
             (frontier queried_wire)"
        using
          valid_frontier
          queried_wire_valid_before
        unfolding is_valid_frontier_def
        by auto

      have old_edge_is_not_deleted_edge:
        (* The old frontier edge belongs to queried_wire, while the
           deleted edge belongs to q. Since the wires are different,
           the two edge records cannot be equal *)
        "make_edge
           (frontier queried_wire)
           (get_output_node_id queried_wire)
           queried_wire
         \<noteq>
         make_edge
           (frontier q)
           (get_output_node_id q)
           q"
        using False
        unfolding make_edge_def
        by simp

      have old_output_edge_still_exists:
        (* The splice removes only the old edge on q. Since the frontier
           edge of queried_wire is different, it remains in the edge set.
           The two newly inserted edges do not remove any existing edge. *)
        "make_edge
           (frontier queried_wire)
           (get_output_node_id queried_wire)
           queried_wire
         \<in> edges ?updated_circuit"
        using
          old_output_edge_exists
          old_edge_is_not_deleted_edge
        by (simp add: fst_splice_wire edges_splice_wire_without_updating_frontier)

      have old_frontier_node_still_exists:
        (* splice_wire modifies edges and the frontier, but does not modify the circuit's nodes field. *)
        "nodes ?updated_circuit (frontier queried_wire) = Some old_frontier_node"
        using old_frontier_node_exists
        by simp

      have unaffected_wire_relation_unchanged:
        "wire_edge_relation ?updated_circuit queried_wire
         =
         wire_edge_relation circuit queried_wire"
        using False
        by (simp add:splice_wire_preserves_other_wire_relation)

      show ?thesis
        (* For an unaffected wire, reuse its original frontier node.
           Its frontier lookup, stored node, wire membership, and final
           output edge all remain valid after the splice. *)
        using
          updated_frontier_unchanged
          old_frontier_node_still_exists
          old_frontier_node_uses_wire
          old_output_edge_still_exists
          unaffected_wire_relation_unchanged
          has_unique_wire_successor_def
          old_frontier_unique_successor
        by auto
    qed
  qed
qed

lemma wire_edge_relation_update_next_id[simp]:
  (* Updating only next_id does not change the wire-edge relation, since wire_edge_relation depends only on the edge set. *)
  "wire_edge_relation (circuit\<lparr>next_id := new_next_id\<rparr>) q
   =
   wire_edge_relation circuit q"

  unfolding wire_edge_relation_def
  by simp

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

proof (rule set_eqI)
  fix relation_pair :: "node_id \<times> node_id"

  obtain source_id target_id where
    [simp]: "relation_pair = (source_id, target_id)"
    by (cases relation_pair) simp

  show
    "relation_pair
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q
     \<longleftrightarrow>
     relation_pair
       \<in> (wire_edge_relation circuit q
            - {(frontier q, get_output_node_id q)})
          \<union> {(frontier q, new_node_id),
             (new_node_id, get_output_node_id q)}"
    unfolding
      wire_edge_relation_def
      splice_wire_without_updating_frontier_def
      delete_edge_def
      insert_edge_def
      make_edge_def
      Let_def
    by auto
qed

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

proof (rule set_eqI)
  fix relation_pair :: "node_id \<times> node_id"

  obtain source_id target_id where
    [simp]: "relation_pair = (source_id, target_id)"
    by (cases relation_pair) simp

  show
    "relation_pair
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           other_q
     \<longleftrightarrow>
     relation_pair
       \<in> wire_edge_relation circuit other_q"
    using different_wire
    unfolding
      wire_edge_relation_def
      splice_wire_without_updating_frontier_def
      delete_edge_def
      insert_edge_def
      make_edge_def
      Let_def
    by simp
qed

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

proof (cases
    "(source_id, target_id) =
     (frontier q, get_output_node_id q)")

  case True

  have first_new_edge:
    "(frontier q, new_node_id)
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q"
    using wire_edge_relation_after_splice_same_wire
    by simp

  have second_new_edge:
    "(new_node_id, get_output_node_id q)
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q"
    using wire_edge_relation_after_splice_same_wire
    by simp

  have frontier_reaches_new:
    "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       (frontier q)
       new_node_id"
    using first_new_edge
    by (simp add: wire_edge_implies_wire_reaches)

  have new_reaches_output:
    "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       new_node_id
       (get_output_node_id q)"
    using second_new_edge
    by (simp add: wire_edge_implies_wire_reaches)

  have frontier_reaches_output:
    "wire_reaches
       (splice_wire_without_updating_frontier
          circuit frontier q new_node_id)
       q
       (frontier q)
       (get_output_node_id q)"
  proof -
    show ?thesis
      unfolding wire_reaches_def
      using frontier_reaches_new new_reaches_output
      unfolding wire_reaches_def
      by (rule trancl_trans)
  qed

  show ?thesis
    using True frontier_reaches_output
    by simp

next

  case False

  have old_edge_not_deleted:
    "(source_id, target_id)
       \<in> wire_edge_relation circuit q
          - {(frontier q, get_output_node_id q)}"
    using old_edge False
    by simp

  have edge_still_present:
    "(source_id, target_id)
       \<in> wire_edge_relation
           (splice_wire_without_updating_frontier
              circuit frontier q new_node_id)
           q"
    using old_edge_not_deleted
      wire_edge_relation_after_splice_same_wire
    by auto

  show ?thesis
    using edge_still_present
    by (rule wire_edge_implies_wire_reaches)

qed

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

proof -
  let ?updated_circuit =
    "splice_wire_without_updating_frontier
       circuit frontier q new_node_id"

  have old_trancl:
    "(source_id, target_id)
       \<in> (wire_edge_relation circuit q)\<^sup>+"
    using old_reachability
    unfolding wire_reaches_def .

  have preserved_trancl:
    "(source_id, target_id)
       \<in> (wire_edge_relation ?updated_circuit q)\<^sup>+"
    using old_trancl
  proof (induction rule: trancl_induct)

    case (base target_id)

    have preserved_edge:
      "wire_reaches
         ?updated_circuit q source_id target_id"
      using base.hyps
      by (rule old_wire_edge_reaches_after_splice)

    then show ?case
      unfolding wire_reaches_def
      .

  next
    case (step middle_id target_id)

    have preserved_prefix:
      "(source_id, middle_id)
         \<in> (wire_edge_relation ?updated_circuit q)\<^sup>+"
      using step.IH .

    have preserved_last_edge:
      "wire_reaches
         ?updated_circuit q middle_id target_id"
      using step.hyps(2)
      by (rule old_wire_edge_reaches_after_splice)

    have preserved_last_trancl:
      "(middle_id, target_id)
         \<in> (wire_edge_relation ?updated_circuit q)\<^sup>+"
      using preserved_last_edge
      unfolding wire_reaches_def
      .

    show ?case
      using preserved_prefix preserved_last_trancl
      by (rule trancl_trans)

  qed

  show ?thesis
    using preserved_trancl
    unfolding wire_reaches_def
    .
qed

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

proof -
  have old_comparison:
    "node_a = node_b
     \<or> wire_reaches circuit q node_a node_b
     \<or> wire_reaches circuit q node_b node_a"
    using
      old_nodes_comparable
      node_a_lookup
      node_b_lookup
      node_a_uses_q
      node_b_uses_q
    unfolding nodes_comparable_on_wire_def
    by simp

  from old_comparison show ?thesis
  proof (elim disjE)
    assume nodes_equal:
      "node_a = node_b"

    then show ?thesis
      by simp

  next
    assume node_a_reaches_node_b:
      "wire_reaches circuit q node_a node_b"

    have preserved_reachability:
      "wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_a node_b"
      using node_a_reaches_node_b
      by (rule old_wire_reaches_after_splice)

    then show ?thesis
      by simp

  next
    assume node_b_reaches_node_a:
      "wire_reaches circuit q node_b node_a"

    have preserved_reachability:
      "wire_reaches
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)
         q node_b node_a"
      using node_b_reaches_node_a
      by (rule old_wire_reaches_after_splice)

    then show ?thesis
      by simp

  qed
qed

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

proof (induction qs arbitrary: circuit frontier) (* Prove using induction on qubit list, keeping circuit and frontier flexible *)

  case Nil
  then show ?case 
    by simp

next
  case (Cons q qs) 
    (* q is the first wire; 
       qs is the remaining list;
       Cons.IH is induction hypothesis for remaining wires
    *)
  obtain updated_circuit updated_frontier  \<comment>\<open>names for pair produced by splicing the first wire q\<close>
    where splice_result:
      "splice_wire circuit frontier q new_node_id = (updated_circuit, updated_frontier)"
    by (cases "splice_wire circuit frontier q new_node_id")

  have first_splice_preserves_node:
    "nodes updated_circuit node_id = nodes circuit node_id" \<comment>\<open>The circuit returned after splicing the first wire q has the same node stored at node_id as the original circuit.\<close>

  proof-
    have "nodes (fst (splice_wire circuit frontier q new_node_id)) node_id = nodes circuit node_id" 
      \<comment>\<open>A single call to splice_wire changes only edges and the frontier, so the nodes field remains unchanged.\<close>
      unfolding
        splice_wire_def
        splice_wire_without_updating_frontier_def
        Let_def
        insert_edge_def
        delete_edge_def
      by simp
    then show ?thesis
      using splice_result
      by simp
  qed

  have remaining_splices_preserve_nodes:
    "nodes (fst (splice_wires updated_circuit updated_frontier qs new_node_id)) node_id = nodes updated_circuit node_id"  \<comment>\<open>By the induction hypothesis, recursively splicing the remaining
       wires qs preserves the nodes field of updated_circuit.\<close>

    using Cons.IH[of updated_circuit updated_frontier] (* Cons.IH means inductive hypothesis *)
    by simp

  show ?case
    by (simp add: first_splice_preserves_node remaining_splices_preserve_nodes splice_result)
qed

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

  using unaffected_wire

proof (induction qs arbitrary: circuit frontier)
  case Nil
  then show ?case
    by simp

next
  case (Cons current_wire remaining_wires)

  have different_wire:
    "q \<noteq> current_wire"
    using Cons.prems
    by simp


  have unaffected_remaining:
    "q \<notin> set remaining_wires"
    using Cons.prems
    by simp

  obtain updated_circuit updated_frontier where
    first_splice:
    "splice_wire
         circuit
         frontier
         current_wire
         new_node_id
       =
       (updated_circuit, updated_frontier)"
    by (cases
        "splice_wire
             circuit
             frontier
             current_wire
             new_node_id")

  have first_splice_preserves_q:
    "wire_edge_relation updated_circuit q = wire_edge_relation circuit q"
    using
      first_splice
      different_wire
      splice_wire_preserves_other_wire_relation[
        of q current_wire circuit frontier new_node_id]
    by simp

  have remaining_splices_preserve_q:
    "wire_edge_relation
       (fst
         (splice_wires
           updated_circuit
           updated_frontier
           remaining_wires
           new_node_id))
       q
     =
     wire_edge_relation updated_circuit q"
    by (simp add: Cons.IH unaffected_remaining)

  show ?case
    using
      first_splice
      first_splice_preserves_q
      remaining_splices_preserve_q
    by simp
qed

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

  using distinct_wires affected_wire
proof (induction qs arbitrary: circuit frontier)
  case Nil

  then show ?case
    by simp

next
  case (Cons current_wire remaining_wires)

  obtain updated_circuit updated_frontier where
    first_splice:
    "splice_wire
         circuit
         frontier
         current_wire
         new_node_id
       =
       (updated_circuit, updated_frontier)"
    by (cases
        "splice_wire
             circuit
             frontier
             current_wire
             new_node_id")

  show ?case
  proof (cases "current_wire = q")
    case True

    have q_not_in_remaining:
      "q \<notin> set remaining_wires"
      using Cons.prems True
      by simp

    have first_splice_updates_q:
      "wire_edge_relation updated_circuit q
       =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"
      using first_splice True
      unfolding
        splice_wire_def
        splice_wire_without_updating_frontier_def
        wire_edge_relation_def
        insert_edge_def
        delete_edge_def
        make_edge_def
        Let_def
      by auto

    have remaining_splices_preserve_q:
      "wire_edge_relation
         (fst
           (splice_wires
             updated_circuit
             updated_frontier
             remaining_wires
             new_node_id))
         q
       =
       wire_edge_relation updated_circuit q"
      using
        splice_wires_preserves_unaffected_wire_relation[
          OF q_not_in_remaining,
          of updated_circuit updated_frontier new_node_id]
      .

    show ?thesis
      using
        first_splice
        first_splice_updates_q
        remaining_splices_preserve_q
        True
      by simp

  next
    case False

    have remaining_distinct:
      "distinct remaining_wires"
      using Cons.prems
      by simp

    have q_in_remaining:
      "q \<in> set remaining_wires"
      using Cons.prems False
      by simp

    have first_splice_preserves_q:
      "wire_edge_relation updated_circuit q =
       wire_edge_relation circuit q"
      using
        first_splice
        False
        splice_wire_preserves_other_wire_relation[
          of q current_wire circuit frontier new_node_id]
      by simp

    have updated_frontier_preserves_q:
      "updated_frontier q = frontier q"
      using first_splice False
      unfolding
        splice_wire_def
        update_frontier_def
      by auto

    have remaining_splices_update_q:
      "wire_edge_relation
         (fst
           (splice_wires
             updated_circuit
             updated_frontier
             remaining_wires
             new_node_id))
         q
       =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (updated_frontier q, new_node_id)
           (wire_edge_relation updated_circuit q -
              {(updated_frontier q, get_output_node_id q)}))"
      using
        Cons.IH[
          of updated_circuit updated_frontier
          ]
        remaining_distinct
        q_in_remaining
      by simp

    show ?thesis
      using
        first_splice
        remaining_splices_update_q
        first_splice_preserves_q
        updated_frontier_preserves_q
      by simp
  qed
qed

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

  using distinct_wires edge_in_result

proof (induction qs arbitrary: circuit frontier e)
  case Nil
    (* With no wires to splice, splice_wires returns the original circuit
     and frontier unchanged. Therefore, the given edge already belongs
     to the original circuit. *)
  then show ?case
    by simp

next
  case (Cons q qs)

(* Since the complete list q # qs is distinct, the remaining
     list qs is also distinct. This will satisfy the distinctness
     assumption required by the induction hypothesis. *)
  have remaining_wires_distinct:
    "distinct qs"
    using Cons.prems(1)
    by simp

(* Distinctness also tells us that the first wire a does not
     occur again among the remaining wires qs. We will need this
     later when proving that later recursive splices do not change
     the frontier entry originally associated with a different wire. *)
  have first_wire_not_in_remaining:
    "q \<notin> set qs"
    using Cons.prems(1)
    by simp

(* Give names to the circuit and frontier returned after splicing
     the first wire q. This mirrors the recursive definition of
     splice_wires, which performs one splice_wire call before
     recursively processing qs. *)
  obtain updated_circuit updated_frontier where first_splice:
    "splice_wire circuit frontier q new_node_id =
       (updated_circuit, updated_frontier)"
    by (cases "splice_wire circuit frontier q new_node_id")

  have splice_wires_first_step:
    (* Splicing the nonempty list q # qs first performs splice_wire
       on the head wire q. Since first_splice names the returned pair,
       the remaining computation is splice_wires on qs starting from
       updated_circuit and updated_frontier. *)
    "splice_wires
       circuit
       frontier
       (q # qs)
       new_node_id
     =
     splice_wires
       updated_circuit
       updated_frontier
       qs
       new_node_id"
    using first_splice
    by simp

(* Rewrite the original membership assumption using the result of
     the first splice. The edge e is therefore present after recursively
     processing the remaining wires qs. *)
  have edge_after_remaining_splices:
    (* The original assumption says that e is present after processing
       q # qs. Rewriting that computation with splice_wires_first_step
       shows that e is present after processing the remaining qs from
       the state returned by the first splice. *)
    "e \<in> edges
       (fst
         (splice_wires
           updated_circuit
           updated_frontier
           qs
           new_node_id))"
    using Cons.prems(2) first_splice
    by simp

(* Apply the induction hypothesis to the remaining wire list qs.
     Relative to the state produced by the first splice, the edge e
     must either:
       1. already belong to updated_circuit;
       2. be a newly inserted frontier-to-node edge for some wire in qs;
       3. be a newly inserted node-to-output edge for some wire in qs.
  *)

  have remaining_edge_cases:
    (* Apply the induction hypothesis to the recursive processing of qs.

       Relative to the state after the first splice, every resulting
       edge e must be one of:

         1. an edge already present in updated_circuit;
         2. a new edge from updated_frontier r to new_node_id for
            some remaining wire r;
         3. a new edge from new_node_id to the output node of some
            remaining wire r.
    *)
    "e \<in> edges updated_circuit
     \<or> (\<exists>r \<in> set qs.
          e = make_edge
                (updated_frontier r)
                new_node_id
                r)
     \<or> (\<exists>r \<in> set qs.
          e = make_edge
                new_node_id
                (get_output_node_id r)
                r)"
    using
      Cons.IH
      remaining_wires_distinct
      edge_after_remaining_splices
    by simp

(* Prove the required edge classification for the complete
     nonempty wire list q # qs. *)
  from remaining_edge_cases consider
    (old_edge)
    "e \<in> edges updated_circuit"
    | (new_input_edge)
      r where
      "r \<in> set qs"
      "e = make_edge
                 (updated_frontier r)
                 new_node_id
                 r"

| (new_output_edge)
  r where
  "r \<in> set qs"
  "e = make_edge
                 new_node_id
                 (get_output_node_id r)
                 r"
    by auto

  then show ?case
  proof cases
    case old_edge

(* In this branch, e was already present in the intermediate
       circuit produced after splicing the first wire q. *)
    have edge_in_updated_circuit:
      "e \<in> edges updated_circuit"
      using old_edge .

(* The intermediate circuit is exactly the circuit produced by
       splicing the first wire q. *)
    have updated_circuit_eq:
      "updated_circuit =
       splice_wire_without_updating_frontier
         circuit frontier q new_node_id"
      using first_splice
      by (simp add: splice_wire_def)

(* Rewrite edge membership using the concrete circuit produced
       by the first splice. *)
    have edge_after_first_splice:
      "e \<in> edges
         (splice_wire_without_updating_frontier
            circuit frontier q new_node_id)"
      using edge_in_updated_circuit updated_circuit_eq
      by simp

(* A single-wire splice leaves old edges, except for the removed
       edge, and inserts exactly two new edges on wire q. *)
    have first_splice_cases:
      "e \<in> edges circuit
       \<or> e = make_edge
               (frontier q)
               new_node_id
               q
       \<or> e = make_edge
               new_node_id
               (get_output_node_id q)
               q"
      using edge_after_first_splice
        edges_splice_wire_without_updating_frontier
      by auto

(* Since q belongs to set (q # qs), each new edge fits one of
       the existential alternatives required by the theorem. *)
    show ?thesis
      using first_splice_cases
      by auto

  next
    case (new_input_edge r)

(* The witness r belongs to the remaining wire list qs. *)
    have r_in_remaining:
      "r \<in> set qs"
      using new_input_edge(1) .

(* Since q does not occur in qs and r does occur in qs,
       r must be different from the first wire q. *)
    have r_not_q:
      "r \<noteq> q"
      using
        r_in_remaining
        first_wire_not_in_remaining
      by auto

(* The frontier returned by the first splice is exactly the old
       frontier updated at the first wire q. *)
    have updated_frontier_eq:
      "updated_frontier =
       update_frontier frontier q new_node_id"
      using first_splice
      by (simp add: splice_wire_def)

(* Since r and q are different wires, the first splice did not
       change the frontier entry for r. *)
    have frontier_r_unchanged:
      "updated_frontier r = frontier r"
      using
        updated_frontier_eq
        r_not_q
      by simp

(* Rewrite the edge using the original frontier and show that r
       belongs to the complete wire list q # qs. *)
    show ?thesis
    proof (rule disjI2, rule disjI1)
      (* Choose r as the affected wire witnessing the new input edge. *)
      show
        "\<exists>r' \<in> set (q # qs).
           e = make_edge
                 (frontier r')
                 new_node_id
                 r'"
      proof (intro bexI[of _ r])
        (* Rewrite updated_frontier r to frontier r in the edge
           equation supplied by the induction hypothesis. *)
        show
          "e = make_edge
                 (frontier r)
                 new_node_id
                 r"
          using
            new_input_edge(2)
            frontier_r_unchanged
          by simp

(* A wire in qs also belongs to q # qs. *)
        show
          "r \<in> set (q # qs)"
          using r_in_remaining
          by simp
      qed
    qed

  next
    case (new_output_edge r)
      (* The witness r belongs to the remaining wire list qs. *)
    have r_in_remaining:
      "r \<in> set qs"
      using new_output_edge(1) .

(* Since r belongs to qs, it also belongs to the complete wire list q # qs. Therefore, the edge matches the third alternative of the theorem statement. *)
    show ?thesis
    proof (rule disjI2, rule disjI2)

      show
        "\<exists>r' \<in> set (q # qs).
            e =
              make_edge
                new_node_id
                (get_output_node_id r')
                r'"
      proof (intro bexI[of _ r])

(* This is exactly the equality supplied by the induction hypothesis. *)
        show
          "e =
             make_edge
               new_node_id
               (get_output_node_id r)
               r"
          using new_output_edge(2)
          .

(* Every wire in qs also belongs to q # qs. *)
        show
          "r \<in> set (q # qs)"
          using r_in_remaining
          by simp
      qed
    qed
  qed
qed    

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

  using
    valid_frontier
    new_node_exists
    new_node_uses_all_wires
    distinct_wires
    new_node_not_frontiers
    new_node_has_no_other_successors \<comment>\<open>Passes assumptions to the induction proof\<close>

proof (induction qs arbitrary: circuit frontier) \<comment>\<open>Circuit and frontier will be updated in recursive calls, hence arbitrary\<close>
  case Nil
    (* With no wires to splice, splice_wires returns the original circuit and frontier unchanged. Therefore the original valid-frontier assumption proves the result directly. *)
  then show ?case by simp

next
  case (Cons q qs)

  obtain updated_circuit updated_frontier  \<comment>\<open>names for pair produced by splicing the first wire q\<close>
    where splice_result:
      "splice_wire circuit frontier q new_node_id = (updated_circuit, updated_frontier)"
    by (cases "splice_wire circuit frontier q new_node_id")

  have new_node_uses_first_wire:
    "node_uses_qubit new_node q"
    (* Since q is the head of q # qs and the new node uses every wire in that list, the new node must use q. *)
    using Cons.prems(3)
    by simp

  have new_node_not_first_frontier:
    "new_node_id \<noteq> frontier q"
    using Cons.prems(5)
    by simp

  have new_node_has_no_other_successor_on_first_wire:
    "\<And>successor_id.
       (new_node_id, successor_id)
         \<in> wire_edge_relation circuit q
       \<Longrightarrow> successor_id = get_output_node_id q"
    using Cons.prems(6)
    by simp

  have first_splice_preserves_frontier:
    (* Splicing the first wire produces a circuit and frontier that still satisfy the valid-frontier invariant. *)
    "is_valid_frontier updated_circuit updated_frontier"

  proof -
    have
      "is_valid_frontier
         (fst (splice_wire circuit frontier q new_node_id))
         (snd (splice_wire circuit frontier q new_node_id))"
      using
        splice_wire_preserves_valid_frontier[
          OF
          Cons.prems(1)
          Cons.prems(2)
          new_node_uses_first_wire
          new_node_not_first_frontier
          new_node_has_no_other_successor_on_first_wire
          ]
      .

    then show ?thesis
      using splice_result
      by simp
  qed


  have new_node_still_exists:
    (* Splicing the first wire does not modify the nodes field, so the inserted node remains stored at new_node_id. *)
    "nodes updated_circuit new_node_id = Some new_node"
  proof -
    have "nodes (fst (splice_wire circuit frontier q new_node_id)) new_node_id = nodes circuit new_node_id"
      by simp

    then show ?thesis
      using splice_result Cons.prems(2)
      by simp
  qed

  have new_node_uses_remaining_wires:
    (* If the new node uses every wire in q # qs, it also uses every
       wire in the tail qs. *)
    "\<forall>wire \<in> set qs. node_uses_qubit new_node wire"
    using Cons.prems(3)
    by simp

  have remaining_wires_distinct:
    (* Since q # qs is distinct, the tail qs is also distinct. *)
    "distinct qs"
    using Cons.prems(4)
    by simp

  have new_node_not_remaining_frontiers:
    (* The first splice updates only the frontier entry for q.

       Every wire in qs is different from q because the original wire
       list is distinct. Therefore, the frontier entries for all
       remaining wires are unchanged, and the inserted node is still
       different from those frontier nodes.
    *)
    "\<forall>wire \<in> set qs.
       new_node_id \<noteq> updated_frontier wire"
  proof (intro ballI)
    fix wire

    assume wire_in_remaining:
      "wire \<in> set qs"

    have wire_not_first:
      "wire \<noteq> q"
      using Cons.prems(4) wire_in_remaining
      by auto

    have remaining_frontier_unchanged:
      "updated_frontier wire = frontier wire"
      using splice_result wire_not_first
      by (simp add: splice_wire_def split_pairs)

    have new_node_not_remaining_frontiers:
      (* The first splice updates only the frontier entry for q.

       Every wire in qs is different from q because the original wire
       list is distinct. Therefore, the frontier entries for all
       remaining wires are unchanged, and the inserted node is still
       different from those frontier nodes.
    *)
      "\<forall>wire \<in> set qs.
       new_node_id \<noteq> updated_frontier wire"
    proof (intro ballI)
      fix wire

      assume wire_in_remaining:
        "wire \<in> set qs"

      have wire_not_first:
        "wire \<noteq> q"
        using Cons.prems(4) wire_in_remaining
        by auto

      have remaining_frontier_unchanged:
        "updated_frontier wire = frontier wire"
        using splice_result wire_not_first
        by (simp add: splice_wire_def split_pairs)

      have new_node_not_old_frontier:
        "new_node_id \<noteq> frontier wire"
        using Cons.prems(5) wire_in_remaining
        by simp

      show
        "new_node_id \<noteq> updated_frontier wire"
        using
          remaining_frontier_unchanged
          new_node_not_old_frontier
        by simp
    qed

    have new_node_not_old_frontier:
      "new_node_id \<noteq> frontier wire"
      using Cons.prems(5) wire_in_remaining
      by simp

    show
      "new_node_id \<noteq> updated_frontier wire"
      using
        remaining_frontier_unchanged
        new_node_not_old_frontier
      by simp
  qed

  have new_node_has_no_other_successors_remaining:
    (* The first splice changes only the q-labelled wire relation.

       Since every remaining wire differs from q, its wire relation is
       unchanged. Therefore, the original no-conflicting-successor
       property transfers to updated_circuit for every remaining wire.
    *)
    "\<forall>wire \<in> set qs.
       (\<forall>successor_id.
          (new_node_id, successor_id)
            \<in> wire_edge_relation updated_circuit wire
          \<longrightarrow> successor_id = get_output_node_id wire)"
  proof (intro ballI allI impI)
    fix wire successor_id

    assume wire_in_remaining:
      "wire \<in> set qs"

    assume successor_edge_after:
      "(new_node_id, successor_id)
         \<in> wire_edge_relation updated_circuit wire"

    have wire_not_first:
      "wire \<noteq> q"
      using Cons.prems(4) wire_in_remaining
      by auto

    have remaining_wire_relation_unchanged:
      "wire_edge_relation updated_circuit wire =
       wire_edge_relation circuit wire"
      using
        splice_result
        wire_not_first
        splice_wire_preserves_other_wire_relation[
          of wire q circuit frontier new_node_id]
      by simp

    have successor_edge_before:
      "(new_node_id, successor_id)
         \<in> wire_edge_relation circuit wire"
      using
        successor_edge_after
        remaining_wire_relation_unchanged
      by simp

    show
      "successor_id = get_output_node_id wire"
      using
        Cons.prems(6)
        wire_in_remaining
        successor_edge_before
      by simp
  qed

  have remaining_splices_preserve_frontier:
    (* Apply the induction hypothesis to the circuit and frontier
       obtained after splicing the first wire. *)
    "is_valid_frontier
       (fst
         (splice_wires
           updated_circuit
           updated_frontier
           qs
           new_node_id))
       (snd
         (splice_wires
           updated_circuit
           updated_frontier
           qs
           new_node_id))"
    using Cons.IH[
        OF
        first_splice_preserves_frontier
        new_node_still_exists
        new_node_uses_remaining_wires
        remaining_wires_distinct
        new_node_not_remaining_frontiers
        new_node_has_no_other_successors_remaining
        ] .

  show ?case
    using splice_result remaining_splices_preserve_frontier
    by simp
qed

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

proof -
  let ?circuit1 = "insert_node (next_id circuit) (OperationNode op) circuit"
  let ?splice_result = "splice_wires ?circuit1 frontier (op_qargs op) (next_id circuit)"

  let ?circuit2 = "fst ?splice_result"
  let ?frontier2 = "snd ?splice_result"

  let ?final_circuit = "?circuit2 \<lparr> next_id := increment_node_id (next_id circuit) \<rparr>"

  have valid_frontier:
    "is_valid_frontier circuit frontier"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have next_id_unused:
    "next_id_is_unused circuit"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have circuit_well_formed:
    "is_well_formed_circuit circuit"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have valid_operation:
    "is_valid_operation op"
    using operation_valid_for_circuit
    unfolding operation_in_circuit_def
    by simp

  have next_node_id_unused:
    (* next_id_is_unused means that no node is currently stored at the node ID that insert_operation is about to allocate. *)
    "nodes circuit (next_id circuit) = None"
    using next_id_unused
    unfolding next_id_is_unused_def
    by simp

  have frontier_after_insert_is_valid:
    (* Inserting the OperationNode at the unused next_id leaves the existing frontier valid. *)
    "is_valid_frontier ?circuit1 frontier"
    using valid_frontier next_node_id_unused
    by (rule insert_node_at_unused_id_preserves_valid_frontier)

  have operation_node_exists:
    (* After insert_node, the new OperationNode is stored at the old next_id of the circuit. *)
    "nodes ?circuit1 (next_id circuit) = Some (OperationNode op)"
    by simp

  have operation_node_uses_all_qubits:
    (* By definition, an OperationNode uses exactly the qubits listed in the operation's op_qargs field. *)
    "\<forall>q \<in> set (op_qargs op). node_uses_qubit (OperationNode op) q"
    by simp

  have operation_wires_distinct:
    (* A valid operation does not list the same qubit more than once. *)
    "distinct (op_qargs op)"
    using valid_operation
    unfolding is_valid_operation_def
    by simp

  have new_node_not_existing_frontiers:
    (* Every frontier ID already stores a node. Since next_id is unused,
       it cannot equal the frontier ID of any affected wire. *)
    "\<forall>q \<in> set (op_qargs op).
       next_id circuit \<noteq> frontier q"
  proof (intro ballI)
    fix q

    assume q_in_operation:
      "q \<in> set (op_qargs op)"

    have q_valid:
      "qubit_in_circuit circuit q"
      using
        operation_valid_for_circuit
        q_in_operation
      unfolding operation_in_circuit_def
      by simp

    from valid_frontier q_valid
    obtain frontier_node where frontier_exists:
      "nodes circuit (frontier q) = Some frontier_node"
      unfolding is_valid_frontier_def
      by blast

    show
      "next_id circuit \<noteq> frontier q"
    proof
      assume same_id:
        "next_id circuit = frontier q"

      from next_node_id_unused same_id have
        "nodes circuit (frontier q) = None"
        by simp

      with frontier_exists show False
        by simp
    qed
  qed

  have new_node_has_no_conflicting_successors:
    (* The old next_id was unused. Since every old edge is well formed,
       no old edge can use next_id as its source. Inserting the node does
       not alter the edge set, so the freshly inserted node initially has
       no outgoing edge on any affected wire. *)
    "\<forall>q \<in> set (op_qargs op).
       (\<forall>successor_id.
          ((next_id circuit), successor_id)
            \<in> wire_edge_relation ?circuit1 q
          \<longrightarrow> successor_id = get_output_node_id q)"
  proof (intro ballI allI impI)
    fix q successor_id

    assume successor_edge:
      "(next_id circuit, successor_id)
        \<in> wire_edge_relation ?circuit1 q"

    have old_edge:
      "make_edge (next_id circuit) successor_id q
        \<in> edges circuit"
      using successor_edge
      unfolding
        wire_edge_relation_def
        insert_node_def
      by simp

    have well_formed_edges:
      "are_well_formed_edges circuit"
      using circuit_well_formed
      unfolding is_well_formed_circuit_def
      by simp

    from well_formed_edges old_edge have source_exists:
      "node_exists circuit (next_id circuit)"
      unfolding
        are_well_formed_edges_def
        is_well_formed_edge_def
        make_edge_def
      by auto

    have False
      using
        source_exists
        next_node_id_unused
      unfolding node_exists_def
      by simp

    then show
      "successor_id = get_output_node_id q"
      by simp
  qed

  have frontier_after_splice:
    (* Splicing the newly inserted operation node into all of its qubit
       wires preserves the strengthened frontier invariant. *)
    "is_valid_frontier ?circuit2 ?frontier2"
    using
      frontier_after_insert_is_valid
      operation_node_exists
      operation_node_uses_all_qubits
      operation_wires_distinct
      new_node_not_existing_frontiers
      new_node_has_no_conflicting_successors
    by (rule splice_wires_preserve_valid_frontier)

  have frontier_after_next_id_update:
    (* Advancing next_id changes only the allocator state.
     The frontier depends only on the node table, edge set,
     and qubit count, so it remains valid. *)
    "is_valid_frontier ?final_circuit ?frontier2"
    using frontier_after_splice
    by (rule update_next_id_preserves_valid_frontier)

  have insert_operation_result:
    (* insert_operation returns exactly the final circuit and frontier
     represented by the local abbreviations above. *)
    "insert_operation circuit frontier op = (?final_circuit, ?frontier2)"

  proof -
    obtain spliced_circuit updated_frontier where
      splice_result:
      "?splice_result = (spliced_circuit, updated_frontier)"
      by (cases ?splice_result)

    show ?thesis
      unfolding insert_operation_def
      using splice_result
      by simp
  qed

  show ?thesis
    using
      frontier_after_next_id_update
      insert_operation_result
    by simp
qed

lemma insert_operation_new_node:
  (* After insertion, looking up the node whose ID was the old "next_id" returns the newly inserted node *)
  "nodes (fst (insert_operation circuit frontier op))
         (next_id circuit)
   = Some (OperationNode op)"

proof -
  let ?new_node_id = "next_id circuit" 
    (* The ID at which the new operation node will be stored. *)

  let ?circuit_with_new_node = "insert_node ?new_node_id (OperationNode op) circuit"
    (* The circuit after storing the new operation node, but before rewiring any qubit wires. *)

  let ?spliced_result = "splice_wires ?circuit_with_new_node frontier (op_qargs op) ?new_node_id "
    (* The pair containing the rewired circuit and updated frontier. *)

  let ?spliced_circuit = "fst ?spliced_result"
    (* The circuit component returned after all required wires are spliced. *)

  let ?updated_frontier = "snd ?spliced_result"
    (* The frontier component returned after all required wires are spliced. *)

  let ?final_circuit = "?spliced_circuit \<lparr> next_id := increment_node_id ?new_node_id \<rparr>"
    (* The final circuit returned by insert_operation, obtained by advancing next_id after rewiring *)

  have node_exists_after_inserting:
    "nodes ?circuit_with_new_node ?new_node_id = Some (OperationNode op)"
    (* Immediately after insert_node, looking up the fresh node ID returns the newly inserted operation node. *)
    unfolding insert_node_def
    by simp

  have node_exists_after_splicing:
    "nodes ?spliced_circuit ?new_node_id = Some (OperationNode op)"
    (* After rewiring the qubit wires, the newly inserted operation node is still stored at the fresh node ID. *)
    using node_exists_after_inserting
    by simp

  have updating_next_id_preserves_nodes:
    (* Updating next_id changes only the next_id field, so the new operation node remains stored at the fresh ID. *)
    "nodes ?final_circuit ?new_node_id = Some (OperationNode op)"
    using node_exists_after_splicing
    by simp

  have insert_operation_returns_final_circuit:
    "fst (insert_operation circuit frontier op) = ?final_circuit"
    (* The circuit returned by insert_operation is the final circuit constructed above. *)
  proof -
    obtain spliced_circuit updated_frontier where
      spliced_result: "?spliced_result = (spliced_circuit, updated_frontier)"
      by (cases ?spliced_result)
        \<comment>\<open>Split the pair returned by splice_wires into its circuit and frontier components.\<close>

    then show ?thesis
      unfolding insert_operation_def
      by simp
  qed

  show ?thesis
    using insert_operation_returns_final_circuit
    by simp
qed

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
proof -
  show ?thesis
    using different_node_id
    unfolding
      insert_operation_def
      Let_def
      insert_node_def
      increment_node_id_def
    by simp
qed

lemma insert_operation_next_id[simp]:
  (* After insertion, next_id of the new circuit is 1 more than the next_id of the circuit before insertion *)
  "next_id (fst (insert_operation circuit frontier op)) =
   increment_node_id (next_id circuit)"

proof -
  let ?new_node_id = "next_id circuit"
    (* The ID at which the new operation node will be stored. *)

  let ?circuit_with_new_node = "insert_node ?new_node_id (OperationNode op) circuit"
    (* The circuit after storing the new operation node, but before rewiring any qubit wires. *)

  let ?spliced_result = "splice_wires ?circuit_with_new_node frontier (op_qargs op) ?new_node_id"
    (* The pair containing the rewired circuit and updated frontier. *)

  obtain spliced_circuit updated_frontier where
    spliced_result: "?spliced_result = (spliced_circuit, updated_frontier)"
    by (cases ?spliced_result)
      \<comment>\<open>Split the pair returned by splice_wires into its circuit and frontier components.\<close>

  have returned_circuit:
    "fst (insert_operation circuit frontier op) = 
       spliced_circuit \<lparr> next_id := increment_node_id ?new_node_id \<rparr>"
    (* New circuit returned by insert_operation is same as "spliced_circuit" whose next_id is the incremented node_id *)
    using spliced_result
    unfolding insert_operation_def
    by simp

  show ?thesis
    using returned_circuit
    by simp
qed

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

proof -
  have existing_old_node_is_below_next_id:
    (* Restate the original allocation invariant in a form that can be
       directly applied to any node known to exist in the old circuit. *)
    "\<And>existing_node_id.
       nodes circuit existing_node_id \<noteq> None
       \<Longrightarrow>
       node_id_to_nat existing_node_id < node_id_to_nat (next_id circuit)"
    using valid_allocation
    unfolding all_existing_node_ids_below_next_id_def
    by simp

  show ?thesis
    unfolding all_existing_node_ids_below_next_id_def

  proof (intro allI impI)
    fix existing_node_id
    assume node_exists_after_insertion:
      (* Pick an arbitrary node ID that contains a node in the circuit
         returned by insert_operation. *)
      "nodes (fst (insert_operation circuit frontier op)) existing_node_id \<noteq> None"

    show "node_id_to_nat existing_node_id < 
          node_id_to_nat (next_id (fst (insert_operation circuit frontier op)))"

    proof (cases "existing_node_id = next_id circuit")
      case True
      then show ?thesis
        by simp
    next
      case False

      have node_existed_before_insertion:
        (* Since existing_node_id differs from the allocated ID,
           insert_node did not modify its node-table entry.

           splice_wires changes only edges and the frontier, and the final
           record update changes only next_id. Therefore, this node must
           already have existed in the original circuit.
        *)
        "nodes circuit existing_node_id \<noteq> None"
        using node_exists_after_insertion False
        unfolding insert_operation_def Let_def
        by simp

      have old_id_is_below_old_next_id:
        (* Apply the original sequential-allocation invariant to this
           previously existing node. *)
        "node_id_to_nat existing_node_id
         <
         node_id_to_nat (next_id circuit)"

        using
          existing_old_node_is_below_next_id
          node_existed_before_insertion
        by simp

      show ?thesis
        (* insert_operation increments next_id by one. Hence anything
           smaller than the old next_id is also smaller than the new one. *)
        using old_id_is_below_old_next_id
        by simp
    qed
  qed
qed

lemma insert_operation_num_qubits[simp]:
  (* Inserting an operation does not change the number of qubits in the circuit. *)
  "num_qubits (fst (insert_operation circuit frontier op)) =
   num_qubits circuit"

proof -
  let ?new_node_id = "next_id circuit"
    (* The ID at which the new operation node will be stored. *)

  let ?circuit_with_new_node =
    "insert_node ?new_node_id (OperationNode op) circuit"
    (* The circuit after storing the new operation node,
     but before rewiring any qubit wires. *)

  let ?spliced_result =
    "splice_wires
       ?circuit_with_new_node
       frontier
       (op_qargs op)
       ?new_node_id"
    (* The pair containing the rewired circuit and updated frontier. *)

  obtain spliced_circuit updated_frontier where
    spliced_result:
    "?spliced_result = (spliced_circuit, updated_frontier)"
    by (cases ?spliced_result)
      \<comment>\<open>Split the pair returned by splice_wires into its circuit and frontier components.\<close>

  have inserting_node_preserves_num_qubits:
    "num_qubits ?circuit_with_new_node = num_qubits circuit"
    (* Inserting the new operation node changes only the nodes field,
       so the number of qubits remains unchanged. *)
    unfolding insert_node_def
    by simp

  have splicing_wires_preserves_num_qubits:
    (* For any circuit, frontier, qubit list, and node ID,
       splice_wires does not change the number of qubits. *)
    "num_qubits
       (fst
         (splice_wires
           current_circuit
           current_frontier
           qubits
           node_id))
     = num_qubits current_circuit"

for current_circuit current_frontier qubits node_id
  \<comment>\<open>Make this a general local fact rather than restricting it to the current circuit and operation.\<close>

  proof (induction qubits arbitrary: current_circuit current_frontier)
    case Nil
      (* If there are no wires to splice, splice_wires returns the original circuit. *)

    then show ?case
      by simp

  next
    case (Cons q qs)
      (* For a nonempty wire list, first splice wire q,
       then recursively splice the remaining wires qs. *)

    obtain updated_circuit updated_frontier where
      splice_result:
      "splice_wire
           current_circuit
           current_frontier
           q
           node_id
         =
         (updated_circuit, updated_frontier)"
      by (cases
          "splice_wire
               current_circuit
               current_frontier
               q
               node_id")
          \<comment>\<open>Split the result of the first wire splice into its updated circuit and frontier.\<close>

    have recursive_splicing_preserves_num_qubits:
      "num_qubits
         (fst
           (splice_wires
             updated_circuit
             updated_frontier
             qs
             node_id))
       =
       num_qubits updated_circuit"
      (* By the induction hypothesis, splicing the remaining wires
         does not change the qubit count of the updated circuit. *)
      using Cons.IH
      by simp

    have first_splice_preserves_num_qubits:
      "num_qubits updated_circuit =
       num_qubits current_circuit"
      (* Splicing the first wire changes only edges and the frontier,
         so the number of qubits remains unchanged. *)
      using
        splice_result
        splice_wire_preserves_num_qubits[
          of current_circuit current_frontier q node_id]
      by simp

    show ?case
      (* Combining the first splice with the recursive splicing step
         shows that the entire splice_wires call preserves num_qubits. *)
      using
        splice_result
        recursive_splicing_preserves_num_qubits
        first_splice_preserves_num_qubits
      by simp
  qed

  have spliced_circuit_preserves_num_qubits:
    "num_qubits spliced_circuit =
     num_qubits circuit"
    (* The circuit obtained after inserting the node and splicing all
       affected wires has the same number of qubits as the original circuit. *)
  proof -
    have
      "num_qubits (fst ?spliced_result) =
       num_qubits ?circuit_with_new_node"
      (* Applying the general splice_wires preservation fact to the actual
         qubit arguments of the inserted operation. *)
      using
        splicing_wires_preserves_num_qubits[
          of ?circuit_with_new_node
          frontier
          "op_qargs op"
          ?new_node_id]
      by simp

    also have
      "num_qubits ?circuit_with_new_node =
       num_qubits circuit"
      (* The earlier node insertion did not change the qubit count. *)
      using inserting_node_preserves_num_qubits .

    finally show ?thesis
      (* Replace fst ?spliced_result with the named spliced_circuit. *)
      using spliced_result
      by simp
  qed

  have returned_circuit:
    "fst (insert_operation circuit frontier op) =
       spliced_circuit
         \<lparr>next_id := increment_node_id ?new_node_id\<rparr>"
    (* insert_operation returns the rewired circuit with next_id advanced
       to the next unused node ID. *)
    using spliced_result
    unfolding insert_operation_def
    by simp

  show ?thesis
    (* Updating next_id changes only the next_id field,
       so the final returned circuit has the same qubit count. *)
    using
      returned_circuit
      spliced_circuit_preserves_num_qubits
    by simp
qed

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

proof -
  let ?updated_circuit = "fst (insert_operation circuit frontier op)"

  have boundary_nodes:
    "are_well_formed_boundary_nodes ?updated_circuit"
  proof -
    (* Extract the original boundary-node invariant from the assumption
       that the original circuit is well formed. *)
    have old_boundary_nodes:
      "are_well_formed_boundary_nodes circuit"
      using circuit_well_formed
      unfolding is_well_formed_circuit_def
      by simp

    show ?thesis
      unfolding are_well_formed_boundary_nodes_def

    proof (intro allI impI)
      fix qubit_number

      assume qubit_valid_after:
        "qubit_number < num_qubits ?updated_circuit"

(* insert_operation does not alter the circuit's qubit count.
         Therefore, a qubit valid after insertion was also valid before
         insertion. *)
      have qubit_valid_before:
        "qubit_number < num_qubits circuit"
        using qubit_valid_after
        by simp

      have old_input_node:
        "nodes circuit (get_input_node_id (Qubit qubit_number)) =
           Some (InputNode (Qubit qubit_number))"
        using old_boundary_nodes qubit_valid_before
        unfolding are_well_formed_boundary_nodes_def
        by simp

      have old_output_node:
        "nodes circuit (get_output_node_id (Qubit qubit_number)) =
           Some (OutputNode (Qubit qubit_number))"
        using old_boundary_nodes qubit_valid_before
        unfolding are_well_formed_boundary_nodes_def
        by simp

      have input_id_not_next_id:
        "get_input_node_id (Qubit qubit_number)
         \<noteq> next_id circuit"
      proof
        assume same_id:
          "get_input_node_id (Qubit qubit_number)
           = next_id circuit"

        have input_id_below_next_id:
          "node_id_to_nat
             (get_input_node_id (Qubit qubit_number))
           <
           node_id_to_nat (next_id circuit)"
          using valid_allocation old_input_node
          unfolding all_existing_node_ids_below_next_id_def
          by simp

        show False
          using input_id_below_next_id same_id
          by simp
      qed

      have output_id_not_next_id:
        "get_output_node_id (Qubit qubit_number)
         \<noteq> next_id circuit"
      proof
        assume same_id:
          "get_output_node_id (Qubit qubit_number)
           = next_id circuit"

        have output_id_below_next_id:
          "node_id_to_nat
             (get_output_node_id (Qubit qubit_number))
           <
           node_id_to_nat (next_id circuit)"
          using valid_allocation old_output_node
          unfolding all_existing_node_ids_below_next_id_def
          by simp

        show False
          using output_id_below_next_id same_id
          by simp
      qed

      show
        "nodes ?updated_circuit
           (get_input_node_id (Qubit qubit_number))
         =
         Some (InputNode (Qubit qubit_number))
         \<and>
         nodes ?updated_circuit
           (get_output_node_id (Qubit qubit_number))
         =
         Some (OutputNode (Qubit qubit_number))"
      proof
        show
          "nodes ?updated_circuit
             (get_input_node_id (Qubit qubit_number))
           =
           Some (InputNode (Qubit qubit_number))"
          using input_id_not_next_id old_input_node
          unfolding insert_operation_def Let_def
          by simp

        show
          "nodes ?updated_circuit
             (get_output_node_id (Qubit qubit_number))
           =
           Some (OutputNode (Qubit qubit_number))"
          using output_id_not_next_id old_output_node
          unfolding insert_operation_def Let_def
          by simp
      qed
    qed
  qed

  have well_formed_edges:
    (* Every edge present after inserting the operation is well formed.

       An updated edge is classified into one of three cases:
         1. an edge inherited from the original circuit;
         2. a new edge from the old frontier node to the operation node;
         3. a new edge from the operation node to the output node.
    *)
    "are_well_formed_edges ?updated_circuit"
  proof -
    (* The original circuit is well formed, so every edge originally
       present in it satisfies the edge well-formedness predicate. *)
    have old_edges_well_formed:
      "are_well_formed_edges circuit"
      using circuit_well_formed
      unfolding is_well_formed_circuit_def
      by simp

(* The operation is valid for the original circuit. Therefore, all
       wires used by the operation belong to the circuit and the wire
       list contains no duplicates. *)
    have operation_wires_distinct:
      "distinct (op_qargs op)"
      using operation_valid_for_circuit
      unfolding operation_in_circuit_def
        is_valid_operation_def
      by simp

(* Prove the universal condition defining well-formed edges by
       selecting an arbitrary edge from the updated circuit. *)
    show ?thesis
      unfolding are_well_formed_edges_def
    proof (intro ballI)
      fix e

      assume edge_in_updated:
        "e \<in> edges ?updated_circuit"

(* The final next_id update does not modify the edge set.
         Therefore, e belongs to the circuit returned by splice_wires. *)
      have edge_in_spliced_result:
        "e \<in> edges
           (fst
             (splice_wires
               (insert_node
                 (next_id circuit)
                 (OperationNode op)
                 circuit)
               frontier
               (op_qargs op)
               (next_id circuit)))"
        using edge_in_updated
        unfolding insert_operation_def Let_def
        by simp

(* Apply the recursive splice-edge classification.

         Every resulting edge is either:
           1. already present before splicing;
           2. a frontier-to-operation edge;
           3. an operation-to-output edge.
      *)
      have updated_edge_cases:
        "e \<in> edges circuit
         \<or> (\<exists>q \<in> set (op_qargs op).
              e = make_edge
                    (frontier q)
                    (next_id circuit)
                    q)
         \<or> (\<exists>q \<in> set (op_qargs op).
              e = make_edge
                    (next_id circuit)
                    (get_output_node_id q)
                    q)"
      proof -
        have splice_cases:
          "e \<in> edges
               (insert_node
                 (next_id circuit)
                 (OperationNode op)
                 circuit)
           \<or> (\<exists>q \<in> set (op_qargs op).
                e = make_edge
                      (frontier q)
                      (next_id circuit)
                      q)
           \<or> (\<exists>q \<in> set (op_qargs op).
                e = make_edge
                      (next_id circuit)
                      (get_output_node_id q)
                      q)"
          using edges_splice_wires_cases[
              OF operation_wires_distinct edge_in_spliced_result]
          .

(* insert_node changes only the node table, so an edge present
           before splicing is an edge from the original circuit. *)
        show ?thesis
          using splice_cases
          unfolding insert_node_def
          by simp
      qed

(* Convert the nested disjunction into three explicitly named
         cases so that each edge kind can be proved separately. *)
      from updated_edge_cases consider
        (old_edge)
        "e \<in> edges circuit"

| (new_input_edge)
  q where
  "q \<in> set (op_qargs op)"
  "e = make_edge
                     (frontier q)
                     (next_id circuit)
                     q"

| (new_output_edge)
  q where
  "q \<in> set (op_qargs op)"
  "e = make_edge
                     (next_id circuit)
                     (get_output_node_id q)
                     q"
        by auto

      then show
        "is_well_formed_edge ?updated_circuit e"
      proof cases
        case old_edge
          (* Since e belongs to the original circuit and all original
           edges are well formed, e is well formed before insertion. *)
        have edge_well_formed_before:
          "is_well_formed_edge circuit e"
          using old_edges_well_formed old_edge
          unfolding are_well_formed_edges_def
          by simp

(* A well-formed old edge has an existing source node.
           Since next_id was unused, the source cannot equal next_id. *)
        have source_not_next_id:
          "edge_source e \<noteq> next_id circuit"
        proof
          assume source_is_next:
            "edge_source e = next_id circuit"

          from edge_well_formed_before have source_exists:
            "node_exists circuit (edge_source e)"
            unfolding is_well_formed_edge_def
            by simp

          from source_exists have
            "nodes circuit (edge_source e) \<noteq> None"
            unfolding node_exists_def
            by simp

          with source_is_next next_id_unused show False
            unfolding next_id_is_unused_def
            by simp
        qed

(* The same argument applies to the target endpoint. *)
        have target_not_next_id:
          "edge_target e \<noteq> next_id circuit"
        proof
          assume target_is_next:
            "edge_target e = next_id circuit"

          from edge_well_formed_before have target_exists:
            "node_exists circuit (edge_target e)"
            unfolding is_well_formed_edge_def
            by simp

          from target_exists have
            "nodes circuit (edge_target e) \<noteq> None"
            unfolding node_exists_def
            by simp

          with target_is_next next_id_unused show False
            unfolding next_id_is_unused_def
            by simp
        qed

(* insert_operation changes the node table only at next_id.
           Since neither endpoint equals next_id, both endpoint lookups
           remain exactly as they were in the original circuit. *)
        have source_lookup_unchanged:
          "nodes ?updated_circuit (edge_source e)
           =
           nodes circuit (edge_source e)"
          using source_not_next_id
          unfolding insert_operation_def Let_def
          by simp

        have target_lookup_unchanged:
          "nodes ?updated_circuit (edge_target e)
           =
           nodes circuit (edge_target e)"
          using target_not_next_id
          unfolding insert_operation_def Let_def
          by simp

(* is_well_formed_edge depends only on endpoint existence,
           endpoint node lookups, the edge wire, and num_qubits.
           All of those are unchanged for this old edge. *)
        show ?thesis
          using
            edge_well_formed_before
            source_lookup_unchanged
            target_lookup_unchanged
          unfolding
            is_well_formed_edge_def
            node_exists_def
            qubit_in_circuit_def
          by simp
      next
        case (new_input_edge q)
          (* The wire q is one of the qubits used by the inserted
           operation. *)
        have q_in_operation:
          "q \<in> set (op_qargs op)"
          using new_input_edge(1) .

(* Since op is valid for the original circuit, every wire used
           by op belongs to that circuit. *)
        have q_valid_before:
          "qubit_in_circuit circuit q"
          using operation_valid_for_circuit q_in_operation
          unfolding operation_in_circuit_def
          by simp

(* Frontier validity gives us the concrete node currently at
           frontier q, together with the fact that it lies on wire q. *)
        from valid_frontier q_valid_before
        obtain frontier_node where
          frontier_node_lookup:
          "nodes circuit (frontier q) = Some frontier_node"
          and frontier_node_uses_q:
          "node_uses_qubit frontier_node q"
          and old_frontier_edge:
          "make_edge
               (frontier q)
               (get_output_node_id q)
               q
             \<in> edges circuit"
          unfolding is_valid_frontier_def
          by auto

(* The frontier node cannot be next_id because next_id was
           unused in the original circuit. Therefore, inserting the
           operation node does not overwrite the frontier node. *)
        have frontier_id_not_next_id:
          "frontier q \<noteq> next_id circuit"
        proof
          assume same_id:
            "frontier q = next_id circuit"

          from frontier_node_lookup have
            "nodes circuit (next_id circuit) = Some frontier_node"
            using same_id
            by simp

          with next_id_unused show False
            unfolding next_id_is_unused_def
            by simp
        qed

(* Wire splicing and the final next_id update do not alter the
           node table. Hence the frontier node remains stored at the
           same ID in the final circuit. *)
        have frontier_node_lookup_after:
          "nodes ?updated_circuit (frontier q) =
           Some frontier_node"
          using frontier_node_lookup frontier_id_not_next_id
          unfolding insert_operation_def Let_def
          by simp

(* The newly allocated node ID stores exactly the inserted
           operation node in the final circuit. *)
        have inserted_node_lookup:
          "nodes ?updated_circuit (next_id circuit) =
           Some (OperationNode op)"
          using insert_operation_new_node .

(* insert_operation preserves num_qubits, so q remains valid
           in the updated circuit. *)
        have q_valid_after:
          "qubit_in_circuit ?updated_circuit q"
          using q_valid_before
          unfolding qubit_in_circuit_def
          by simp

(* OperationNode op uses every qubit listed in op_qargs op. *)
        have inserted_node_uses_q:
          "node_uses_qubit (OperationNode op) q"
          using q_in_operation
          by simp

(* Substitute the concrete form of e and discharge each
           well-formedness condition using the facts above. *)
        show ?thesis
          using
            new_input_edge(2)
            frontier_node_lookup_after
            frontier_node_uses_q
            inserted_node_lookup
            inserted_node_uses_q
            q_valid_after
          unfolding
            is_well_formed_edge_def
            node_exists_def
            make_edge_def
          by simp

      next
        case (new_output_edge q)
          (* The wire q is one of the qubits used by the inserted
           operation. *)
        have q_in_operation:
          "q \<in> set (op_qargs op)"
          using new_output_edge(1) .

(* Since op is valid for the original circuit, every wire used
           by op belongs to that circuit. *)
        have q_valid_before:
          "qubit_in_circuit circuit q"
          using operation_valid_for_circuit q_in_operation
          unfolding operation_in_circuit_def
          by simp

(* insert_operation preserves num_qubits, so q remains a valid
           circuit wire after insertion. *)
        have q_valid_after:
          "qubit_in_circuit ?updated_circuit q"
          using q_valid_before
          unfolding qubit_in_circuit_def
          by simp

(* The old next_id now stores exactly the inserted operation
           node in the updated circuit. *)
        have inserted_node_lookup:
          "nodes ?updated_circuit (next_id circuit) =
           Some (OperationNode op)"
          using insert_operation_new_node .

(* OperationNode op uses every qubit listed in op_qargs op. *)
        have inserted_node_uses_q:
          "node_uses_qubit (OperationNode op) q"
          using q_in_operation
          by simp

(* The previously proved boundary-node invariant guarantees that
           the output node of q exists in the updated circuit. *)
        have output_node_lookup:
          "nodes ?updated_circuit (get_output_node_id q) =
           Some (OutputNode q)"
        proof -
          obtain qubit_number where q_form:
            "q = Qubit qubit_number"
            by (cases q)

          from q_valid_after have qubit_number_valid:
            "qubit_number < num_qubits ?updated_circuit"
            using q_form
            unfolding qubit_in_circuit_def
            by simp

          from boundary_nodes qubit_number_valid show ?thesis
            using q_form
            unfolding are_well_formed_boundary_nodes_def
            by simp
        qed

(* An output node for q lies on wire q by definition. *)
        have output_node_uses_q:
          "node_uses_qubit (OutputNode q) q"
          by simp

(* Substitute the concrete form of e and discharge all five
           edge well-formedness conditions using the facts above. *)
        show ?thesis
          using
            new_output_edge(2)
            inserted_node_lookup
            inserted_node_uses_q
            output_node_lookup
            output_node_uses_q
            q_valid_after
          unfolding
            is_well_formed_edge_def
            node_exists_def
            make_edge_def
          by simp
      qed
    qed
  qed

  have operation_nodes:
    "are_well_formed_operation_nodes ?updated_circuit"

  proof -
    (* Extract the fact that every operation node already present in the original circuit contains an operation valid for that circuit. *)
    have old_operation_nodes:
      "are_well_formed_operation_nodes circuit"
      using circuit_well_formed
      unfolding is_well_formed_circuit_def
      by simp

(* Unfold the universal condition defining well-formed operation nodes in the updated circuit. *)
    show ?thesis
      unfolding are_well_formed_operation_nodes_def

    proof (intro allI impI)
      (* Select an arbitrary node ID and arbitrary operation stored
         at that ID in the updated circuit. *)
      fix node_id existing_op

      assume updated_node_lookup:
        "nodes ?updated_circuit node_id =
         Some (OperationNode existing_op)"

(* Split according to whether this is the newly allocated node ID
         or an operation node that existed before insertion. *)
      show
        "operation_in_circuit ?updated_circuit existing_op"

      proof (cases "node_id = next_id circuit")
        case True

(* At the old next_id, insert_operation stores exactly the
           operation supplied to insert_operation. *)
        have inserted_node_lookup:
          "nodes ?updated_circuit (next_id circuit) =
           Some (OperationNode op)"
          using insert_operation_new_node .

(* The arbitrary operation existing_op found at this ID must
           therefore be the newly inserted operation op. *)
        have existing_op_is_inserted_op:
          "existing_op = op"
          using
            updated_node_lookup
            inserted_node_lookup
            True
          by simp

(* The assumption says that op is valid for the original circuit.
           Since insertion does not alter num_qubits, the valid qubit set
           is unchanged, so op is also valid for the updated circuit. *)
        have inserted_operation_valid_after:
          "operation_in_circuit ?updated_circuit op"
          using operation_valid_for_circuit
          unfolding operation_in_circuit_def
            qubit_in_circuit_def
          by simp

(* Replace existing_op by op and use the validity fact above. *)
        show ?thesis
          using
            existing_op_is_inserted_op
            inserted_operation_valid_after
          by simp

      next
        case False

(* Since node_id is not the allocated insertion ID, insert_node
           does not change its node-table entry. Wire splicing changes
           only edges, and updating next_id changes only next_id.
           Therefore, this same operation node existed before insertion. *)
        have old_node_lookup:
          "nodes circuit node_id =
           Some (OperationNode existing_op)"
          using updated_node_lookup False
          unfolding insert_operation_def Let_def
          by simp

(* The original circuit was well formed, so the operation stored
           at this old node ID was valid for the original circuit. *)
        have old_operation_valid:
          "operation_in_circuit circuit existing_op"
          using old_operation_nodes old_node_lookup
          unfolding are_well_formed_operation_nodes_def
          by blast

(* operation_in_circuit depends on the operation's validity and
           whether its qubits lie below num_qubits. Since insertion
           preserves num_qubits, validity transfers to the updated circuit. *)
        show ?thesis
          using old_operation_valid
          unfolding operation_in_circuit_def
            qubit_in_circuit_def
          by simp
      qed
    qed
  qed

  show ?thesis
    unfolding is_well_formed_circuit_def
    using boundary_nodes well_formed_edges operation_nodes
    by simp
qed

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

proof -
  let ?updated_circuit = "fst (insert_operation circuit frontier op)"
  let ?updated_frontier = "snd (insert_operation circuit frontier op)"

  have updated_circuit_is_well_formed:
    "is_well_formed_circuit ?updated_circuit"
    using insert_operation_preserves_well_formed_circuit
      is_valid_construction_state_def valid_operation
      valid_state
    by simp 

  have updated_frontier_is_valid:
    "is_valid_frontier ?updated_circuit ?updated_frontier"
    using insert_operation_preserves_valid_frontier
      is_valid_construction_state_def
      operation_in_circuit_def
      valid_operation valid_state
    by simp

  have all_existing_node_ids_of_updated_circuit_are_below_next_id:
    "all_existing_node_ids_below_next_id ?updated_circuit"
    using insert_operation_preserves_node_id_allocation
      is_valid_construction_state_def
      valid_state
    by simp

  have next_id_of_updated_circuit_is_unused:
    "next_id_is_unused ?updated_circuit"
    using all_existing_node_ids_below_next_id_def
      all_existing_node_ids_of_updated_circuit_are_below_next_id
      next_id_is_unused_def
    by auto

  show ?thesis
    using
      updated_circuit_is_well_formed
      updated_frontier_is_valid
      next_id_of_updated_circuit_is_unused
      all_existing_node_ids_of_updated_circuit_are_below_next_id
    unfolding is_valid_construction_state_def
    by simp
qed

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

proof -
  have comparable:
    "nodes_comparable_on_wire circuit q"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  from frontier_valid q_valid
  obtain frontier_node where
    frontier_lookup:
    "nodes circuit (frontier q) = Some frontier_node"
    and frontier_uses_q:
    "node_uses_qubit frontier_node q"
    and frontier_output_edge:
    "make_edge
         (frontier q)
         (get_output_node_id q)
         q
       \<in> edges circuit"
    unfolding is_valid_frontier_def
    by blast

  have frontier_reaches_output:
    "wire_reaches
       circuit q
       (frontier q)
       (get_output_node_id q)"
    unfolding
      wire_reaches_def
      wire_edge_relation_def
    using frontier_output_edge
    by (simp add: r_into_trancl)

  from comparable
    node_lookup
    frontier_lookup
    node_uses_q
    frontier_uses_q
  have ordering:
    "node_id = frontier q
     \<or> wire_reaches circuit q node_id (frontier q)
     \<or> wire_reaches circuit q (frontier q) node_id"
    unfolding nodes_comparable_on_wire_def
    by simp

  from ordering consider
    (same)
    "node_id = frontier q"
    | (before)
      "wire_reaches circuit q node_id (frontier q)"
    | (after)
      "wire_reaches circuit q (frontier q) node_id"
    by blast

  then show ?thesis
  proof cases
    case same

    then show ?thesis
      by simp

  next
    case before

    then show ?thesis
      by simp

  next
    case after

    have output_has_no_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
      using linear_before
      unfolding wire_is_linear_def
      by simp

    have frontier_output_relation:
      "(frontier q, get_output_node_id q)
         \<in> wire_edge_relation circuit q"
      using frontier_output_edge
      unfolding wire_edge_relation_def
      by simp

    have frontier_successor_is_output:
      "\<And>successor_id.
         (frontier q, successor_id)
           \<in> wire_edge_relation circuit q
         \<Longrightarrow> successor_id = get_output_node_id q"
      using
        frontier_unique_successor
        frontier_output_relation
      unfolding has_unique_wire_successor_def
      by auto

    have frontier_reaches_only_output:
      "\<And>target_id.
         wire_reaches circuit q (frontier q) target_id
         \<Longrightarrow> target_id = get_output_node_id q"
    proof -
      fix target_id

      assume reaches_target:
        "wire_reaches circuit q (frontier q) target_id"

      then have path:
        "(frontier q, target_id)
           \<in> (wire_edge_relation circuit q)\<^sup>+"
        unfolding wire_reaches_def
        .

      then show
        "target_id = get_output_node_id q"
      proof (induction rule: trancl_induct)
        case base

        then show ?case
          using frontier_successor_is_output
          by blast

      next
        case (step intermediate_id final_id)

        from step.IH have intermediate_is_output:
          "intermediate_id = get_output_node_id q"
          .

        from step.hyps have
          "(intermediate_id, final_id)
             \<in> wire_edge_relation circuit q"
          by simp

        then have
          "(get_output_node_id q, final_id)
             \<in> wire_edge_relation circuit q"
          using intermediate_is_output
          by simp

        with output_has_no_successor show ?case
          by blast
      qed
    qed

    have node_is_output:
      "node_id = get_output_node_id q"
      using after
      by (rule frontier_reaches_only_output)

    then show ?thesis
      by simp
  qed
qed

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

proof -
  let ?old_relation =
    "wire_edge_relation circuit q"

  let ?new_relation =
    "wire_edge_relation updated_circuit q"

  have every_old_edge_has_new_path:
    "\<And>source_id target_id.
       (source_id, target_id) \<in> ?old_relation
       \<Longrightarrow>
       (source_id, target_id) \<in> ?new_relation\<^sup>+"
  proof -
    fix source_id target_id

    assume old_edge:
      "(source_id, target_id) \<in> ?old_relation"

    show
      "(source_id, target_id) \<in> ?new_relation\<^sup>+"
    proof (
        cases
        "(source_id, target_id) =
         (frontier q, get_output_node_id q)"
        )
      case True

      have frontier_to_new:
        "(frontier q, new_node_id) \<in> ?new_relation"
        using relation_after
        by simp

      have new_to_output:
        "(new_node_id, get_output_node_id q) \<in> ?new_relation"
        using relation_after
        by simp

      have frontier_reaches_new:
        "(frontier q, new_node_id) \<in> ?new_relation\<^sup>+"
        using frontier_to_new
        by (rule r_into_trancl)

      have frontier_reaches_output:
        "(frontier q, get_output_node_id q)
          \<in> ?new_relation\<^sup>+"
        using frontier_reaches_new new_to_output
        by (rule trancl_into_trancl)

      show ?thesis
        using True frontier_reaches_output
        by simp

    next
      case False

      have edge_still_exists:
        "(source_id, target_id) \<in> ?new_relation"
        using
          old_edge
          False
          relation_after
        by auto

      then show ?thesis
        by (rule r_into_trancl)
    qed
  qed

  from old_reachability have old_path:
    "(node_a, node_b) \<in> ?old_relation\<^sup>+"
    unfolding wire_reaches_def
    .

  have new_path:
    "(node_a, node_b) \<in> ?new_relation\<^sup>+"
    using old_path
  proof (induction rule: trancl_induct)
    case base

    then show ?case
      using every_old_edge_has_new_path
      by blast

  next
    case step

    then show ?case
      using
        every_old_edge_has_new_path
        trancl_trans
      by metis
  qed

  show ?thesis
    using new_path
    unfolding wire_reaches_def
    .
qed

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

proof -
  have frontier_to_new_edge:
    "(frontier q, new_node_id)
       \<in> wire_edge_relation updated_circuit q"
    using relation_after
    by simp

  have new_to_output_edge:
    "(new_node_id, get_output_node_id q)
       \<in> wire_edge_relation updated_circuit q"
    using relation_after
    by simp

  have frontier_reaches_new:
    "wire_reaches updated_circuit q (frontier q) new_node_id"
    unfolding wire_reaches_def
    using frontier_to_new_edge
    by (rule r_into_trancl)

  have new_reaches_output:
    "wire_reaches
       updated_circuit q
       new_node_id
       (get_output_node_id q)"
    unfolding wire_reaches_def
    using new_to_output_edge
    by (rule r_into_trancl)

  show ?thesis
    unfolding nodes_comparable_on_wire_def
  proof (intro allI impI)
    fix node_a node_b node_a_value node_b_value

    assume node_a_lookup_after:
      "nodes updated_circuit node_a = Some node_a_value"

    assume node_b_lookup_after:
      "nodes updated_circuit node_b = Some node_b_value"

    assume node_a_uses_q:
      "node_uses_qubit node_a_value q"

    assume node_b_uses_q:
      "node_uses_qubit node_b_value q"

    show
      "node_a = node_b
       \<or> wire_reaches updated_circuit q node_a node_b
       \<or> wire_reaches updated_circuit q node_b node_a"
    proof (cases "node_a = new_node_id")
      case True

      have node_a_value_is_new:
        "node_a_value = new_node"
        using
          node_a_lookup_after
          new_node_exists_after
          True
        by simp

      show ?thesis
      proof (cases "node_b = new_node_id")
        case True

        then show ?thesis
          using \<open>node_a = new_node_id\<close>
          by simp

      next
        case False

        have node_b_not_new:
          "node_b \<noteq> new_node_id"
          using False .

        have node_b_lookup_before:
          "nodes circuit node_b = Some node_b_value"
          using
            node_b_lookup_after
            old_nodes_unchanged[OF False]
          by simp

        have node_b_position:
          "node_b = get_output_node_id q
           \<or> node_b = frontier q
           \<or> wire_reaches circuit q node_b (frontier q)"
          using
            linear_before
            frontier_valid
            q_valid
            node_b_lookup_before
            node_b_uses_q
            valid_frontier_has_unique_successor
            wire_node_reaches_frontier_or_is_output
          by simp

        from node_b_position consider
          (output_node_b)
          "node_b = get_output_node_id q"
          | (frontier)
            "node_b = frontier q"
          | (before_frontier)
            "wire_reaches circuit q node_b (frontier q)"
          by auto

        then show ?thesis
        proof cases
          case output_node_b

          have
            "wire_reaches updated_circuit q node_a node_b"
            using
              True
              output_node_b
              new_reaches_output
            by simp

          then show ?thesis
            by simp

        next
          case frontier

          have
            "wire_reaches updated_circuit q node_b node_a"
            using
              True
              frontier
              frontier_reaches_new
            by simp

          then show ?thesis
            by blast

        next
          case before_frontier

          have node_b_reaches_frontier_after:
            "wire_reaches
               updated_circuit q
               node_b
               (frontier q)"
            using
              before_frontier
              relation_after
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          have node_b_reaches_new:
            "wire_reaches
               updated_circuit q
               node_b
               new_node_id"
          proof -
            have old_path:
              "(node_b, frontier q)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using node_b_reaches_frontier_after
              unfolding wire_reaches_def
              by simp

            have
              "(node_b, new_node_id)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using old_path frontier_to_new_edge
              by (rule trancl_into_trancl)

            then show ?thesis
              unfolding wire_reaches_def
              .
          qed

          have
            "wire_reaches updated_circuit q node_b node_a"
            using True node_b_reaches_new
            by simp

          then show ?thesis
            by simp
        qed
      qed

    next
      case False

      have node_a_not_new:
        "node_a \<noteq> new_node_id"
        using False .

      have node_a_lookup_before:
        "nodes circuit node_a = Some node_a_value"
        using
          node_a_lookup_after
          old_nodes_unchanged[OF False]
        by simp

      show ?thesis
      proof (cases "node_b = new_node_id")
        case True

        have node_b_value_is_new:
          "node_b_value = new_node"
          using
            node_b_lookup_after
            new_node_exists_after
            True
          by simp

        have node_a_position:
          "node_a = get_output_node_id q
           \<or> node_a = frontier q
           \<or> wire_reaches circuit q node_a (frontier q)"
          using
            linear_before
            frontier_valid
            q_valid
            node_a_lookup_before
            node_a_uses_q
            valid_frontier_has_unique_successor
            wire_node_reaches_frontier_or_is_output
          by simp

        from node_a_position consider
          (output_node_a)
          "node_a = get_output_node_id q"
          | (frontier)
            "node_a = frontier q"
          | (before_frontier)
            "wire_reaches circuit q node_a (frontier q)"
          by auto

        then show ?thesis
        proof cases
          case output_node_a

          have
            "wire_reaches updated_circuit q node_b node_a"
            using
              True
              output_node_a
              new_reaches_output
            by simp

          then show ?thesis
            by simp

        next
          case frontier

          have
            "wire_reaches updated_circuit q node_a node_b"
            using
              True
              frontier
              frontier_reaches_new
            by simp

          then show ?thesis
            by simp

        next
          case before_frontier

          have node_a_reaches_frontier_after:
            "wire_reaches
               updated_circuit q
               node_a
               (frontier q)"
            using
              before_frontier
              relation_after
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          have node_a_reaches_new:
            "wire_reaches
               updated_circuit q
               node_a
               new_node_id"
          proof -
            have old_path:
              "(node_a, frontier q)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using node_a_reaches_frontier_after
              unfolding wire_reaches_def
              .

            have
              "(node_a, new_node_id)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using old_path frontier_to_new_edge
              by (rule trancl_into_trancl)

            then show ?thesis
              unfolding wire_reaches_def
              .
          qed

          have
            "wire_reaches updated_circuit q node_a node_b"
            using True node_a_reaches_new
            by simp

          then show ?thesis
            by blast
        qed

      next
        case False

        have node_b_lookup_before:
          "nodes circuit node_b = Some node_b_value"
          using
            node_b_lookup_after
            old_nodes_unchanged[OF False]
          by simp

        from comparable_before
          node_a_lookup_before
          node_b_lookup_before
          node_a_uses_q
          node_b_uses_q
        have old_comparability:
          "node_a = node_b
           \<or> wire_reaches circuit q node_a node_b
           \<or> wire_reaches circuit q node_b node_a"
          unfolding nodes_comparable_on_wire_def
          by blast

        from old_comparability consider
          (same)
          "node_a = node_b"
          | (a_before_b)
            "wire_reaches circuit q node_a node_b"
          | (b_before_a)
            "wire_reaches circuit q node_b node_a"
          by auto

        then show ?thesis
        proof cases
          case same

          then show ?thesis
            by simp

        next
          case a_before_b

          have
            "wire_reaches updated_circuit q node_a node_b"
            using
              a_before_b
              relation_after
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          then show ?thesis
            by simp

        next
          case b_before_a

          have
            "wire_reaches updated_circuit q node_b node_a"
            using
              b_before_a
              relation_after
            using
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          then show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed

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

proof -
  have input_node_has_no_predecessor:
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation circuit q)
     \<and>
     has_unique_wire_successor
       circuit q (get_input_node_id q)"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have output_not_input:
    (* The canonical output and input IDs of the same wire are distinct. *)
    "get_output_node_id q \<noteq> get_input_node_id q"
    using
      get_output_node_id_def
      get_input_node_id_def
    by simp

  show ?thesis
  proof (cases "frontier q = get_input_node_id q")
    case True

    have no_input_predecessor_after:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation updated_circuit q"

    proof
      assume
        "\<exists>predecessor_id.
           (predecessor_id, get_input_node_id q)
             \<in> wire_edge_relation updated_circuit q"

      then obtain predecessor_id where predecessor_edge_after:
        "(predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation updated_circuit q"
        by auto

      from predecessor_edge_after relation_after have
        "(predecessor_id, get_input_node_id q)
          =
          (new_node_id, get_output_node_id q)
       \<or>
        (predecessor_id, get_input_node_id q)
          =
          (frontier q, new_node_id)
       \<or>
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation circuit q -
             {(frontier q, get_output_node_id q)}"
        by simp

      have no_input_predecessor_before:
        "\<nexists>predecessor_id.
           (predecessor_id, get_input_node_id q)
             \<in> wire_edge_relation circuit q"
        using input_node_has_no_predecessor
        by simp

      from
        \<open>(predecessor_id, get_input_node_id q)
            =
            (new_node_id, get_output_node_id q)
         \<or>
          (predecessor_id, get_input_node_id q)
            =
            (frontier q, new_node_id)
         \<or>
          (predecessor_id, get_input_node_id q)
            \<in> wire_edge_relation circuit q -
               {(frontier q, get_output_node_id q)}\<close>
      show False
        using
          output_not_input
          new_node_not_input
          no_input_predecessor_before
        by auto
    qed

    have unique_input_successor_before:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
      using input_node_has_no_predecessor
      by simp

    have old_frontier_output_edge:
      "(frontier q, get_output_node_id q)
        \<in> wire_edge_relation circuit q"
      using valid_frontier_before q_valid
      unfolding
        is_valid_frontier_def
        wire_edge_relation_def
      by auto

    have old_input_output_edge:
      "(get_input_node_id q, get_output_node_id q)
        \<in> wire_edge_relation circuit q"
      using old_frontier_output_edge True
      by simp

    have old_input_successor_is_output:
      "\<And>successor_id.
         (get_input_node_id q, successor_id)
           \<in> wire_edge_relation circuit q
         \<Longrightarrow> successor_id = get_output_node_id q"
      using
        unique_input_successor_before
        old_input_output_edge
      unfolding has_unique_wire_successor_def
      by auto

    have unique_input_successor_after:
      "has_unique_wire_successor
         updated_circuit q (get_input_node_id q)"
      unfolding has_unique_wire_successor_def
    proof (rule ex1I[of _ new_node_id])

      show
        "(get_input_node_id q, new_node_id)
          \<in> wire_edge_relation updated_circuit q"
        using relation_after True
        by simp

    next
      fix successor_id

      assume successor_edge_after:
        "(get_input_node_id q, successor_id)
          \<in> wire_edge_relation updated_circuit q"

      from
        successor_edge_after
        relation_after
      have successor_cases:
        "(get_input_node_id q, successor_id)
            =
            (new_node_id, get_output_node_id q)
         \<or>
          (get_input_node_id q, successor_id)
            =
            (frontier q, new_node_id)
         \<or>
          (get_input_node_id q, successor_id)
            \<in> wire_edge_relation circuit q -
               {(frontier q, get_output_node_id q)}"
        by simp

      from successor_cases consider
        (first)
        "(get_input_node_id q, successor_id)
             =
           (new_node_id, get_output_node_id q)"
        | (second)
          "(get_input_node_id q, successor_id)
             =
           (frontier q, new_node_id)"
        | (third)
          "(get_input_node_id q, successor_id)
             \<in> wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}"
        by auto

      then show "successor_id = new_node_id"
      proof cases
        case first

        from first have
          "get_input_node_id q = new_node_id"
          by simp

        with new_node_not_input show ?thesis
          by simp

      next
        case second

        then show ?thesis
          using True
          by simp

      next
        case third

        from third have old_edge:
          "(get_input_node_id q, successor_id)
             \<in> wire_edge_relation circuit q"
          by simp

        from old_input_successor_is_output[OF old_edge]
        have successor_is_output:
          "successor_id = get_output_node_id q"
          .

        from third have edge_not_removed:
          "(get_input_node_id q, successor_id)
             \<noteq>
           (frontier q, get_output_node_id q)"
          by simp

        show ?thesis
          using
            edge_not_removed
            True
            successor_is_output
          by simp
      qed
    qed

    show ?thesis
      using
        no_input_predecessor_after
        unique_input_successor_after
      by simp

  next
    case False

    have input_predecessor_edges_unchanged:
      (* Since neither newly inserted edge targets the input node, and the removed edge targets the output node, subdivision does not alter any edge entering the input node. *)
      "((predecessor_id, get_input_node_id q) \<in> wire_edge_relation updated_circuit q)
       \<longleftrightarrow>
        ((predecessor_id, get_input_node_id q) \<in> wire_edge_relation circuit q)"
      for predecessor_id
      using
        relation_after
        output_not_input
        new_node_not_input
      by simp

    have no_input_predecessor_after:
      "\<nexists>predecessor_id.
     (predecessor_id, get_input_node_id q)
       \<in> wire_edge_relation updated_circuit q"
    proof
      assume predecessor_exists_after:
        "\<exists>predecessor_id.
       (predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation updated_circuit q"

      then obtain predecessor_id where predecessor_after:
        "(predecessor_id, get_input_node_id q)
      \<in> wire_edge_relation updated_circuit q"
        by blast

      from input_predecessor_edges_unchanged predecessor_after have
        "(predecessor_id, get_input_node_id q)
      \<in> wire_edge_relation circuit q"
        by blast

      moreover from input_node_has_no_predecessor have
        "\<nexists>predecessor_id.
       (predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
        by simp

      ultimately show False
        by blast
    qed

    have input_successor_edges_unchanged:
      (* Because the frontier is not the input node, the removed edge is not
     an outgoing input edge. Neither inserted edge has the input node as
     its source, because both frontier and new_node_id differ from the
     input node. *)
      "((get_input_node_id q, successor_id)
      \<in> wire_edge_relation updated_circuit q)
   \<longleftrightarrow>
   ((get_input_node_id q, successor_id)
      \<in> wire_edge_relation circuit q)"
      for successor_id
      using
        relation_after
        False
        new_node_not_input
      by auto

    have unique_input_successor_after:
      "has_unique_wire_successor
     updated_circuit q (get_input_node_id q)"
    proof -
      from input_node_has_no_predecessor have unique_before:
        "has_unique_wire_successor
       circuit q (get_input_node_id q)"
        by simp

      show ?thesis
        using unique_before input_successor_edges_unchanged
        unfolding has_unique_wire_successor_def
        by blast
    qed

    show ?thesis
      using
        no_input_predecessor_after
        unique_input_successor_after
      by simp

  qed
qed

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

proof -
  have no_output_successor_before:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have frontier_output_edge_before:
    "(frontier q, get_output_node_id q)
       \<in> wire_edge_relation circuit q"
    using valid_frontier_before q_valid
    unfolding
      is_valid_frontier_def
      wire_edge_relation_def
    by auto

  have frontier_not_output:
    "frontier q \<noteq> get_output_node_id q"
  proof
    assume frontier_is_output:
      "frontier q = get_output_node_id q"

    from frontier_output_edge_before frontier_is_output have
      "(get_output_node_id q, get_output_node_id q)
         \<in> wire_edge_relation circuit q"
      by simp

    with no_output_successor_before show False
      by blast
  qed

  show ?thesis
    using
      relation_after
      no_output_successor_before
      new_node_not_output
      frontier_not_output
    by auto
qed

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

proof -
  have unique_output_predecessor_before:
    "has_unique_wire_predecessor
       circuit q (get_output_node_id q)"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have frontier_output_edge_before:
    "(frontier q, get_output_node_id q)
       \<in> wire_edge_relation circuit q"
    using valid_frontier_before q_valid
    unfolding
      is_valid_frontier_def
      wire_edge_relation_def
    by auto

  have old_output_predecessor_is_frontier:
    "\<And>predecessor_id.
       (predecessor_id, get_output_node_id q)
         \<in> wire_edge_relation circuit q
       \<Longrightarrow> predecessor_id = frontier q"
    using
      unique_output_predecessor_before
      frontier_output_edge_before
    unfolding has_unique_wire_predecessor_def
    by blast

  show ?thesis
    unfolding has_unique_wire_predecessor_def
  proof (rule ex1I[of _ new_node_id])

    show
      "(new_node_id, get_output_node_id q)
         \<in> wire_edge_relation updated_circuit q"
      using relation_after
      by simp

  next
    fix predecessor_id

    assume predecessor_edge_after:
      "(predecessor_id, get_output_node_id q)
         \<in> wire_edge_relation updated_circuit q"

    from predecessor_edge_after relation_after have predecessor_cases:
      "(predecessor_id, get_output_node_id q)
          =
        (new_node_id, get_output_node_id q)
       \<or>
       (predecessor_id, get_output_node_id q)
          =
        (frontier q, new_node_id)
       \<or>
       (predecessor_id, get_output_node_id q)
          \<in> wire_edge_relation circuit q -
             {(frontier q, get_output_node_id q)}"
      by auto

    from predecessor_cases consider
      (new_edge)
      "(predecessor_id, get_output_node_id q)
             =
           (new_node_id, get_output_node_id q)"
      | (frontier_new_edge)
        "(predecessor_id, get_output_node_id q)
             =
           (frontier q, new_node_id)"
      | (old_edge)
        "(predecessor_id, get_output_node_id q)
             \<in> wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}"
      by blast

    then show "predecessor_id = new_node_id"
    proof cases
      case new_edge

      then show ?thesis
        by simp

    next
      case frontier_new_edge

      from frontier_new_edge have
        "get_output_node_id q = new_node_id"
        by simp

      with new_node_not_output show ?thesis
        by simp

    next
      case old_edge

      from old_edge have old_output_edge:
        "(predecessor_id, get_output_node_id q)
           \<in> wire_edge_relation circuit q"
        by simp

      from old_output_predecessor_is_frontier[OF old_output_edge]
      have predecessor_is_frontier:
        "predecessor_id = frontier q"
        .

      from old_edge have edge_not_removed:
        "(predecessor_id, get_output_node_id q)
           \<noteq>
         (frontier q, get_output_node_id q)"
        by simp

      from edge_not_removed predecessor_is_frontier
      show ?thesis
        by simp
    qed
  qed
qed

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

proof -
  have old_operation_degrees:
    "\<forall>node_id stored_op.
       nodes circuit node_id = Some (OperationNode stored_op)
       \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
       \<longrightarrow> has_unique_wire_predecessor circuit q node_id
         \<and> has_unique_wire_successor circuit q node_id"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have old_output_has_no_successor:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have old_edges_well_formed:
    "are_well_formed_edges circuit"
    using circuit_well_formed
    unfolding is_well_formed_circuit_def
    by simp

  have no_old_edge_to_new_node:
    "\<And>source_id.
       (source_id, new_node_id)
         \<notin> wire_edge_relation circuit q"
  proof
    fix source_id

    assume old_edge:
      "(source_id, new_node_id)
        \<in> wire_edge_relation circuit q"

    then have edge_in:
      "make_edge source_id new_node_id q
        \<in> edges circuit"
      unfolding wire_edge_relation_def
      by simp

    from old_edges_well_formed edge_in have
      "node_exists circuit new_node_id"
      unfolding
        are_well_formed_edges_def
        is_well_formed_edge_def
        make_edge_def
      by auto

    then have
      "nodes circuit new_node_id \<noteq> None"
      unfolding node_exists_def
      .

    with new_node_unused_before show False
      by simp
  qed

  have no_old_edge_from_new_node:
    "\<And>target_id.
       (new_node_id, target_id)
         \<notin> wire_edge_relation circuit q"
  proof
    fix target_id

    assume old_edge:
      "(new_node_id, target_id)
        \<in> wire_edge_relation circuit q"

    then have edge_in:
      "make_edge new_node_id target_id q
        \<in> edges circuit"
      unfolding wire_edge_relation_def
      by simp

    from old_edges_well_formed edge_in have
      "node_exists circuit new_node_id"
      unfolding
        are_well_formed_edges_def
        is_well_formed_edge_def
        make_edge_def
      by auto

    then have
      "nodes circuit new_node_id \<noteq> None"
      unfolding node_exists_def
      .

    with new_node_unused_before show False
      by simp
  qed

  have old_frontier_output_edge:
    "(frontier q, get_output_node_id q)
      \<in> wire_edge_relation circuit q"
    using valid_frontier_before q_valid
    unfolding
      is_valid_frontier_def
      wire_edge_relation_def
    by auto

  have frontier_not_new:
    "frontier q \<noteq> new_node_id"
  proof
    assume
      "frontier q = new_node_id"

    with old_frontier_output_edge have
      "(new_node_id, get_output_node_id q)
        \<in> wire_edge_relation circuit q"
      by simp

    with no_old_edge_from_new_node show False
      by blast
  qed

  have output_not_new:
    "get_output_node_id q \<noteq> new_node_id"
  proof
    assume
      "get_output_node_id q = new_node_id"

    with old_frontier_output_edge have
      "(frontier q, new_node_id)
        \<in> wire_edge_relation circuit q"
      by simp

    with no_old_edge_to_new_node show False
      by blast
  qed

  show ?thesis
  proof (intro allI impI)
    fix node_id stored_op

    assume operation_lookup_after:
      "nodes updated_circuit node_id =
       Some (OperationNode stored_op)"

    assume operation_uses_q:
      "node_uses_qubit (OperationNode stored_op) q"

    show
      "has_unique_wire_predecessor
         updated_circuit q node_id
       \<and>
       has_unique_wire_successor
         updated_circuit q node_id"
    proof (cases "node_id = new_node_id")
      case True

      have stored_op_is_new_op:
        "stored_op = new_op"
        using
          operation_lookup_after
          new_node_exists_after
          True
        by simp

      have unique_new_predecessor:
        "has_unique_wire_predecessor
           updated_circuit q new_node_id"
        unfolding has_unique_wire_predecessor_def
      proof (rule ex1I[of _ "frontier q"])
        show
          "(frontier q, new_node_id)
            \<in> wire_edge_relation updated_circuit q"
          using relation_after
          by simp

      next
        fix predecessor_id

        assume predecessor_edge:
          "(predecessor_id, new_node_id)
            \<in> wire_edge_relation updated_circuit q"

        from predecessor_edge relation_after show
          "predecessor_id = frontier q"
          using
            output_not_new
            no_old_edge_to_new_node
          by auto
      qed

      have unique_new_successor:
        "has_unique_wire_successor
           updated_circuit q new_node_id"
        unfolding has_unique_wire_successor_def
      proof (rule ex1I[of _ "get_output_node_id q"])
        show
          "(new_node_id, get_output_node_id q)
            \<in> wire_edge_relation updated_circuit q"
          using relation_after
          by simp

      next
        fix successor_id

        assume successor_edge:
          "(new_node_id, successor_id)
            \<in> wire_edge_relation updated_circuit q"

        from successor_edge relation_after show
          "successor_id = get_output_node_id q"
          using
            frontier_not_new
            no_old_edge_from_new_node
          by auto
      qed

      show ?thesis
        using
          True
          unique_new_predecessor
          unique_new_successor
        by simp

    next
      case False

      have operation_lookup_before:
        "nodes circuit node_id =
         Some (OperationNode stored_op)"
        using
          operation_lookup_after
          old_nodes_unchanged[OF False]
        by simp

      have old_degrees:
        "has_unique_wire_predecessor circuit q node_id
         \<and>
         has_unique_wire_successor circuit q node_id"
        using
          old_operation_degrees
          operation_lookup_before
          operation_uses_q
        by blast

      have node_not_output:
        "node_id \<noteq> get_output_node_id q"
      proof
        assume node_is_output:
          "node_id = get_output_node_id q"

        from old_degrees have
          "has_unique_wire_successor circuit q node_id"
          by simp

        then obtain successor_id where
          "(node_id, successor_id)
            \<in> wire_edge_relation circuit q"
          unfolding has_unique_wire_successor_def
          by blast

        with node_is_output old_output_has_no_successor
        show False
          by blast
      qed

      have predecessor_edges_unchanged:
        "\<And>predecessor_id.
           ((predecessor_id, node_id)
              \<in> wire_edge_relation updated_circuit q)
           \<longleftrightarrow>
           ((predecessor_id, node_id)
              \<in> wire_edge_relation circuit q)"
        using
          relation_after
          False
          node_not_output
        by auto

      have unique_predecessor_after:
        "has_unique_wire_predecessor
           updated_circuit q node_id"
        using
          old_degrees
          predecessor_edges_unchanged
        unfolding has_unique_wire_predecessor_def
        by blast

      have unique_successor_after:
        "has_unique_wire_successor
           updated_circuit q node_id"
      proof (cases "node_id = frontier q")
        case True

        have old_frontier_unique_successor:
          "has_unique_wire_successor
             circuit q (frontier q)"
          using old_degrees True
          by simp

        have old_frontier_successor_is_output:
          "\<And>successor_id.
             (frontier q, successor_id)
               \<in> wire_edge_relation circuit q
             \<Longrightarrow> successor_id = get_output_node_id q"
          using
            old_frontier_unique_successor
            old_frontier_output_edge
          unfolding has_unique_wire_successor_def
          by blast

        show ?thesis
          unfolding has_unique_wire_successor_def
        proof (rule ex1I[of _ new_node_id])
          show
            "(node_id, new_node_id)
              \<in> wire_edge_relation updated_circuit q"
            using relation_after True
            by simp

        next
          fix successor_id

          assume successor_edge:
            "(node_id, successor_id)
              \<in> wire_edge_relation updated_circuit q"

          from successor_edge relation_after True show
            "successor_id = new_node_id"
            using
              frontier_not_new
              no_old_edge_from_new_node
              old_frontier_successor_is_output
            by auto
        qed

      next
        case False

        have successor_edges_unchanged:
          "\<And>successor_id.
             ((node_id, successor_id)
                \<in> wire_edge_relation updated_circuit q)
             \<longleftrightarrow>
             ((node_id, successor_id)
                \<in> wire_edge_relation circuit q)"
          using
            relation_after
            False
            new_node_unused_before
            operation_lookup_before
          by auto

        show ?thesis
          using
            old_degrees
            successor_edges_unchanged
          unfolding has_unique_wire_successor_def
          by blast
      qed

      show ?thesis
        using
          unique_predecessor_after
          unique_successor_after
        by simp
    qed
  qed
qed

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

  unfolding all_wires_linear_def

proof -
  let ?updated_circuit = "fst (insert_operation circuit frontier op)"
    (* The circuit returned after inserting the new operation. *)

  show "\<forall>q. qubit_in_circuit ?updated_circuit q
        \<longrightarrow> wire_is_linear ?updated_circuit q"

  proof (intro allI impI)
    fix q
      (* Choose an arbitrary wire q. We must prove that it remains linear
       whenever it is valid in the updated circuit. *)

    assume q_is_valid_after_insertion:
      "qubit_in_circuit ?updated_circuit q"

    have q_is_valid_before_insertion:
      "qubit_in_circuit circuit q"
      using
        qubit_in_circuit_def
        q_is_valid_after_insertion
      by simp

    have q_is_linear_before_insertion:
      "wire_is_linear circuit q"
      using linear_before q_is_valid_before_insertion
      unfolding all_wires_linear_def
      by simp

    show "wire_is_linear ?updated_circuit q"
    proof (cases "q \<in> set (op_qargs op)")
      case True

      have distinct_operation_wires:
        "distinct (op_qargs op)"
        using operation_valid
        unfolding 
          operation_in_circuit_def
          is_valid_operation_def
        by simp

      have q_wire_relation_after:
        "wire_edge_relation ?updated_circuit q
       =
       insert
         (next_id circuit, get_output_node_id q)
         (insert
           (frontier q, next_id circuit)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

      proof -
        let ?new_node_id = "next_id circuit"

        let ?circuit_with_node =
          "insert_node
           ?new_node_id
           (OperationNode op)
           circuit"

        let ?spliced_result =
          "splice_wires
           ?circuit_with_node
           frontier
           (op_qargs op)
           ?new_node_id"

        obtain spliced_circuit updated_frontier where
          spliced_result:
          "?spliced_result =
           (spliced_circuit, updated_frontier)"
          by (cases ?spliced_result)

        have relation_after_splicing:
          "wire_edge_relation spliced_circuit q
         =
         insert
           (?new_node_id, get_output_node_id q)
           (insert
             (frontier q, ?new_node_id)
             (wire_edge_relation ?circuit_with_node q -
                {(frontier q, get_output_node_id q)}))"
          using
            distinct_operation_wires
            True
            spliced_result
            splice_wires_updates_affected_wire_relation[
              of "op_qargs op" q
              ?circuit_with_node frontier ?new_node_id]
          by simp

        have node_insertion_preserves_relation:
          "wire_edge_relation ?circuit_with_node q =
         wire_edge_relation circuit q"
          unfolding
            wire_edge_relation_def
            insert_node_def
          by simp

        show ?thesis
          using
            spliced_result
            relation_after_splicing
            node_insertion_preserves_relation
          unfolding insert_operation_def Let_def
          by simp

      qed

      have valid_frontier_before:
        (* Extract the original frontier invariant from the valid
         construction-state assumption. *)
        "is_valid_frontier circuit frontier"
        using valid_state
        unfolding is_valid_construction_state_def
        by simp

      have new_node_unused_before:
        (* The node ID used for insertion was unused in the original
         circuit. *)
        "nodes circuit (next_id circuit) = None"
        using valid_state
        unfolding
          is_valid_construction_state_def
          next_id_is_unused_def
        by simp

      have output_node_exists_before:
        "nodes circuit (get_output_node_id q)
     = Some (OutputNode q)"
      proof -
        have "is_well_formed_circuit circuit"
          using
            is_valid_construction_state_def
            valid_state
          by simp
        then show ?thesis
          using
            are_well_formed_boundary_nodes_def
            get_qubit_index.elims
            insert_operation_num_qubits
            is_well_formed_circuit_def
            q_is_valid_after_insertion
            qubit_in_circuit_def
          by moura
      qed


      have new_node_not_output:
        "next_id circuit \<noteq> get_output_node_id q"
      proof
        assume same_id:
          "next_id circuit = get_output_node_id q"

        from new_node_unused_before have
          "nodes circuit (get_output_node_id q) = None"
          using same_id
          by simp

        with output_node_exists_before show False
          by simp
      qed

      have new_node_exists_after:
        (* The returned circuit stores the inserted operation node at the
         old next_id. *)
        "nodes ?updated_circuit (next_id circuit) =
       Some (OperationNode op)"
        using insert_operation_new_node
        by simp

      have new_node_uses_q:
        (* Since q occurs in the operation's qubit arguments, the inserted
         operation node uses q. *)
        "node_uses_qubit (OperationNode op) q"
        using True
        by simp

      have old_nodes_unchanged:
        (* Every node-table entry other than the newly allocated ID is
         unchanged by insert_operation. *)
        "node_id \<noteq> next_id circuit
       \<Longrightarrow> nodes ?updated_circuit node_id =
           nodes circuit node_id"
        for node_id
        using insert_operation_preserves_other_nodes
        by simp

      have comparable_after:
        "nodes_comparable_on_wire ?updated_circuit q"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          new_node_exists_after
          new_node_uses_q
          old_nodes_unchanged
          q_wire_relation_after
          subdividing_final_edge_preserves_wire_comparability
          wire_is_linear_def
          is_valid_construction_state_def valid_state
        by blast

      have input_node_exists_before:
        "nodes circuit (get_input_node_id q) =
   Some (InputNode q)"
        using
          valid_state
          q_is_valid_before_insertion
        unfolding
          is_valid_construction_state_def
          is_well_formed_circuit_def
          are_well_formed_boundary_nodes_def
          qubit_in_circuit_def
        by (metis get_qubit_index.elims)

      have new_node_not_input:
        "next_id circuit \<noteq> get_input_node_id q"
      proof
        assume same_id:
          "next_id circuit = get_input_node_id q"

        from new_node_unused_before same_id have
          "nodes circuit (get_input_node_id q) = None"
          by simp

        with input_node_exists_before show False
          by simp
      qed

      have input_boundary_after:
        "(\<nexists>predecessor_id.
          (predecessor_id, get_input_node_id q)
            \<in> wire_edge_relation ?updated_circuit q)
       \<and> has_unique_wire_successor
           ?updated_circuit q (get_input_node_id q)"

        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          q_wire_relation_after
          new_node_not_input
        using subdividing_final_edge_preserves_input_boundary
        by simp

      have output_predecessor_after:
        "has_unique_wire_predecessor
     ?updated_circuit q (get_output_node_id q)"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          q_wire_relation_after
          new_node_not_output
        by (simp add: subdividing_final_edge_preserves_output_predecessor)

      have output_no_successor_after:
        "\<nexists>successor_id.
     (get_output_node_id q, successor_id)
       \<in> wire_edge_relation ?updated_circuit q"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_not_output
          q_wire_relation_after
        by (rule subdividing_final_edge_preserves_output_no_successor)


      have operation_nodes_after:
        "\<forall>node_id stored_op.
         nodes ?updated_circuit node_id =
           Some (OperationNode stored_op)
         \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
         \<longrightarrow> has_unique_wire_predecessor
               ?updated_circuit q node_id
           \<and> has_unique_wire_successor
               ?updated_circuit q node_id"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          new_node_exists_after
          new_node_uses_q
          old_nodes_unchanged
          q_wire_relation_after
          is_valid_construction_state_def
          subdividing_final_edge_preserves_operation_node_degrees
          valid_state
        by simp

      show ?thesis
        using
          comparable_after
          input_boundary_after
          output_predecessor_after
          output_no_successor_after
          operation_nodes_after
        unfolding wire_is_linear_def
        by simp

    next
      case False

      have q_wire_relation_unchanged:
        "wire_edge_relation ?updated_circuit q = wire_edge_relation circuit q"

      proof -
        let ?new_node_id = "next_id circuit"

        let ?circuit_with_node =
          "insert_node
           ?new_node_id
           (OperationNode op)
           circuit"

        let ?spliced_result =
          "splice_wires
           ?circuit_with_node
           frontier
           (op_qargs op)
           ?new_node_id"

        obtain spliced_circuit updated_frontier where
          spliced_result:
          "?spliced_result =
           (spliced_circuit, updated_frontier)"
          by (cases ?spliced_result)

        have relation_after_splicing:
          "wire_edge_relation spliced_circuit q =
         wire_edge_relation ?circuit_with_node q"
          using
            False
            spliced_result
            splice_wires_preserves_unaffected_wire_relation[
              of q "op_qargs op"
              ?circuit_with_node frontier ?new_node_id]
          by simp

        have inserting_node_preserves_relation:
          "wire_edge_relation ?circuit_with_node q =
         wire_edge_relation circuit q"
          unfolding
            wire_edge_relation_def
            insert_node_def
          by simp

        show ?thesis
          using
            spliced_result
            relation_after_splicing
            inserting_node_preserves_relation
          unfolding
            insert_operation_def
            Let_def
          by simp
      qed

      have old_node_lookup_unchanged:
        (* Inserting the operation changes the nodes field only at the old
         next_id. Every other node-table entry remains unchanged. *)
        "node_id \<noteq> next_id circuit
       \<Longrightarrow> nodes ?updated_circuit node_id =
           nodes circuit node_id"
        for node_id

        unfolding
          insert_operation_def
          Let_def
        by simp

      have q_wire_reaches_unchanged:
        (* Since the immediate q-labelled edge relation is unchanged,
           its transitive closure, and therefore reachability on q, is
           unchanged as well. *)
        "wire_reaches ?updated_circuit q node_a node_b
         \<longleftrightarrow> wire_reaches circuit q node_a node_b"

        unfolding wire_reaches_def
        using q_wire_relation_unchanged
        by simp

      have q_nodes_comparable_after:
        "nodes_comparable_on_wire ?updated_circuit q"
        unfolding nodes_comparable_on_wire_def
      proof (intro allI impI)
        fix node_a node_b node_a_value node_b_value

        assume node_a_lookup_after:
          "nodes ?updated_circuit node_a = Some node_a_value"

        assume node_b_lookup_after:
          "nodes ?updated_circuit node_b = Some node_b_value"

        assume node_a_uses_q:
          "node_uses_qubit node_a_value q"

        assume node_b_uses_q:
          "node_uses_qubit node_b_value q"

        have node_a_not_new:
          "node_a \<noteq> next_id circuit"
        proof
          assume node_a_is_new:
            "node_a = next_id circuit"

          have new_node_lookup:
            "nodes ?updated_circuit (next_id circuit) =
           Some (OperationNode op)"
            using insert_operation_new_node
            by simp

          from
            node_a_lookup_after
            new_node_lookup
            node_a_is_new
          have node_a_value_eq:
            "node_a_value = OperationNode op"
            by simp

          from node_a_uses_q node_a_value_eq have
            "q \<in> set (op_qargs op)"
            by simp

          with False show False
            by contradiction
        qed

        have node_b_not_new:
          "node_b \<noteq> next_id circuit"
        proof
          assume node_b_is_new:
            "node_b = next_id circuit"

          have new_node_lookup:
            "nodes ?updated_circuit (next_id circuit) =
           Some (OperationNode op)"
            using insert_operation_new_node
            by simp

          from node_b_lookup_after new_node_lookup node_b_is_new
          have node_b_value_eq:
            "node_b_value = OperationNode op"
            by simp

          from node_b_uses_q node_b_value_eq have
            "q \<in> set (op_qargs op)"
            by simp

          with False show False
            by contradiction
        qed

        have node_a_lookup_before:
          "nodes circuit node_a = Some node_a_value"
          using
            node_a_lookup_after
            old_node_lookup_unchanged[OF node_a_not_new]
          by simp

        have node_b_lookup_before:
          "nodes circuit node_b = Some node_b_value"
          using
            node_b_lookup_after
            old_node_lookup_unchanged[OF node_b_not_new]
          by simp

        from q_is_linear_before_insertion have comparable_before:
          "nodes_comparable_on_wire circuit q"
          unfolding wire_is_linear_def
          by simp

        from comparable_before
          node_a_lookup_before
          node_b_lookup_before
          node_a_uses_q
          node_b_uses_q
        have
          "node_a = node_b
         \<or> wire_reaches circuit q node_a node_b
         \<or> wire_reaches circuit q node_b node_a"
          unfolding nodes_comparable_on_wire_def
          by blast

        then show
          "node_a = node_b
         \<or> wire_reaches ?updated_circuit q node_a node_b
         \<or> wire_reaches ?updated_circuit q node_b node_a"
          using
            q_wire_reaches_unchanged
            q_wire_relation_unchanged
            wire_reaches_def
          by simp
      qed

      have operation_nodes_linear_after:
        "\<forall>node_id stored_op.
         nodes ?updated_circuit node_id =
           Some (OperationNode stored_op)
         \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
         \<longrightarrow> has_unique_wire_predecessor
               ?updated_circuit q node_id
           \<and> has_unique_wire_successor
               ?updated_circuit q node_id"
      proof (intro allI impI)
        fix node_id stored_op

        assume operation_lookup_after:
          "nodes ?updated_circuit node_id =
         Some (OperationNode stored_op)"

        assume stored_op_uses_q:
          "node_uses_qubit (OperationNode stored_op) q"

        have node_id_not_new:
          "node_id \<noteq> next_id circuit"
        proof
          assume node_id_is_new:
            "node_id = next_id circuit"

          have new_node_lookup:
            "nodes ?updated_circuit (next_id circuit) = Some (OperationNode op)"
            using insert_operation_new_node
            by simp

          from operation_lookup_after
            new_node_lookup
            node_id_is_new
          have "stored_op = op"
            by simp

          with stored_op_uses_q have
            "q \<in> set (op_qargs op)"
            by simp

          with False show False
            by contradiction
        qed

        have operation_lookup_before:
          "nodes circuit node_id = Some (OperationNode stored_op)"
          using
            operation_lookup_after
            old_node_lookup_unchanged[OF node_id_not_new]
          by simp

        from q_is_linear_before_insertion
          operation_lookup_before
          stored_op_uses_q
        have old_degrees:
          "has_unique_wire_predecessor circuit q node_id
         \<and> has_unique_wire_successor circuit q node_id"
          unfolding wire_is_linear_def
          by blast

        show
          "has_unique_wire_predecessor
           ?updated_circuit q node_id
         \<and> has_unique_wire_successor
           ?updated_circuit q node_id"
          using old_degrees q_wire_relation_unchanged
          unfolding
            has_unique_wire_predecessor_def
            has_unique_wire_successor_def
          by simp
      qed

      show ?thesis
        using
          q_is_linear_before_insertion
          q_nodes_comparable_after
          operation_nodes_linear_after
          q_wire_relation_unchanged
        unfolding
          wire_is_linear_def
          has_unique_wire_predecessor_def
          has_unique_wire_successor_def
        by simp

    qed
  qed
qed

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

proof -
  let ?new_node_id = "next_id circuit"

  let ?updated_circuit = "fst (insert_operation circuit frontier op)"

  let ?old_relation = "edge_relation circuit"

  let ?updated_relation = "edge_relation ?updated_circuit"

  have old_relation_acyclic:
    "acyclic ?old_relation" (* Previous edge relations are acyclic *)
    using acyclic
    unfolding is_acyclic_circuit_def
    by simp

  have circuit_well_formed:
    "is_well_formed_circuit circuit" (* Previous circuit is well-formed *)
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have new_node_unused:
    "nodes circuit ?new_node_id = None" (* New node was unused before insertion *)
    using valid_state
    unfolding
      is_valid_construction_state_def
      next_id_is_unused_def
    by simp

  have new_node_not_old_source:
    "\<And>target_id.
       (?new_node_id, target_id) \<notin> ?old_relation" (* New node did not occur in any old edge *)
  proof -
    fix target_id
    show
      "(?new_node_id, target_id) \<notin> ?old_relation"

    proof
      assume relation_edge:
        "(?new_node_id, target_id) \<in> ?old_relation"

      then obtain e where
        edge_in:
        "e \<in> edges circuit"
        and source_eq:
        "edge_source e = ?new_node_id"
        unfolding edge_relation_def
        by blast

      have edge_well_formed:
        "is_well_formed_edge circuit e"
        using circuit_well_formed edge_in
        unfolding
          is_well_formed_circuit_def
          are_well_formed_edges_def
        by simp

      have source_exists:
        "node_exists circuit ?new_node_id"
        using edge_well_formed source_eq
        unfolding is_well_formed_edge_def
        by simp

      then show False
        using new_node_unused
        unfolding node_exists_def
        by simp
    qed
  qed

  have new_node_not_old_target:
    "\<And>source_id.
       (source_id, ?new_node_id) \<notin> ?old_relation"
  proof -
    fix source_id

    show
      "(source_id, ?new_node_id) \<notin> ?old_relation"
    proof
      assume relation_edge:
        "(source_id, ?new_node_id) \<in> ?old_relation"

      then obtain e where
        edge_in:
        "e \<in> edges circuit"
        and target_eq:
        "edge_target e = ?new_node_id"
        unfolding edge_relation_def
        by auto

      have edge_well_formed:
        "is_well_formed_edge circuit e"
        using circuit_well_formed edge_in
        unfolding is_well_formed_circuit_def
          are_well_formed_edges_def
        by blast

      have target_exists:
        "node_exists circuit ?new_node_id"
        using edge_well_formed target_eq
        unfolding is_well_formed_edge_def
        by simp

      then show False
        using new_node_unused
        unfolding node_exists_def
        by simp
    qed
  qed

(* ---------- Establish well-formedness and linearity after insertion proofs begin --------- *)

  have updated_state_valid:
    "is_valid_construction_state
       ?updated_circuit
       (snd (insert_operation circuit frontier op))"
    using valid_state operation_valid
    by (simp add: insert_operation_preserves_valid_construction_state)

  have updated_well_formed:
    "is_well_formed_circuit ?updated_circuit"
    using updated_state_valid
    unfolding is_valid_construction_state_def
    by simp

  have updated_linear:
    "all_wires_linear ?updated_circuit"
    using valid_state operation_valid linear_before
    by (simp add: insert_operation_preserves_wire_linearity)

(* ---------- Establish well-formedness and linearity after insertion proofs end --------- *)

  have updated_output_is_sink:
    "\<And>q target_id.
       qubit_in_circuit ?updated_circuit q
       \<Longrightarrow>
       (get_output_node_id q, target_id)
         \<notin> ?updated_relation"
  proof -
    fix q target_id

    assume valid_q:
      "qubit_in_circuit ?updated_circuit q"

    show
      "(get_output_node_id q, target_id)
         \<notin> ?updated_relation"
    proof
      assume relation_edge:
        "(get_output_node_id q, target_id)
           \<in> ?updated_relation"

      then obtain e where
        edge_in:
        "e \<in> edges ?updated_circuit"
        and source_eq:
        "edge_source e = get_output_node_id q"
        and  target_eq:
        "edge_target e = target_id"
        unfolding edge_relation_def
        by auto

      have edge_well_formed:
        "is_well_formed_edge ?updated_circuit e"
        using
          updated_well_formed
          edge_in
        unfolding
          is_well_formed_circuit_def
          are_well_formed_edges_def
        by simp

      have output_node_value:
        "nodes ?updated_circuit (get_output_node_id q)
           = Some (OutputNode q)"
        using updated_well_formed valid_q
        unfolding is_well_formed_circuit_def
          are_well_formed_boundary_nodes_def
          qubit_in_circuit_def
        by (cases q; simp)

      have edge_wire_is_q:
        "edge_wire e = q"
        using edge_well_formed source_eq output_node_value
        unfolding is_well_formed_edge_def
        by (cases "nodes ?updated_circuit (edge_source e)") auto

      have wire_linear_q:
        "wire_is_linear ?updated_circuit q"
        using updated_linear valid_q
        unfolding all_wires_linear_def
        by simp

      have no_output_successor:
        "\<nexists>successor_id.
           (get_output_node_id q, successor_id)
             \<in> wire_edge_relation ?updated_circuit q"
        using wire_linear_q
        unfolding wire_is_linear_def
        by simp

      have output_wire_edge:
        "(get_output_node_id q, target_id)
          \<in> wire_edge_relation ?updated_circuit q"
      proof -
        have edge_eq:
          "e =
             make_edge
               (get_output_node_id q)
               target_id
               q"
          using source_eq edge_wire_is_q target_eq
          by (cases e) (simp add: make_edge_def)

        show ?thesis
          unfolding wire_edge_relation_def
          using edge_in edge_eq
          by simp
      qed

      then show False
        using no_output_successor
        by simp
    qed
  qed

  have updated_cycle_implies_old_cycle:
    "\<And>node_id.
       (node_id, node_id) \<in> ?updated_relation\<^sup>+
       \<Longrightarrow>
       (node_id, node_id) \<in> ?old_relation\<^sup>+"

  proof -
    fix node_id
    assume updated_cycle:
      "(node_id, node_id) \<in> ?updated_relation\<^sup>+"

    have updated_edge_is_old_or_new:
      "\<And>u v.
         (u,v) \<in> ?updated_relation
        \<Longrightarrow>
         (u,v) \<in> ?old_relation
         \<or> u = ?new_node_id
         \<or> v = ?new_node_id"
    proof -
      fix u v
      assume updated_edge:
        "(u,v) \<in> ?updated_relation" 
      obtain e where
        edge_in:
        "e \<in> edges ?updated_circuit"
        and source:
        "edge_source e = u"
        and target:
        "edge_target e = v"

        using updated_edge
        unfolding edge_relation_def
        by auto

      have splice_wires_edge_cases:
        "\<And>base_circuit base_frontier qs e.
           e \<in> edges
             (fst
               (splice_wires
                 base_circuit
                 base_frontier
                 qs
                 ?new_node_id))
          \<Longrightarrow>
           e \<in> edges base_circuit
           \<or> edge_source e = ?new_node_id
           \<or> edge_target e = ?new_node_id"
      proof -
        fix base_circuit base_frontier qs e

        show
          "e \<in> edges
       (fst
         (splice_wires
           base_circuit
           base_frontier
           qs
           ?new_node_id))
     \<Longrightarrow>
       e \<in> edges base_circuit
       \<or> edge_source e = ?new_node_id
       \<or> edge_target e = ?new_node_id"
        proof (induction qs arbitrary: base_circuit base_frontier)
          case Nil

          then show ?case
            by simp

        next
          case (Cons q qs)

          obtain first_circuit first_frontier where first_splice:
            "splice_wire
               base_circuit
               base_frontier
               q
               ?new_node_id
             =
             (first_circuit, first_frontier)"
            by (cases
                "splice_wire
                   base_circuit
                   base_frontier
                   q
                   ?new_node_id")

          have after_remaining:
            "e \<in> edges first_circuit
           \<or> edge_source e = ?new_node_id
           \<or> edge_target e = ?new_node_id"
            using Cons.prems
              Cons.IH[of first_circuit first_frontier]
              first_splice
            by simp

          then show ?case
            using first_splice
            unfolding
              splice_wire_def
              splice_wire_without_updating_frontier_def
              insert_edge_def
              delete_edge_def
              make_edge_def
              Let_def
            by auto
        qed
      qed

      have edge_cases:
        "e \<in> edges circuit
       \<or> edge_source e = ?new_node_id
       \<or> edge_target e = ?new_node_id"
      proof -
        have spliced_edge_cases:
          "e \<in> edges (insert_node ?new_node_id (OperationNode op) circuit)
         \<or> edge_source e = ?new_node_id
         \<or> edge_target e = ?new_node_id"
          using
            edge_in
            splice_wires_edge_cases[
              where
                base_circuit =
                "insert_node
               ?new_node_id
               (OperationNode op)
               circuit"
                and base_frontier = frontier
                and qs = "op_qargs op"
                and e = e
                ]
          unfolding
            insert_operation_def
            Let_def
          by simp

        then show ?thesis
          unfolding insert_node_def
          by simp
      qed

      from edge_cases
      consider
        (old) "e \<in> edges circuit"
        | (src) "edge_source e = ?new_node_id"
        | (tgt) "edge_target e = ?new_node_id"
        by auto

      show
        "(u,v) \<in> ?old_relation
         \<or> u = ?new_node_id
         \<or> v = ?new_node_id"

        using edge_cases source target
        unfolding edge_relation_def
        by auto
    qed

    have updated_path_old_or_through_new:
      "\<And>u v.
     (u, v) \<in> ?updated_relation\<^sup>+
     \<Longrightarrow>
       (u, v) \<in> ?old_relation\<^sup>+
       \<or>
       ((u, ?new_node_id) \<in> ?updated_relation\<^sup>*
        \<and>
        (?new_node_id, v) \<in> ?updated_relation\<^sup>*)"
    proof -
      fix u v

      assume updated_path:
        "(u, v) \<in> ?updated_relation\<^sup>+"

      show
        "(u, v) \<in> ?old_relation\<^sup>+
     \<or>
     ((u, ?new_node_id) \<in> ?updated_relation\<^sup>*
      \<and>
      (?new_node_id, v) \<in> ?updated_relation\<^sup>*)"
        using updated_path
      proof (induction rule: trancl_induct)
        case (base v)

        have edge_cases:
          "(u, v) \<in> ?old_relation
       \<or> u = ?new_node_id
       \<or> v = ?new_node_id"
          using updated_edge_is_old_or_new[OF base]
          .

        then show ?case
        proof
          assume old_edge:
            "(u, v) \<in> ?old_relation"

          then have
            "(u, v) \<in> ?old_relation\<^sup>+"
            by (rule r_into_trancl)

          then show ?case
            by simp

        next
          assume new_endpoint:
            "u = ?new_node_id \<or> v = ?new_node_id"

          then show ?case
          proof
            assume source_new:
              "u = ?new_node_id"

            have start_refl:
              "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
              using source_new
              by simp

            have remaining_edge:
              "(?new_node_id, v) \<in> ?updated_relation\<^sup>*"
              using base source_new
              by auto

            show ?case
              using start_refl remaining_edge
              by blast

          next
            assume target_new:
              "v = ?new_node_id"

            have first_edge:
              "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
              using base target_new
              by auto

            have end_refl:
              "(?new_node_id, v) \<in> ?updated_relation\<^sup>*"
              using target_new
              by simp

            show ?case
              using first_edge end_refl
              by simp
          qed
        qed

      next
        case (step v w)

        have final_edge_cases:
          "(v, w) \<in> ?old_relation
         \<or> v = ?new_node_id
         \<or> w = ?new_node_id"
          using updated_edge_is_old_or_new[OF step.hyps(2)]
          .

        have induction_hypothesis:
          "(u, v) \<in> ?old_relation\<^sup>+
       \<or>
       ((u, ?new_node_id) \<in> ?updated_relation\<^sup>* \<and> (?new_node_id, v) \<in> ?updated_relation\<^sup>*)"
          by (simp add: step.IH)

        from induction_hypothesis
        show ?case
        proof
          assume old_path:
            "(u, v) \<in> ?old_relation\<^sup>+"

          from final_edge_cases
          show ?thesis
          proof
            assume old_edge:
              "(v, w) \<in> ?old_relation"

            have old_extended:
              "(u, w) \<in> ?old_relation\<^sup>+"
              using old_path old_edge
              by (rule trancl_into_trancl)

            then show ?thesis
              by blast

          next
            assume new_endpoint:
              "v = ?new_node_id \<or> w = ?new_node_id"

            then show ?thesis
            proof
              assume source_is_new:
                "v = ?new_node_id"

              have path_to_new:
                "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
                using step.hyps(1) source_is_new
                by (simp add: trancl_into_rtrancl)

              have path_from_new:
                "(?new_node_id, w) \<in> ?updated_relation\<^sup>*"
                using step.hyps(2) source_is_new
                by auto

              show ?thesis
                using path_to_new path_from_new
                by blast

            next
              assume target_is_new:
                "w = ?new_node_id"

              have updated_extended:
                "(u, w) \<in> ?updated_relation\<^sup>+"
                using step.hyps(1) step.hyps(2)
                by (rule trancl_into_trancl)

              have path_to_new:
                "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
                using updated_extended target_is_new
                by (simp add: trancl_into_rtrancl)

              have path_from_new:
                "(?new_node_id, w) \<in> ?updated_relation\<^sup>*"
                using target_is_new
                by simp

              show ?thesis
                using path_to_new path_from_new
                by blast
            qed
          qed

        next
          assume through_new:
            "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*
          \<and>
         (?new_node_id, v) \<in> ?updated_relation\<^sup>*"


          have path_to_new:
            "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
            using through_new
            by blast

          have path_from_new:
            "(?new_node_id, v) \<in> ?updated_relation\<^sup>*"
            using through_new
            by blast

          have extended_from_new:
            "(?new_node_id, w) \<in> ?updated_relation\<^sup>*"
            using path_from_new step.hyps(2)
            by (rule rtrancl_into_rtrancl)

          show ?thesis
            using path_to_new extended_from_new
            by blast

        qed
      qed
    qed


    have updated_cycle_old_or_contains_new:
      "\<And>x.
         (x, x) \<in> ?updated_relation\<^sup>+
         \<Longrightarrow>
         (x, x) \<in> ?old_relation\<^sup>+
       \<or> (?new_node_id, ?new_node_id) \<in> ?updated_relation\<^sup>+"
      by (metis
          rtrancl_eq_or_trancl
          trancl_rtrancl_trancl
          updated_path_old_or_through_new)


    have splice_wires_new_source_cases:
      "\<And>base_circuit base_frontier qs e.
     distinct qs
     \<Longrightarrow>
     (\<forall>q \<in> set qs.
        base_frontier q \<noteq> ?new_node_id)
     \<Longrightarrow>
     e \<in> edges
       (fst
         (splice_wires
           base_circuit
           base_frontier
           qs
           ?new_node_id))
     \<Longrightarrow>
     edge_source e = ?new_node_id
     \<Longrightarrow>
       (e \<in> edges base_circuit
        \<and> edge_source e = ?new_node_id)
       \<or>
       (\<exists>q \<in> set qs.
          e =
            make_edge
              ?new_node_id
              (get_output_node_id q)
              q)"
    proof -
      fix base_circuit :: quantum_circuit
        and base_frontier :: "qubit \<Rightarrow> node_id"
        and qs :: "qubit list"
        and e :: edge

      assume distinct_qs:
        "distinct qs"

      assume frontier_not_new:
        "\<forall>q \<in> set qs.
         base_frontier q \<noteq> ?new_node_id"

      assume edge_in:
        "e \<in> edges
       (fst
         (splice_wires
           base_circuit
           base_frontier
           qs
           ?new_node_id))"

      assume source_is_new:
        "edge_source e = ?new_node_id"

      show
        "(e \<in> edges base_circuit
      \<and> edge_source e = ?new_node_id)
     \<or>
     (\<exists>q \<in> set qs.
        e =
          make_edge
            ?new_node_id
            (get_output_node_id q)
            q)"
        using edge_in source_is_new distinct_qs frontier_not_new
      proof (induction qs arbitrary: base_circuit base_frontier)
        case Nil

        then show ?case
          by simp

      next
        case (Cons q qs)

        have q_not_in_remaining:
          "q \<notin> set qs"

          using Cons.prems(3)
          by simp

        have current_frontier_not_new:
          "base_frontier q \<noteq> ?new_node_id"
          using Cons.prems(4)
          by simp

        obtain first_circuit first_frontier where first_splice:
          "splice_wire
         base_circuit
         base_frontier
         q
         ?new_node_id
       =
       (first_circuit, first_frontier)"
          by (cases
              "splice_wire
             base_circuit
             base_frontier
             q
             ?new_node_id")

        have remaining_edge:
          "e \<in> edges
     (fst
       (splice_wires
         first_circuit
         first_frontier
         qs
         ?new_node_id))"
          using Cons.prems(1) first_splice
          by simp

        have remaining_source:
          "edge_source e = ?new_node_id"
          using Cons.prems(2)
          .

        have remaining_distinct:
          "distinct qs"
          using Cons.prems(3)
          by simp

        have remaining_frontier_not_new:
          "\<forall>r \<in> set qs.
     first_frontier r \<noteq> ?new_node_id"
          by (metis
              Cons.prems(4)
              first_splice list.set_intros(2)
              q_not_in_remaining
              snd_eqD
              splice_wire_def
              update_frontier_other)

        have after_remaining:
          "(e \<in> edges first_circuit
        \<and> edge_source e = ?new_node_id)
       \<or>
       (\<exists>r \<in> set qs.
          e =
            make_edge
              ?new_node_id
              (get_output_node_id r)
              r)"
          using
            Cons.IH[
              OF
              remaining_edge
              remaining_source
              remaining_distinct
              remaining_frontier_not_new] .

        then show ?case
          using 
            first_splice
            Cons.prems(4)
            edges_splice_wire_without_updating_frontier
          unfolding
            splice_wire_def
            splice_wire_without_updating_frontier_def
            insert_edge_def
            delete_edge_def
            make_edge_def
            Let_def
          by auto
      qed
    qed
    have new_node_successor_is_output:
      "\<And>target_id.
     (?new_node_id, target_id) \<in> ?updated_relation
     \<Longrightarrow>
     \<exists>q.
       qubit_in_circuit ?updated_circuit q
       \<and> target_id = get_output_node_id q"
    proof -
      fix target_id

      assume relation_edge:
        "(?new_node_id, target_id) \<in> ?updated_relation"

      obtain e where
        edge_in:
        "e \<in> edges ?updated_circuit"
        and source_eq:
        "edge_source e = ?new_node_id"
        and target_eq:
        "edge_target e = target_id"
        using relation_edge
        unfolding edge_relation_def
        by auto

      have distinct_qargs:
        "distinct (op_qargs op)"
        using operation_valid
        unfolding operation_in_circuit_def
        by (simp add: is_valid_operation_def)

      have frontier_not_new_on_qargs:
        "\<forall>q \<in> set (op_qargs op).
     frontier q \<noteq> ?new_node_id"
      proof (intro ballI)
        fix q
        assume q_in_args:
          "q \<in> set (op_qargs op)"

        have valid_q:
          "qubit_in_circuit circuit q"
          using operation_valid q_in_args
          unfolding operation_in_circuit_def
          by simp

        have frontier_exists:
          "node_exists circuit (frontier q)"

          using
            valid_state
            valid_q
            is_valid_frontier_def
            node_exists_def
            is_valid_construction_state_def

          by auto

        show "frontier q \<noteq> ?new_node_id"
        proof
          assume frontier_eq:
            "frontier q = ?new_node_id"

          have new_node_exists:
            "node_exists circuit ?new_node_id"
            using frontier_exists frontier_eq
            by simp

          show False
            using new_node_exists new_node_unused
            unfolding node_exists_def
            by simp
        qed
      qed

      have outgoing_cases:
        "(e \<in>
        edges
          (insert_node
            ?new_node_id
            (OperationNode op)
            circuit)
      \<and> edge_source e = ?new_node_id)
     \<or>
     (\<exists>q \<in> set (op_qargs op).
        e =
          make_edge
            ?new_node_id
            (get_output_node_id q)
            q)"
        using
          edge_in
          source_eq
          splice_wires_new_source_cases[
            where
              base_circuit =
              "insert_node
               ?new_node_id
               (OperationNode op)
               circuit"
              and base_frontier = frontier
              and qs = "op_qargs op"
              and e = e]
        unfolding insert_operation_def Let_def
        by (simp add:
            distinct_qargs
            frontier_not_new_on_qargs)


      have inserted_case_impossible:
        "\<not>
      (e \<in>
         edges
           (insert_node
             ?new_node_id
             (OperationNode op)
             circuit)
       \<and> edge_source e = ?new_node_id)"
      proof
        assume inserted_old:
          "e \<in>
         edges
           (insert_node
             ?new_node_id
             (OperationNode op)
             circuit)
       \<and> edge_source e = ?new_node_id"

        then have old_edge:
          "e \<in> edges circuit"
          unfolding insert_node_def
          by simp

        have old_relation_edge:
          "(?new_node_id, edge_target e) \<in> ?old_relation"
          using old_edge source_eq
          unfolding edge_relation_def
          by blast

        show False
          using
            new_node_not_old_source[of "edge_target e"]
            old_relation_edge
          by contradiction
      qed

      then obtain q where
        q_in_args:
        "q \<in> set (op_qargs op)"
        and edge_eq:
        "e =
        make_edge
          ?new_node_id
          (get_output_node_id q)
          q"
        using outgoing_cases
        by blast

      have valid_q_old:
        "qubit_in_circuit circuit q"
        using operation_valid q_in_args
        unfolding operation_in_circuit_def
        by blast

      have valid_q_updated:
        "qubit_in_circuit ?updated_circuit q"
        using
          qubit_in_circuit_def
          valid_q_old
        by auto

      have target_is_output:
        "target_id = get_output_node_id q"
        using target_eq edge_eq
        unfolding make_edge_def
        by simp

      show
        "\<exists>q.
       qubit_in_circuit ?updated_circuit q
       \<and> target_id = get_output_node_id q"
        using valid_q_updated target_is_output
        by blast
    qed

    have new_node_not_on_updated_cycle:
      "(?new_node_id, ?new_node_id) \<notin> ?updated_relation\<^sup>+"
      by (metis
          new_node_successor_is_output
          rtrancl_trancl_trancl
          tranclD updated_output_is_sink)

    show "(node_id, node_id) \<in> ?old_relation\<^sup>+"
      using
        updated_cycle
        updated_cycle_old_or_contains_new
        new_node_not_on_updated_cycle
      by simp
  qed

  have updated_relation_acyclic:
    "acyclic ?updated_relation"

  proof -
    show ?thesis
      unfolding acyclic_def
    proof
      fix node_id

      show
        "(node_id, node_id) \<notin> ?updated_relation\<^sup>+"
      proof
        assume updated_cycle:
          "(node_id, node_id) \<in> ?updated_relation\<^sup>+"

        have old_cycle:
          "(node_id, node_id) \<in> ?old_relation\<^sup>+"
          using updated_cycle_implies_old_cycle[OF updated_cycle]
          by simp

        have no_old_cycle:
          "(node_id, node_id) \<notin> ?old_relation\<^sup>+"
          using old_relation_acyclic
          unfolding acyclic_def
          by simp

        show False
          using old_cycle no_old_cycle
          by simp
      qed
    qed
  qed

  show ?thesis
    using updated_relation_acyclic
    unfolding is_acyclic_circuit_def
    by simp
qed

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
     satisfies every component of is_valid_circuit.
  *)
  assumes valid_circuit:
    "is_valid_circuit circuit"

assumes valid_state:
  "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

shows
  "is_valid_circuit
       (fst (insert_operation circuit frontier op))"
  using
    insert_operation_preserves_acyclicity
    insert_operation_preserves_well_formed_circuit
    insert_operation_preserves_wire_linearity
    is_valid_construction_state_def
    is_valid_circuit_def
    operation_valid valid_circuit
    valid_state
  by simp

lemma initial_construction_state_is_valid:
  (* The initial circuit together with the initial frontier forms a
     valid starting state for repeated operation insertion. *)
  "is_valid_construction_state (initial_circuit number_of_qubits) initial_frontier"

  using
    initial_circuit_is_well_formed
    initial_frontier_is_valid
    initial_next_id_is_unused
    initial_existing_node_ids_are_below_next_id
  unfolding is_valid_construction_state_def
  by simp

(* ============================================================ *)
(* Navigation functions                                         *)
(* ============================================================ *)

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

(* ============================================================ *)
(* Operation deletion                                           *)
(* ============================================================ *)

definition reconnect_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> quantum_circuit \<Rightarrow> quantum_circuit"
where
  (* Reconnect one wire around the operation node being deleted.

     The first circuit is the original circuit used to determine the
     predecessor and successor. The final circuit is the accumulating
     circuit whose edge set is modified by the fold.
  *)
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
  (* Delete an operation node while reconnecting every wire used by it.

     Suppose the node contains operation op and, on an affected wire q,
     the local structure is

         predecessor \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> node_id \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> successor.

     Deletion performs the following rewrite:

         1. remove predecessor \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> node_id;
         2. remove node_id \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> successor;
         3. insert predecessor \<midarrow>\<midarrow>q\<midarrow>\<midarrow>> successor.

     This rewrite is repeated for every qubit in op_qargs op. After all
     affected wires have been reconnected, the operation node is removed
     from the node table by mapping node_id to None.

     next_id is deliberately left unchanged. Deleted node IDs are not
     reused, so the monotonic node-allocation invariant remains compatible
     with later insertions.

     If node_id does not contain an OperationNode, the circuit is returned
     unchanged. If either adjacent node cannot be found on some affected
     wire, that wire is also left unchanged.
  *)
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
  (* Reconnecting one wire changes only the edge set. It does not change
     the node table. *)
  "nodes
     (reconnect_wire original_circuit operation_node_id q circuit)
     node_id
   =
   nodes circuit node_id"

  unfolding reconnect_wire_def
  apply (auto split: option.splits)
  by (simp add: delete_edge_def insert_edge_def)

lemma fold_reconnect_wire_preserves_nodes[simp]:
  (* Reconnecting any list of wires preserves the complete node table. *)
  "nodes
     (fold
        (reconnect_wire original_circuit operation_node_id)
        qs
        circuit)
     node_id
   =
   nodes circuit node_id"

proof (induction qs arbitrary: circuit)

  case Nil

  show ?case
    by simp

next

  case (Cons q qs)

  show ?case
    using Cons.IH
    by simp

qed

lemma delete_operation_nodes:
  (* When operation_node_id stores an OperationNode, deletion preserves
     every node-table entry except operation_node_id, which is mapped to
     None. *)
  assumes
    operation_exists:
      "nodes circuit operation_node_id =
         Some (OperationNode op)"
  shows
    "nodes
       (delete_operation circuit operation_node_id)
     =
     (nodes circuit)(operation_node_id := None)"

proof -

  have reconnected_nodes:
    "nodes
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
     =
     nodes circuit"

  proof (rule ext)

    fix node_id

    show
      "nodes
         (fold
            (reconnect_wire circuit operation_node_id)
            (op_qargs op)
            circuit)
         node_id
       =
       nodes circuit node_id"
      by simp

  qed

  show ?thesis
    unfolding delete_operation_def
    using operation_exists reconnected_nodes
    by simp

qed

lemma delete_operation_other_node[simp]:
  (* Deleting one operation does not change any other node-table entry. *)
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

  using
    delete_operation_nodes[OF operation_exists]
    different_node
  by simp

lemma reconnect_wire_edges_characterisation:
  (* Reconnecting a wire removes the two edges incident on the deleted
     operation node and inserts the corresponding bypass edge. *)
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

  unfolding
    reconnect_wire_def
    insert_edge_def
    delete_edge_def
    make_edge_def
  using predecessor successor
  by auto

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

proof -

  have
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
          -
          { make_edge predecessor_id operation_node_id q,
            make_edge operation_node_id successor_id q })"
    using assms
    by (rule reconnect_wire_edges_characterisation)

  then show ?thesis
    unfolding wire_edge_relation_def make_edge_def
    by auto

qed

lemma reconnect_wire_preserves_input_boundary:
  (* Reconnecting predecessor -> operation_node_id -> successor into
     predecessor -> successor preserves the input boundary of wire q.

     The original input node has no incoming q-edge and exactly one outgoing
     q-edge. The bypass edge cannot enter the input node. If the input node
     is the predecessor, its old edge to operation_node_id is replaced by
     exactly one edge to successor_id. Otherwise, its outgoing edge is
     unaffected.
  *)
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

proof -

  have incoming_operation_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have operation_not_input:
    "operation_node_id \<noteq> get_input_node_id q"
  proof
    assume
      "operation_node_id = get_input_node_id q"

    then have
      "(predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_input_predecessor
      by blast
  qed

  have successor_not_input:
    "successor_id \<noteq> get_input_node_id q"
  proof
    assume
      "successor_id = get_input_node_id q"

    then have
      "(operation_node_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_input_predecessor
      by blast
  qed

  have relation_after:
    "wire_edge_relation
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
     =
     insert
       (predecessor_id, successor_id)
       (wire_edge_relation circuit q
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  show ?thesis
    unfolding has_unique_wire_successor_def
    using
      no_input_predecessor
      unique_input_successor
      incoming_operation_edge
      operation_not_input
      successor_not_input
      relation_after
    unfolding has_unique_wire_successor_def
    by auto
qed

lemma reconnect_wire_preserves_input_boundary_from_same_relation:
  (* During a fold, predecessor and successor are always looked up in the
     fixed original circuit, while the edge rewrite is applied to the
     current accumulator.

     If the current accumulator still has the same q-edge relation as the
     original circuit, then reconnecting q preserves the input boundary
     on q.
  *)
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

proof -

  
  have incoming_operation_edge_original:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have incoming_operation_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation current_circuit q"
    using incoming_operation_edge_original same_relation
    by simp

  have outgoing_operation_edge_original:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation current_circuit q"
    using outgoing_operation_edge_original same_relation
    by simp

  have operation_not_input:
    "operation_node_id \<noteq> get_input_node_id q"
  proof
    assume
      "operation_node_id = get_input_node_id q"

    then have
      "(predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation current_circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_input_predecessor
      by blast
  qed

  have successor_not_input:
    "successor_id \<noteq> get_input_node_id q"
  proof
    assume
      "successor_id = get_input_node_id q"

    then have
      "(operation_node_id, get_input_node_id q)
         \<in> wire_edge_relation current_circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_input_predecessor
      by blast
  qed

  have relation_after:
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
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  show ?thesis
    using
      no_input_predecessor
      unique_input_successor
      incoming_operation_edge
      operation_not_input
      successor_not_input
      relation_after
    unfolding has_unique_wire_successor_def
    by auto

qed

lemma reconnect_wire_preserves_other_wire_relation:
  (* Reconnecting the deleted node on wire q changes only q-labelled
     edges. Therefore, the immediate-edge relation of every different
     wire r remains unchanged. *)
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

  unfolding
    reconnect_wire_def
    wire_edge_relation_def
    insert_edge_def
    delete_edge_def
    make_edge_def
  using different_wire
  by (auto split: option.splits)

lemma fold_reconnect_preserves_other_wire_relation:
  (* Reconnecting an entire list of wires different from r never changes
     the immediate edge relation on wire r. *)
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
  using other_wire

proof (induction qs arbitrary: current_circuit)

  case Nil

  show ?case
    by simp

next

  case (Cons q qs)
  
  have q_neq:
    "r \<noteq> q"
    using Cons.prems
    by simp

  have qs_not_contains:
    "r \<notin> set qs"
    using Cons.prems
    by simp

  show ?case
    using
      reconnect_wire_preserves_other_wire_relation[OF q_neq]
      Cons.IH[OF qs_not_contains]
    by simp

qed

lemma fold_reconnect_preserves_input_boundary:
  (* In a distinct list of affected wires containing q, all wires before
     and after q leave q's relation unchanged. The single reconnection of
     q preserves its input boundary. *)
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

proof -

  obtain before after where
    qs_decomposition:
      "qs = before @ q # after"
    using used_wire
    by (meson split_list)

  have q_not_in_before:
    "q \<notin> set before"
    using distinct_wires qs_decomposition
    by auto

  have q_not_in_after:
    "q \<notin> set after"
    using distinct_wires qs_decomposition
    by auto

  let ?before_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       before
       circuit"

  let ?q_circuit =
    "reconnect_wire
       circuit
       operation_node_id
       q
       ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q =
       wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation[
        where original_circuit = circuit
          and operation_node_id = operation_node_id
          and qs = before
          and current_circuit = circuit
          and r = q,
        OF q_not_in_before]
    by simp

  have no_input_predecessor_before:
    "\<nexists>pred.
       (pred, get_input_node_id q)
         \<in> wire_edge_relation ?before_circuit q"
    using
      no_input_predecessor
      before_same_relation
    by simp

  have unique_input_successor_before:
    "has_unique_wire_successor
       ?before_circuit q (get_input_node_id q)"
    using
      unique_input_successor
      before_same_relation
    unfolding has_unique_wire_successor_def
    by auto

  have boundary_after_q:
    "(\<nexists>pred.
         (pred, get_input_node_id q)
           \<in> wire_edge_relation ?q_circuit q)
     \<and>
     has_unique_wire_successor
       ?q_circuit q (get_input_node_id q)"
    using
      reconnect_wire_preserves_input_boundary_from_same_relation[
        OF
          no_input_predecessor_before
          unique_input_successor_before
          before_same_relation
          predecessor
          successor]
    by simp

  have after_same_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
     =
     wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation[
        where original_circuit = circuit
          and operation_node_id = operation_node_id
          and qs = after
          and current_circuit = ?q_circuit
          and r = q,
        OF q_not_in_after]
    by simp

  show ?thesis
    using
      boundary_after_q
      after_same_relation
      qs_decomposition
    unfolding has_unique_wire_successor_def
    by auto

qed

lemma delete_operation_removes_operation_node[simp]:
  (* If node_id stores an OperationNode, then deleting that operation
     removes it from the circuit. *)

  assumes operation_node:
    "nodes circuit node_id = Some (OperationNode op)"

  shows
    "nodes (delete_operation circuit node_id) node_id = None"

proof -

  have delete_case:
    "delete_operation circuit node_id =
      (let
         reconnect_wire =
           (\<lambda>q current_circuit.
              case
                (predecessor_on_wire circuit node_id q,
                 successor_on_wire circuit node_id q)
              of

                (Some predecessor, Some successor) \<Rightarrow>
                  insert_edge
                    (make_edge predecessor successor q)
                    (delete_edge
                      (make_edge node_id successor q)
                      (delete_edge
                        (make_edge predecessor node_id q)
                        current_circuit))

              | _ \<Rightarrow> current_circuit);

         reconnected_circuit =
           fold
             reconnect_wire
             (op_qargs op)
             circuit;

         circuit_without_node =
           reconnected_circuit
             \<lparr>nodes :=
                (nodes reconnected_circuit)
                  (node_id := None)\<rparr>

       in
         circuit_without_node)"
    using operation_node 
    unfolding
      delete_operation_def
      Let_def
      reconnect_wire_def
    by simp

  show ?thesis
    unfolding
      delete_case
      Let_def
    by simp
qed

lemma reconnect_wire_preserves_num_qubits:
  (* Reconnecting a single wire only updates the circuit's edge set.
     It does not change the number of qubits in the circuit. *)
  "num_qubits
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   num_qubits current_circuit"
  
  unfolding
    reconnect_wire_def
    delete_edge_def 
    insert_edge_def

  by (auto split:
        option.splits
        prod.splits)

lemma reconnect_wire_edge_cases:
  (* Every edge present after reconnecting one wire is either:

       1. an edge that was already present in the accumulating circuit; or
       2. the new direct predecessor-to-successor edge inserted on q.

     This lemma deliberately over-approximates the old-edge case: some old
     incident edges may have been deleted, but every surviving old edge
     certainly belonged to current_circuit.
  *)
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
proof -
  show ?thesis
    using edge_after
    unfolding reconnect_wire_def
    by (auto
          split:
            option.splits
            prod.splits)
qed

lemma fold_reconnect_wire_edge_cases:
  (*
    Every edge present after reconnecting a list of wires is either an
    original edge or a bypass edge introduced while processing one wire
    from that list.
  *)
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
  
  using edge_after

proof (induction qs arbitrary: current_circuit)

  case Nil

  (*
    Folding over an empty wire list leaves the accumulating circuit
    unchanged. Therefore, every resulting edge is already an edge of
    current_circuit.
  *)
  then show ?case
    by simp

next

  case (Cons q qs)

  (*
    The first fold step reconnects q. The remaining wires qs are then
    processed using that updated circuit as the new accumulator.
  *)
  let ?updated_circuit =
    "reconnect_wire
       original_circuit
       operation_node_id
       q
       current_circuit"

  have edge_after_remaining_wires:
    "e \<in>
     edges
       (fold
         (reconnect_wire original_circuit operation_node_id)
         qs
         ?updated_circuit)"
    using Cons.prems
    by simp

  (*
    Apply the induction hypothesis to the remaining fold. The edge is
    either already present immediately after reconnecting q, or it is a
    bypass edge introduced while processing one of the later wires in qs.
  *)
  have remaining_wire_cases:
    "e \<in> edges ?updated_circuit
     \<or>
     (\<exists>q' \<in> set qs.
        \<exists>predecessor successor.
          predecessor_on_wire
            original_circuit operation_node_id q'
            = Some predecessor
        \<and>
          successor_on_wire
            original_circuit operation_node_id q'
            = Some successor
        \<and>
          e = make_edge predecessor successor q')"
    using Cons.IH[of ?updated_circuit]
          edge_after_remaining_wires
    by blast

    from remaining_wire_cases show ?case
  proof

    assume edge_after_first_reconnection:
      "e \<in> edges ?updated_circuit"

    have first_wire_cases:
      "e \<in> edges current_circuit
       \<or>
       (\<exists>predecessor successor.
          predecessor_on_wire
            original_circuit operation_node_id q
            = Some predecessor
        \<and>
          successor_on_wire
            original_circuit operation_node_id q
            = Some successor
        \<and>
          e = make_edge predecessor successor q)"
      using edge_after_first_reconnection
      by (rule reconnect_wire_edge_cases)

    then show ?thesis
      by auto

  next

    assume bypass_on_remaining_wire:
      "\<exists>q' \<in> set qs.
         \<exists>predecessor successor.
           predecessor_on_wire
             original_circuit operation_node_id q'
             = Some predecessor
         \<and>
           successor_on_wire
             original_circuit operation_node_id q'
             = Some successor
         \<and>
           e = make_edge predecessor successor q'"

    then show ?thesis
      by simp
  qed
qed

lemma reconnect_wire_inserted_edge_well_formed:
  (*
    Whenever reconnect_wire inserts a bypass edge, that edge is
    well formed in the resulting circuit.

    reconnect_wire modifies only the edge set. Therefore the node table
    and qubit count remain unchanged, while the predecessor and successor
    already satisfy the endpoint conditions inherited from the original
    well-formed edges.
  *)
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

proof -

  (*
    Structural validity of the original circuit guarantees that every
    edge already present in it is well formed.
  *)
  have original_edges_well_formed:
    "are_well_formed_edges circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  (*
    predecessor_on_wire identifies an existing edge entering
    operation_node_id from predecessor_node_id on q.
  *)
  have predecessor_edge:
    "make_edge predecessor_node_id operation_node_id q
       \<in> edges circuit"
    using predecessor
    by (rule predecessor_on_wire_correct)

  (*
    successor_on_wire identifies an existing edge leaving
    operation_node_id toward successor_node_id on q.
  *)
  have successor_edge:
    "make_edge operation_node_id successor_node_id q
       \<in> edges circuit"
    using successor
    by (rule successor_on_wire_correct)

  (* Both incident edges are well formed in the original valid circuit. *)
  have predecessor_edge_well_formed:
    "is_well_formed_edge
       circuit
       (make_edge predecessor_node_id operation_node_id q)"
    using original_edges_well_formed predecessor_edge
    unfolding are_well_formed_edges_def
    by blast

  have successor_edge_well_formed:
    "is_well_formed_edge
       circuit
       (make_edge operation_node_id successor_node_id q)"
    using original_edges_well_formed successor_edge
    unfolding are_well_formed_edges_def
    by blast

  (*
    From the incoming edge, obtain everything needed about the new bypass
    edge's source:

      • predecessor_node_id exists;
      • q is a valid circuit qubit;
      • the predecessor node lies on q.
  *)
  have predecessor_properties:
    "node_exists circuit predecessor_node_id
     \<and> qubit_in_circuit circuit q
     \<and>
       (case nodes circuit predecessor_node_id of
          None \<Rightarrow> False
        | Some predecessor_node \<Rightarrow>
            node_uses_qubit predecessor_node q)"
    using
      predecessor_edge_well_formed
      is_well_formed_edge_def
    unfolding
      make_edge_def
    by (metis edge.select_convs(1,3))

  (*
    From the outgoing edge, obtain the corresponding properties of the
    new bypass edge's target.
  *)
  have successor_properties:
    "node_exists circuit successor_node_id
     \<and>
       (case nodes circuit successor_node_id of
          None \<Rightarrow> False
        | Some successor_node \<Rightarrow>
            node_uses_qubit successor_node q)"
    using successor_edge_well_formed
    unfolding
      is_well_formed_edge_def
      make_edge_def
    by (metis edge.select_convs(2,3))

  (*
    reconnect_wire changes only the edge set. Hence the predecessor and
    successor node entries, together with the circuit's qubit count, are
    identical before and after reconnection.
  *)
  have predecessor_node_preserved:
    "nodes
       (reconnect_wire circuit operation_node_id q circuit)
       predecessor_node_id
     =
     nodes circuit predecessor_node_id"
    by (rule reconnect_wire_preserves_nodes)

  have successor_node_preserved:
    "nodes
       (reconnect_wire circuit operation_node_id q circuit)
       successor_node_id
     =
     nodes circuit successor_node_id"
    by (rule reconnect_wire_preserves_nodes)

  have num_qubits_preserved:
    "num_qubits
       (reconnect_wire circuit operation_node_id q circuit)
     =
     num_qubits circuit"
    by (rule reconnect_wire_preserves_num_qubits)

  (*
    The bypass edge therefore has two existing endpoints that both use q,
    and q remains valid in the reconnected circuit.
  *)
  show ?thesis
    using
      predecessor_properties
      successor_properties
      predecessor_node_preserved
      successor_node_preserved
      num_qubits_preserved
    unfolding
      is_well_formed_edge_def
      node_exists_def
      qubit_in_circuit_def
      make_edge_def
    by (simp add: option.case_eq_if)
qed

lemma fold_reconnect_wire_preserves_num_qubits:
  (* Reconnecting every wire in a list preserves the circuit's qubit count.
     This lifts the single-wire preservation result across the fold. *)
  "num_qubits
     (fold
       (reconnect_wire original_circuit node_id)
       qs
       current_circuit)
   =
   num_qubits current_circuit"

proof (induction qs arbitrary: current_circuit)
  case Nil

  then show ?case
    by simp

next
  case (Cons q qs)

  have first_reconnection:
    "num_qubits
       (reconnect_wire
         original_circuit
         node_id
         q
         current_circuit)
     =
     num_qubits current_circuit"
    by (rule reconnect_wire_preserves_num_qubits)

  have remaining_reconnections:
    "num_qubits
       (fold
         (reconnect_wire original_circuit node_id)
         qs
         (reconnect_wire
           original_circuit
           node_id
           q
           current_circuit))
     =
     num_qubits
       (reconnect_wire
         original_circuit
         node_id
         q
         current_circuit)"
    using Cons
    by simp

  show ?case
    using first_reconnection remaining_reconnections
    by simp
qed

lemma operation_incident_edge_on_wire_cases:
  (*
    In a valid circuit, every edge on q that is incident to an operation
    node is exactly the unique incoming edge selected by
    predecessor_on_wire or the unique outgoing edge selected by
    successor_on_wire.

    This connects the abstract wire-linearity invariant with the concrete
    edges removed by reconnect_wire.
  *)
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
proof -

  (* The stored operation is well formed, so every qubit it uses is a
     valid circuit qubit. *)
  have operation_in_circuit:
    "operation_in_circuit circuit op"
    using valid_circuit operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
    by blast

  have valid_q:
    "qubit_in_circuit circuit q"
    using operation_in_circuit operation_uses_wire
    unfolding operation_in_circuit_def
    by blast

  (* Validity also guarantees that q forms a linear wire. *)
  have linear_q:
    "wire_is_linear circuit q"
    using valid_circuit valid_q
    unfolding
      is_valid_circuit_def
      all_wires_linear_def
    by blast

  (* Since OperationNode op uses q, wire linearity gives a unique
     predecessor and a unique successor on that wire. *)
  have unique_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using
      linear_q
      operation_exists
      operation_uses_wire
    unfolding wire_is_linear_def
    by simp

  have unique_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using
      linear_q
      operation_exists
      operation_uses_wire
    unfolding wire_is_linear_def
    by simp

  from incident show ?thesis
  proof

    assume source_is_operation:
      "edge_source e = operation_node_id"

    (* The given edge itself witnesses an outgoing q-edge from the
       operation node. *)
    have given_successor_relation:
      "(operation_node_id, edge_target e)
       \<in> wire_edge_relation circuit q"
      using
        incident_edge
        source_is_operation
        edge_on_wire
      unfolding wire_edge_relation_def
      by (cases e) (simp add: make_edge_def)

    (* Obtain the unique successor promised by wire linearity. *)
    obtain unique_successor_id where
      successor_relation:
        "(operation_node_id, unique_successor_id)
         \<in> wire_edge_relation circuit q"
    and
      successor_unique:
        "\<And>candidate.
           (operation_node_id, candidate)
           \<in> wire_edge_relation circuit q
           \<Longrightarrow>
           candidate = unique_successor_id"
      using unique_successor
      unfolding has_unique_wire_successor_def
      by blast

    (* The concrete given edge must target that unique successor. *)
    have target_is_unique_successor:
      "edge_target e = unique_successor_id"
      using successor_unique given_successor_relation
      by blast

    (* successor_on_wire returns some outgoing q-edge. Its target must
       therefore equal the same unique successor. *)
    have outgoing_exists:
      "\<exists>outgoing.
         outgoing_edge circuit operation_node_id q =
           Some outgoing"
    proof -
      have
        "\<exists>outgoing \<in> edges circuit.
           edge_source outgoing = operation_node_id
         \<and> edge_wire outgoing = q"
        using
          incident_edge
          source_is_operation
          edge_on_wire
        by blast

      then show ?thesis
        unfolding outgoing_edge_def
        by (auto intro: someI_ex)
    qed

    then obtain outgoing where
      outgoing:
        "outgoing_edge circuit operation_node_id q =
           Some outgoing"
      by blast

    have outgoing_properties:
      "outgoing \<in> edges circuit
       \<and> edge_source outgoing = operation_node_id
       \<and> edge_wire outgoing = q"
      using outgoing
      by (rule outgoing_edge_correct)

    have selected_successor_relation:
      "(operation_node_id, edge_target outgoing)
       \<in> wire_edge_relation circuit q"
      using outgoing_properties
      unfolding wire_edge_relation_def
      by (cases outgoing) (simp add: make_edge_def)

    have selected_target:
      "edge_target outgoing = unique_successor_id"
      using successor_unique selected_successor_relation
      by blast

    have successor_lookup:
      "successor_on_wire circuit operation_node_id q =
         Some unique_successor_id"
      using outgoing selected_target
      unfolding successor_on_wire_def
      by simp

    (* The record fields determine e completely. *)
    have edge_shape:
      "e =
       make_edge
         operation_node_id
         unique_successor_id
         q"
      using
        source_is_operation
        target_is_unique_successor
        edge_on_wire
      by (cases e) (simp add: make_edge_def)

    show ?thesis
      using successor_lookup edge_shape
      by blast

  next

    assume target_is_operation:
      "edge_target e = operation_node_id"

    (* The given edge itself witnesses an incoming q-edge to the
       operation node. *)
    have given_predecessor_relation:
      "(edge_source e, operation_node_id)
       \<in> wire_edge_relation circuit q"
      using
        incident_edge
        target_is_operation
        edge_on_wire
      unfolding wire_edge_relation_def
      by (cases e) (simp add: make_edge_def)

    (* Obtain the unique predecessor promised by wire linearity. *)
    obtain unique_predecessor_id where
      predecessor_relation:
        "(unique_predecessor_id, operation_node_id)
         \<in> wire_edge_relation circuit q"
    and
      predecessor_unique:
        "\<And>candidate.
           (candidate, operation_node_id)
           \<in> wire_edge_relation circuit q
           \<Longrightarrow>
           candidate = unique_predecessor_id"
      using unique_predecessor
      unfolding has_unique_wire_predecessor_def
      by blast

    (* The concrete given edge must originate at that unique predecessor. *)
    have source_is_unique_predecessor:
      "edge_source e = unique_predecessor_id"
      using predecessor_unique given_predecessor_relation
      by blast

    (* predecessor_on_wire returns some incoming q-edge. Its source must
       therefore equal the same unique predecessor. *)
    have incoming_exists:
      "\<exists>incoming.
         incoming_edge circuit operation_node_id q =
           Some incoming"
    proof -
      have
        "\<exists>incoming \<in> edges circuit.
           edge_target incoming = operation_node_id
         \<and> edge_wire incoming = q"
        using
          incident_edge
          target_is_operation
          edge_on_wire
        by blast

      then show ?thesis
        unfolding incoming_edge_def
        by (auto intro: someI_ex)
    qed

    then obtain incoming where
      incoming:
        "incoming_edge circuit operation_node_id q =
           Some incoming"
      by blast

    have incoming_properties:
      "incoming \<in> edges circuit
       \<and> edge_target incoming = operation_node_id
       \<and> edge_wire incoming = q"
      using incoming
      by (rule incoming_edge_correct)

    have selected_predecessor_relation:
      "(edge_source incoming, operation_node_id)
       \<in> wire_edge_relation circuit q"
      using incoming_properties
      unfolding wire_edge_relation_def
      by (cases incoming) (simp add: make_edge_def)

    have selected_source:
      "edge_source incoming = unique_predecessor_id"
      using predecessor_unique selected_predecessor_relation
      by blast

    have predecessor_lookup:
      "predecessor_on_wire circuit operation_node_id q =
         Some unique_predecessor_id"
      using incoming selected_source
      unfolding predecessor_on_wire_def
      by simp

    (* The record fields determine e completely. *)
    have edge_shape:
      "e =
       make_edge
         unique_predecessor_id
         operation_node_id
         q"
      using
        source_is_unique_predecessor
        target_is_operation
        edge_on_wire
      by (cases e) (simp add: make_edge_def)

    show ?thesis
      using
        predecessor_lookup
        edge_shape
      by blast
  qed
qed

lemma fold_reconnect_wire_removes_incident_edges:
  (*
    After reconnecting every wire used by the deleted operation, no edge
    remaining in the accumulated circuit is incident to that operation
    node.

    Every edge incident to operation_node_id lies on a wire in op_qargs op.
    Processing that wire removes the corresponding incoming or outgoing
    edge. Later reconnection steps cannot recreate an edge incident to the
    operation node, because they insert only predecessor-to-successor
    bypass edges.
  *)
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
proof -

  (* The operation stored at operation_node_id is valid. In particular,
     its qubit arguments are pairwise distinct. *)
  have operation_valid:
    "is_valid_operation op"
    using valid_circuit operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_operation_wires:
    "distinct (op_qargs op)"
    using operation_valid
    unfolding is_valid_operation_def
    by simp

  (* Every original edge is well formed. This will let us infer that an
     edge incident to OperationNode op lies on one of op_qargs op. *)
  have original_edges_well_formed:
    "are_well_formed_edges circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  (* The original circuit is acyclic, so neither a predecessor nor a
     successor selected around operation_node_id can equal that node. *)
  have original_acyclic:
    "is_acyclic_circuit circuit"
    using valid_circuit
    unfolding is_valid_circuit_def
    by simp

  show ?thesis
  proof (rule ccontr)

    assume not_non_incident:
      "\<not>
        (edge_source e \<noteq> operation_node_id
         \<and> edge_target e \<noteq> operation_node_id)"

    then have incident:
      "edge_source e = operation_node_id
       \<or> edge_target e = operation_node_id"
      by simp

    (* Every edge produced by the fold is either inherited from the
       original circuit or is a newly inserted bypass edge. *)
    have edge_origin:
      "e \<in> edges circuit
       \<or>
       (\<exists>q \<in> set (op_qargs op).
          \<exists>predecessor successor.
            predecessor_on_wire
              circuit operation_node_id q
              = Some predecessor
          \<and>
            successor_on_wire
              circuit operation_node_id q
              = Some successor
          \<and>
            e = make_edge predecessor successor q)"
      using remaining_edge
      by (rule fold_reconnect_wire_edge_cases)

    from edge_origin show False
    proof

      assume original_edge:
        "e \<in> edges circuit"

      (* Since e is well formed and touches OperationNode op, its wire must
         be one of the operation's qubit arguments. *)
      have original_edge_well_formed:
        "is_well_formed_edge circuit e"
        using original_edges_well_formed original_edge
        unfolding are_well_formed_edges_def
        by simp

      have edge_wire_used_by_operation:
        "edge_wire e \<in> set (op_qargs op)"
        using
          original_edge_well_formed
          operation_exists
          incident
        unfolding
          is_well_formed_edge_def
          node_exists_def
        by (auto split: option.splits)

      let ?q = "edge_wire e"

      (* The helper identifies e as exactly the incoming or outgoing edge
         selected by reconnect_wire on its wire. *)
      have selected_edge_cases:
        "(\<exists>predecessor.
            predecessor_on_wire
              circuit operation_node_id ?q
              = Some predecessor
          \<and>
            e = make_edge predecessor operation_node_id ?q)
         \<or>
         (\<exists>successor.
            successor_on_wire
              circuit operation_node_id ?q
              = Some successor
          \<and>
            e = make_edge operation_node_id successor ?q)"
        using
          valid_circuit
          operation_exists
          edge_wire_used_by_operation
          original_edge
          incident
          operation_incident_edge_on_wire_cases
        by simp

      (*
        Reconnecting a different wire cannot insert e, because every edge
        inserted on that step carries that different wire. Since the
        operation's wire list is distinct, e is removed when ?q is
        processed and cannot be recreated later.
      *)
      have selected_edge_removed:
        "e \<notin>
         edges
           (fold
             (reconnect_wire circuit operation_node_id)
             (op_qargs op)
             circuit)"
      proof -
        obtain before after where
          operation_wires_split:
            "op_qargs op = before @ ?q # after"
          using edge_wire_used_by_operation
          by (metis split_list)

        have q_not_in_before:
          "?q \<notin> set before"
        and
          q_not_in_after:
          "?q \<notin> set after"
          using
            distinct_operation_wires
            operation_wires_split
          by auto

        let ?before_circuit =
          "fold
             (reconnect_wire circuit operation_node_id)
             before
             circuit"

        let ?q_circuit =
          "reconnect_wire
             circuit
             operation_node_id
             ?q
             ?before_circuit"

        (* Both adjacent lookups exist. Whichever side of the operation e
           occupies, wire linearity supplies the other side as well. *)
                have predecessor_exists:
          "\<exists>predecessor.
             predecessor_on_wire
               circuit operation_node_id ?q
             = Some predecessor"
        proof -

          (* Wire linearity guarantees that the operation has an incoming
             neighbour on ?q. *)
          obtain predecessor where
            predecessor_relation:
              "(predecessor, operation_node_id)
               \<in> wire_edge_relation circuit ?q"
            using
              valid_circuit
              operation_exists
              edge_wire_used_by_operation
              are_well_formed_operation_nodes_def
              is_well_formed_circuit_def
              node_uses_qubit.simps(3)
              operation_in_circuit_def
            unfolding
              is_valid_circuit_def
              all_wires_linear_def
              wire_is_linear_def
              has_unique_wire_predecessor_def
            by blast

          have incoming_edge_exists:
            "make_edge predecessor operation_node_id ?q
             \<in> edges circuit"
            using predecessor_relation
            unfolding wire_edge_relation_def
            by simp

          have incoming_exists:
            "\<exists>incoming \<in> edges circuit.
               edge_target incoming = operation_node_id
             \<and> edge_wire incoming = ?q"
            proof
            show
              "make_edge predecessor operation_node_id ?q
               \<in> edges circuit"
              using incoming_edge_exists .

            show
              "edge_target
                 (make_edge predecessor operation_node_id ?q)
               = operation_node_id
               \<and>
               edge_wire
                 (make_edge predecessor operation_node_id ?q)
               = ?q"
              unfolding make_edge_def
              by simp
          qed

          (* Therefore incoming_edge returns Some edge, and mapping its
             source produces Some predecessor node. *)
          show ?thesis
            using incoming_exists
            unfolding
              predecessor_on_wire_def
              incoming_edge_def
            by simp
        qed

        have successor_exists:
          "\<exists>successor.
             successor_on_wire
               circuit operation_node_id ?q
             = Some successor"
        proof -

          (* Wire linearity guarantees an outgoing neighbour of the
             operation node on ?q. *)
          obtain successor where
            successor_relation:
              "(operation_node_id, successor)
               \<in> wire_edge_relation circuit ?q"
            using
              valid_circuit
              operation_exists
              edge_wire_used_by_operation
              are_well_formed_operation_nodes_def
              is_well_formed_circuit_def
              node_uses_qubit.simps(3)
              operation_in_circuit_def
            unfolding
              is_valid_circuit_def
              all_wires_linear_def
              wire_is_linear_def
              has_unique_wire_successor_def
            by blast

                  let ?outgoing =
            "make_edge operation_node_id successor ?q"

          have outgoing_in_edges:
            "?outgoing \<in> edges circuit"
            using successor_relation
            unfolding wire_edge_relation_def
            by simp

          have outgoing_source:
            "edge_source ?outgoing = operation_node_id"
            unfolding make_edge_def
            by simp

          have outgoing_wire:
            "edge_wire ?outgoing = ?q"
            unfolding make_edge_def
            by simp

          have outgoing_exists:
            "\<exists>outgoing \<in> edges circuit.
               edge_source outgoing = operation_node_id
             \<and> edge_wire outgoing = ?q"
            using
              outgoing_in_edges
              outgoing_source
              outgoing_wire
            by auto

          (* Hence at least one concrete edge leaves operation_node_id
             on wire ?q. *)
          have outgoing_exists:
            "\<exists>outgoing \<in> edges circuit.
               edge_source outgoing = operation_node_id
             \<and> edge_wire outgoing = ?q"
            using
              outgoing_in_edges
              outgoing_source
              outgoing_wire
            by auto

          (* Therefore outgoing_edge returns Some edge, and mapping its
             target produces Some successor node. *)
          show ?thesis
            using outgoing_exists
            unfolding
              successor_on_wire_def
              outgoing_edge_def
            by simp
        qed

        obtain predecessor where
          predecessor_lookup:
            "predecessor_on_wire
               circuit operation_node_id ?q
             = Some predecessor"
          using predecessor_exists
          by auto

        obtain successor where
          successor_lookup:
            "successor_on_wire
               circuit operation_node_id ?q
             = Some successor"
          using successor_exists
          by blast

        (* The selected predecessor cannot be operation_node_id. Otherwise,
           the original incoming edge would be a self-loop. *)
        have predecessor_not_operation:
          "predecessor \<noteq> operation_node_id"
        proof
          assume predecessor_eq:
            "predecessor = operation_node_id"

          have self_loop_edge:
            "make_edge operation_node_id operation_node_id ?q
             \<in> edges circuit"
            using
              predecessor_on_wire_correct[OF predecessor_lookup]
              predecessor_eq
            by simp

          have self_loop_relation:
            "(operation_node_id, operation_node_id)
             \<in> edge_relation circuit"
            using self_loop_edge
            unfolding edge_relation_def make_edge_def
            by force

          have self_reachable:
            "(operation_node_id, operation_node_id)
             \<in> (edge_relation circuit)\<^sup>+"
            using self_loop_relation
            by (rule r_into_trancl)

          show False
            using original_acyclic self_reachable
            unfolding is_acyclic_circuit_def
            by (simp add: acyclic_def)
        qed

        (* The selected successor cannot be operation_node_id. Otherwise,
           the original outgoing edge would be a self-loop. *)
        have successor_not_operation:
          "successor \<noteq> operation_node_id"
        proof
          assume successor_eq:
            "successor = operation_node_id"

          have self_loop_edge:
            "make_edge operation_node_id operation_node_id ?q
             \<in> edges circuit"
            using
              successor_on_wire_correct[OF successor_lookup]
              successor_eq
            by simp

          have self_loop_relation:
            "(operation_node_id, operation_node_id)
             \<in> edge_relation circuit"
            using self_loop_edge
            unfolding edge_relation_def make_edge_def
            by force

          have self_reachable:
            "(operation_node_id, operation_node_id)
             \<in> (edge_relation circuit)\<^sup>+"
            using self_loop_relation
            by (rule r_into_trancl)

          show False
            using original_acyclic self_reachable 
            unfolding is_acyclic_circuit_def
            by (simp add: acyclic_def)
        qed

        (* The q-step removes both incident edges. The inserted bypass edge
           cannot equal either removed edge because neither bypass endpoint
           is operation_node_id. *)
               
        have q_step_edges:
          "edges ?q_circuit =
             insert
               (make_edge predecessor successor ?q)
               ((edges ?before_circuit
                 - {make_edge predecessor operation_node_id ?q})
                - {make_edge operation_node_id successor ?q})"
          using
            predecessor_lookup
            successor_lookup
          unfolding
            reconnect_wire_def
            insert_edge_def
            delete_edge_def
          by simp

        (* The selected incident edge is absent immediately after the
           reconnection step on its own wire. *)
        have absent_after_q:
          "e \<notin> edges ?q_circuit"
        proof -

          from selected_edge_cases show ?thesis
          proof

            assume incoming_case:
              "\<exists>selected_predecessor.
                 predecessor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_predecessor
               \<and>
                 e =
                   make_edge
                     selected_predecessor
                     operation_node_id
                     ?q"

            then obtain selected_predecessor where
              selected_predecessor_lookup:
                "predecessor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_predecessor"
            and
              e_shape:
                "e =
                   make_edge
                     selected_predecessor
                     operation_node_id
                     ?q"
              by blast

            (* Both lookup equations return Some, so their predecessor
               values must coincide. *)
            have selected_predecessor_eq:
              "selected_predecessor = predecessor"
              using
                selected_predecessor_lookup
                predecessor_lookup
              by simp

            have e_is_removed_incoming:
              "e =
               make_edge predecessor operation_node_id ?q"
              using e_shape selected_predecessor_eq
              by simp

            (* The bypass edge cannot equal the incoming edge because its
               target is successor rather than operation_node_id. *)
            have e_not_bypass:
              "e \<noteq> make_edge predecessor successor ?q"
              using
                e_is_removed_incoming
                successor_not_operation
              apply (auto simp: make_edge_def)
              by (metis edge.ext_inject)

            show ?thesis
              using
                q_step_edges
                e_is_removed_incoming
                e_not_bypass
              by simp

          next

            assume outgoing_case:
              "\<exists>selected_successor.
                 successor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_successor
               \<and>
                 e =
                   make_edge
                     operation_node_id
                     selected_successor
                     ?q"

            then obtain selected_successor where
              selected_successor_lookup:
                "successor_on_wire
                   circuit operation_node_id ?q
                   = Some selected_successor"
            and
              e_shape:
                "e =
                   make_edge
                     operation_node_id
                     selected_successor
                     ?q"
              by blast

            (* Both lookup equations return Some, so their successor
               values must coincide. *)
            have selected_successor_eq:
              "selected_successor = successor"
              using
                selected_successor_lookup
                successor_lookup
              by simp

            have e_is_removed_outgoing:
              "e =
               make_edge operation_node_id successor ?q"
              using e_shape selected_successor_eq
              by simp

            (* The bypass edge cannot equal the outgoing edge because its
               source is predecessor rather than operation_node_id. *)
            have e_not_bypass:
              "e \<noteq> make_edge predecessor successor ?q"
              using
                e_is_removed_outgoing
                predecessor_not_operation
              apply (auto simp: make_edge_def)
              by (metis edge.ext_inject)

            show ?thesis
              using
                q_step_edges
                e_is_removed_outgoing
                e_not_bypass
              by simp
          qed
        qed
        
        have absent_after_later_wires:
          "\<And>current.
             e \<notin> edges current
             \<Longrightarrow>
             e \<notin>
               edges
                 (fold
                   (reconnect_wire circuit operation_node_id)
                   after
                   current)"
          by (metis fold_reconnect_wire_edge_cases make_edges_on_different_wires_unequal q_not_in_after
              selected_edge_cases)


        (* After the q-step, processing the remaining suffix preserves the
           absence of e. Rewriting the original fold using the before/q/after
           decomposition therefore proves that e is absent from the complete
           fold. *)
        have absent_after_suffix:
          "e \<notin>
           edges
             (fold
               (reconnect_wire circuit operation_node_id)
               after
               ?q_circuit)"
          using absent_after_q
          by (rule absent_after_later_wires)

        show ?thesis
          using
            operation_wires_split
            absent_after_suffix
          by simp
      qed

      (* This contradicts the assumption that e remains after the complete
         reconnection fold. *)
      show False
        using remaining_edge selected_edge_removed
        by simp
    next

      assume bypass_edge:
        "\<exists>q \<in> set (op_qargs op).
           \<exists>predecessor successor.
             predecessor_on_wire
               circuit operation_node_id q
               = Some predecessor
           \<and>
             successor_on_wire
               circuit operation_node_id q
               = Some successor
           \<and>
             e = make_edge predecessor successor q"

      then obtain q predecessor successor where
        predecessor_lookup:
          "predecessor_on_wire
             circuit operation_node_id q
           = Some predecessor"
      and
        successor_lookup:
          "successor_on_wire
             circuit operation_node_id q
           = Some successor"
      and
        edge_eq:
          "e = make_edge predecessor successor q"
        by blast

      (* If either bypass endpoint equalled operation_node_id, the
         corresponding original incident edge would be a self-loop,
         contradicting acyclicity. *)
      have predecessor_not_operation:
        "predecessor \<noteq> operation_node_id"
      proof
        assume predecessor_eq:
          "predecessor = operation_node_id"

        have self_loop:
          "make_edge operation_node_id operation_node_id q
           \<in> edges circuit"
          using
            predecessor_on_wire_correct[OF predecessor_lookup]
            predecessor_eq
          by simp

        have self_relation:
          "(operation_node_id, operation_node_id)
           \<in> edge_relation circuit"
          using self_loop
          unfolding edge_relation_def make_edge_def
          by force

        have
          "(operation_node_id, operation_node_id)
           \<in> (edge_relation circuit)\<^sup>+"
          using self_relation
          by (rule r_into_trancl)

        with original_acyclic show False
          unfolding is_acyclic_circuit_def
          by (simp add: acyclic_def)

      qed

      have successor_not_operation:
        "successor \<noteq> operation_node_id"
      proof
        assume successor_eq:
          "successor = operation_node_id"

        have self_loop:
          "make_edge operation_node_id operation_node_id q
           \<in> edges circuit"
          using
            successor_on_wire_correct[OF successor_lookup]
            successor_eq
          by simp

        have self_relation:
          "(operation_node_id, operation_node_id)
           \<in> edge_relation circuit"
          using self_loop
          unfolding edge_relation_def make_edge_def
          by force

        have
          "(operation_node_id, operation_node_id)
           \<in> (edge_relation circuit)\<^sup>+"
          using self_relation
          by (rule r_into_trancl)

        with original_acyclic show False
          unfolding is_acyclic_circuit_def

          by (simp add: acyclic_def)
      qed

      (* A bypass edge connects the predecessor directly to the successor,
         neither of which is the deleted operation node. *)
      have bypass_not_incident:
        "edge_source e \<noteq> operation_node_id
         \<and> edge_target e \<noteq> operation_node_id"
        using
          edge_eq
          predecessor_not_operation
          successor_not_operation
        unfolding make_edge_def
        by simp

      show False
        using incident bypass_not_incident
        by auto
    qed
  qed
qed

lemma delete_operation_preserves_num_qubits:
  (* Deleting an operation only modifies the graph structure. The number
     of qubits in the circuit remains unchanged. *)

  shows
    "num_qubits (delete_operation circuit node_id) = num_qubits circuit"

proof (cases "nodes circuit node_id")
  case None
  then show ?thesis
    unfolding delete_operation_def
    by simp

next
  case (Some node)

  then show ?thesis
  proof (cases node)

    case (InputNode q)

    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OutputNode q)

    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OperationNode op)

    have fold_preserves_num_qubits:
      "num_qubits
         (fold
           (reconnect_wire circuit node_id)
           (op_qargs op)
           circuit)
       =
       num_qubits circuit"

      by (rule fold_reconnect_wire_preserves_num_qubits)

    show ?thesis
      using
        Some
        OperationNode
        fold_preserves_num_qubits
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed
qed

lemma reconnect_wire_preserves_next_id:
  (* Reconnecting a single wire does not allocate or remove node identifiers.
     Therefore, the next unused node identifier remains unchanged. *)
  "next_id
     (reconnect_wire original_circuit node_id q current_circuit)
   =
   next_id current_circuit"

  using
    delete_edge_def
    insert_edge_def
  unfolding reconnect_wire_def
  by (simp split: option.splits)

lemma fold_reconnect_wire_preserves_next_id:
  (* Reconnecting every wire in a list preserves next_id.
     Each individual reconnection leaves next_id unchanged, so the entire
     fold leaves it unchanged as well. *)
  "next_id
     (fold
        (reconnect_wire original_circuit node_id)
        qs
        current_circuit)
   =
   next_id current_circuit"

proof (induction qs arbitrary: current_circuit)
  case Nil
  then show ?case
    by simp

next
  case (Cons q qs)

  have first_reconnection:
    "next_id
       (reconnect_wire
          original_circuit
          node_id
          q
          current_circuit)
     =
     next_id current_circuit"
    by (rule reconnect_wire_preserves_next_id)

  have remaining_reconnections:
    "next_id
       (fold
          (reconnect_wire original_circuit node_id)
          qs
          (reconnect_wire
             original_circuit
             node_id
             q
             current_circuit))
     =
     next_id
       (reconnect_wire
          original_circuit
          node_id
          q
          current_circuit)"
    using Cons
    by simp

  show ?case
    using first_reconnection remaining_reconnections
    by simp
qed

lemma delete_operation_preserves_next_id:
  (* Deleting an operation removes its node and reconnects its incident wires,
     but it does not reuse the deleted node identifier or allocate a new one.
     Therefore, next_id remains unchanged. *)
  "next_id (delete_operation circuit node_id) = next_id circuit"

proof (cases "nodes circuit node_id")
  case None
  then show ?thesis
    unfolding delete_operation_def
    by simp

next
  case (Some node)

  show ?thesis
  proof (cases node)

    case (InputNode q)
    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OutputNode q)
    then show ?thesis
      using Some
      unfolding delete_operation_def
      by simp

  next

    case (OperationNode op)

    have
      "next_id
         (fold
            (reconnect_wire circuit node_id)
            (op_qargs op)
            circuit)
       =
       next_id circuit"
      by (rule fold_reconnect_wire_preserves_next_id)

    then show ?thesis
      using Some OperationNode
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed
qed

lemma delete_operation_preserves_boundary_nodes:
  (* Deleting an operation preserves all canonical input and output nodes.

     reconnect_wire modifies only the edge set. After all affected wires
     have been reconnected, delete_operation changes the node table only
     at operation_node_id, mapping that ID to None.

     Since operation_node_id stores an OperationNode, it cannot be one of
     the canonical input or output node IDs. Therefore, every required
     boundary-node lookup remains unchanged.
  *)
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

proof -
  have wf:
    "are_well_formed_boundary_nodes circuit"
    using
      valid_circuit
      is_well_formed_circuit_def
    unfolding is_valid_circuit_def
    by simp

  show ?thesis
    using
      wf
      operation_exists
      fold_reconnect_wire_preserves_nodes
      fold_reconnect_wire_preserves_num_qubits
    unfolding
      delete_operation_def
      are_well_formed_boundary_nodes_def
      Let_def
    by auto
qed

lemma delete_operation_preserves_operation_nodes:
  (* Deleting one operation preserves the validity of every remaining
     operation node.

     Wire reconnection changes only edges. The final node-table update
     maps operation_node_id to None and leaves every other node unchanged.

     Hence, any OperationNode found after deletion was already present in
     the original circuit. Since the original circuit is valid, that
     remaining operation is still valid for the circuit. The qubit count
     is unchanged by deletion.
  *)
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

proof -
  have original_operation_nodes:
    "are_well_formed_operation_nodes circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  show ?thesis
    unfolding are_well_formed_operation_nodes_def

  proof (intro allI impI)

    fix remaining_node_id remaining_op

    assume remaining_node:
      "nodes
         (delete_operation circuit operation_node_id)
         remaining_node_id
       =
       Some (OperationNode remaining_op)"

    have remaining_node_id_not_deleted:
      "remaining_node_id \<noteq> operation_node_id"
    proof
      assume
        "remaining_node_id = operation_node_id"

      then have
        "nodes
           (delete_operation circuit operation_node_id)
           remaining_node_id
         =
         None"
        using operation_exists
              delete_operation_removes_operation_node
        by simp

      with remaining_node show False
        by simp
    qed

    have remaining_node_original:
      "nodes circuit remaining_node_id =
         Some (OperationNode remaining_op)"
      using
        remaining_node
        remaining_node_id_not_deleted
        operation_exists
        fold_reconnect_wire_preserves_nodes
      unfolding
        delete_operation_def
        Let_def
      by simp

    have operation_valid_original:
      "operation_in_circuit circuit remaining_op"
      using original_operation_nodes remaining_node_original
      unfolding are_well_formed_operation_nodes_def
      by simp

    show
      "operation_in_circuit
         (delete_operation circuit operation_node_id)
         remaining_op"
      using
        operation_valid_original
        delete_operation_preserves_num_qubits
      unfolding
        operation_in_circuit_def
        qubit_in_circuit_def
      by simp
  qed
qed

lemma delete_operation_edge_preserves_reachability:
  (*
    Every single directed edge remaining after deleting an operation
    represents non-empty reachability in the original circuit.

    An edge in the deleted circuit is either:

      1. an original edge that survived deletion; or
      2. a newly inserted bypass edge from a predecessor to a successor.

    In the bypass case, the original circuit contains the two-edge path

        predecessor \<rightarrow> operation_node_id \<rightarrow> successor.
  *)
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
proof -

  (*
    Membership in edge_relation provides a concrete wire-labelled edge
    whose source and target are source_id and target_id.
  *)
  obtain e where
    edge_in_deleted_circuit:
      "e \<in> edges
         (delete_operation circuit operation_node_id)"
  and
    edge_source:
      "edge_source e = source_id"
  and
    edge_target:
      "edge_target e = target_id"
    using edge_after
    unfolding edge_relation_def
    by blast

  (*
    The final step of delete_operation changes only the node table.
    Therefore, every edge in the deleted circuit is already present after
    folding reconnect_wire over the operation's qubit arguments.
  *)
  have edge_after_reconnection:
    "e \<in>
     edges
       (fold
         (reconnect_wire circuit operation_node_id)
         (op_qargs op)
         circuit)"
    using
      edge_in_deleted_circuit
      operation_exists
    unfolding
      delete_operation_def
      Let_def
    by simp

  (*
    Characterize the origin of e. It is either an edge inherited from the
    original circuit or a bypass edge introduced on one of the deleted
    operation's wires.
  *)
  have edge_cases:
    "e \<in> edges circuit
     \<or>
     (\<exists>q \<in> set (op_qargs op).
        \<exists>predecessor successor.
          predecessor_on_wire
            circuit operation_node_id q
            = Some predecessor
        \<and>
          successor_on_wire
            circuit operation_node_id q
            = Some successor
        \<and>
          e = make_edge predecessor successor q)"
    using edge_after_reconnection
    by (rule fold_reconnect_wire_edge_cases)

  from edge_cases show ?thesis
  proof

    assume original_edge:
      "e \<in> edges circuit"

    (*
      An inherited edge directly gives one step in the original circuit's
      edge relation.
    *)
    have original_relation_edge:
      "(source_id, target_id) \<in> edge_relation circuit"
      using
        original_edge
        edge_source
        edge_target
      unfolding edge_relation_def
      by blast

    (* Every relation edge belongs to its non-empty transitive closure. *)
    show ?thesis
      using original_relation_edge
      by (rule r_into_trancl)

  next

    assume bypass_edge:
      "\<exists>q \<in> set (op_qargs op).
         \<exists>predecessor successor.
           predecessor_on_wire
             circuit operation_node_id q
             = Some predecessor
         \<and>
           successor_on_wire
             circuit operation_node_id q
             = Some successor
         \<and>
           e = make_edge predecessor successor q"

    then obtain q predecessor successor where
      predecessor:
        "predecessor_on_wire
           circuit operation_node_id q
         =
         Some predecessor"
    and
      successor:
        "successor_on_wire
           circuit operation_node_id q
         =
         Some successor"
    and
      bypass_edge_eq:
        "e = make_edge predecessor successor q"
      by blast

    (*
      The source and target of the concrete bypass edge are respectively
      predecessor and successor.
    *)
    have source_id_eq:
      "source_id = predecessor"
      using edge_source bypass_edge_eq
      unfolding make_edge_def
      by simp

    have target_id_eq:
      "target_id = successor"
      using edge_target bypass_edge_eq
      unfolding make_edge_def
      by simp

    (*
      predecessor_on_wire and successor_on_wire identify the two original
      edges incident to operation_node_id.
    *)
    have incoming_edge:
      "make_edge predecessor operation_node_id q
       \<in> edges circuit"
      using predecessor
      by (rule predecessor_on_wire_correct)

    have outgoing_edge:
      "make_edge operation_node_id successor q
       \<in> edges circuit"
      using successor
      by (rule successor_on_wire_correct)

    (* The incoming wire-labelled edge gives the first relation step. *)
    have incoming_relation:
      "(predecessor, operation_node_id)
       \<in> edge_relation circuit"
      using incoming_edge
      unfolding
        make_edge_def
        edge_relation_def
      by force

    (* The outgoing wire-labelled edge gives the second relation step. *)
    have outgoing_relation:
      "(operation_node_id, successor)
       \<in> edge_relation circuit"
      using outgoing_edge
      unfolding
        edge_relation_def
        make_edge_def
      by force

    (*
      Convert the first edge to a non-empty path and append the second
      edge. This reconstructs the original two-edge path represented by
      the bypass edge.
    *)
    have bypass_reachable:
      "(predecessor, successor)
       \<in> (edge_relation circuit)\<^sup>+"
    proof -
      have
        "(predecessor, operation_node_id)
         \<in> (edge_relation circuit)\<^sup>+"
        using incoming_relation
        by (rule r_into_trancl)

      then show ?thesis
        using outgoing_relation
        by (rule trancl_into_trancl)
    qed

    show ?thesis
      using
        bypass_reachable
        source_id_eq
        target_id_eq
      by simp
  qed
qed

lemma delete_operation_remaining_edges_not_incident:
  (*
    After deleting an operation, no remaining edge has the deleted
    operation node as either its source or its target.

    Every edge incident to operation_node_id lies on a qubit used by op,
    because the original edge is well formed and the node stored at
    operation_node_id is OperationNode op.

    delete_operation reconnects every qubit in op_qargs op. On each such
    wire, reconnect_wire removes the unique incoming and outgoing edges
    incident to operation_node_id. Therefore, after the complete fold,
    no incident edge remains.
  *)
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

proof -
  (* The final update performed by delete_operation modifies only nodes,
     so the remaining edge already exists after the reconnection fold. *)
  have edge_after_fold:
    "e \<in>
     edges
       (fold
         (reconnect_wire circuit operation_node_id)
         (op_qargs op)
         circuit)"
    using
      remaining_edge
      operation_exists
    unfolding
      delete_operation_def
      Let_def
    by simp

  (* Apply the structural fold invariant proved independently of edge
     well-formedness preservation. *)
  show ?thesis
    using
      valid_circuit
      operation_exists
      edge_after_fold
    by (rule fold_reconnect_wire_removes_incident_edges)
qed

lemma delete_operation_preserves_well_formed_edges:
  (* Deleting an operation preserves the well-formedness of every edge.

     For each qubit used by the deleted operation, deletion removes the
     incoming and outgoing edges incident to operation_node_id and inserts
     a direct edge from the predecessor to the successor.

     Wire linearity guarantees that these adjacent nodes and edges exist.
     The original edge well-formedness guarantees that the predecessor and
     successor both exist, use the same valid qubit, and therefore form a
     well-formed replacement edge.

     Every unaffected edge remains an original well-formed edge, while no
     remaining edge is incident to the removed operation node.
  *)
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


proof -
  have original_edges_well_formed:
    "are_well_formed_edges circuit"
    using valid_circuit
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
    by simp

  show ?thesis
    unfolding are_well_formed_edges_def
  proof (intro ballI)

    fix e

    assume edge_after:
      "e \<in> edges
         (delete_operation circuit operation_node_id)"

    have endpoints_not_deleted:
      "edge_source e \<noteq> operation_node_id
       \<and> edge_target e \<noteq> operation_node_id"
      using
        valid_circuit
        operation_exists
        edge_after
      by (rule delete_operation_remaining_edges_not_incident)

    obtain reconnected_circuit where
      reconnected_circuit:
        "reconnected_circuit =
           fold
             (reconnect_wire circuit operation_node_id)
             (op_qargs op)
             circuit"
      by simp

    have edge_in_reconnected:
      "e \<in> edges reconnected_circuit"
      using
        edge_after
        operation_exists
        reconnected_circuit
        delete_operation_def
      unfolding Let_def
      by simp

    have edge_origin:
      "e \<in> edges circuit
       \<or>
       (\<exists> q \<in> set (op_qargs op).
          \<exists>predecessor successor.
            predecessor_on_wire
              circuit operation_node_id q
              = Some predecessor
          \<and>
            successor_on_wire
              circuit operation_node_id q
              = Some successor
          \<and>
            e = make_edge predecessor successor q)"
      using
        edge_in_reconnected
        reconnected_circuit
        fold_reconnect_wire_edge_cases

      by simp

    then consider
        (original) "e \<in> edges circuit"
      | (bypass)
          q predecessor successor where
          "q \<in> set (op_qargs op)"
          "predecessor_on_wire
             circuit operation_node_id q
             = Some predecessor"
          "successor_on_wire
             circuit operation_node_id q
             = Some successor"
          "e = make_edge predecessor successor q"
      by auto

    then show
      "is_well_formed_edge
         (delete_operation circuit operation_node_id)
         e"
    proof cases

      case original

      have original_edge_well_formed:
        "is_well_formed_edge circuit e"
        using
          original_edges_well_formed
          original
        unfolding are_well_formed_edges_def
        by simp

      (*
        The edge existed originally and neither endpoint is the removed
        operation node. The deletion therefore preserves both endpoint
        nodes. It also preserves num_qubits, so the edge wire remains a
        valid circuit qubit.
      *)
      show ?thesis
        using
          original_edge_well_formed
          endpoints_not_deleted
          operation_exists
          delete_operation_preserves_num_qubits[of
            circuit operation_node_id]
          fold_reconnect_wire_preserves_nodes[of
            circuit operation_node_id
            "op_qargs op" circuit]
        unfolding
          is_well_formed_edge_def
          node_exists_def
          qubit_in_circuit_def
          delete_operation_def
          Let_def
        by (simp split: option.splits)
    next

      case (bypass q predecessor successor)

      (*
        This edge is exactly a bypass edge created between the original
        predecessor and successor on q. Its well-formedness after the
        complete deletion follows from the dedicated local helper.
      *)
      case (bypass q predecessor successor)

      (* The predecessor-to-operation edge exists in the original circuit. *)
      have predecessor_edge:
        "make_edge predecessor operation_node_id q
         \<in> edges circuit"
        using bypass(2)
        by (rule predecessor_on_wire_correct)

      (* The operation-to-successor edge also exists in the original circuit. *)
      have successor_edge:
        "make_edge operation_node_id successor q
         \<in> edges circuit"
        using bypass(3)
        by (rule successor_on_wire_correct)

      (* Since the original circuit is valid, both incident edges are
         well formed. Their outer endpoints therefore exist, lie on q,
         and q is a valid circuit qubit. *)
      have predecessor_edge_well_formed:
        "is_well_formed_edge
           circuit
           (make_edge predecessor operation_node_id q)"
        using original_edges_well_formed predecessor_edge
        unfolding are_well_formed_edges_def
        by blast

      have successor_edge_well_formed:
        "is_well_formed_edge
           circuit
           (make_edge operation_node_id successor q)"
        using original_edges_well_formed successor_edge
        unfolding are_well_formed_edges_def
        by blast

      (* The bypass edge remains after deletion, so neither of its endpoints
         can be the removed operation node. *)
      have bypass_edge_after:
        "make_edge predecessor successor q
         \<in> edges
             (delete_operation circuit operation_node_id)"
        using edge_after bypass(4)
        by simp

      have bypass_endpoints_not_deleted:
        "predecessor \<noteq> operation_node_id
         \<and> successor \<noteq> operation_node_id"
        using
          delete_operation_remaining_edges_not_incident[
            OF valid_circuit operation_exists bypass_edge_after]
        unfolding make_edge_def
        by simp

      (* Reconnection preserves the node table, and the final deletion changes
         only operation_node_id. Since predecessor and successor are different
         from that node, their node entries are unchanged. The qubit count is
         also preserved. *)
      show ?thesis
        using
          predecessor_edge_well_formed
          successor_edge_well_formed
          bypass_endpoints_not_deleted
          operation_exists
          bypass(4)
          delete_operation_preserves_num_qubits[
            of circuit operation_node_id]
          fold_reconnect_wire_preserves_nodes[
            of circuit operation_node_id
               "op_qargs op" circuit predecessor]
          fold_reconnect_wire_preserves_nodes[
            of circuit operation_node_id
               "op_qargs op" circuit successor]
        unfolding
          is_well_formed_edge_def
          node_exists_def
          qubit_in_circuit_def
          delete_operation_def
          make_edge_def
          Let_def
        by auto
    qed
  qed
qed

lemma delete_operation_preserves_well_formed_circuit:
  (* Deleting an operation preserves the local structural validity of the
     circuit.

     Deletion performs three conceptual steps:

       1. Remove the operation node.
       2. Remove all incident wire edges.
       3. Reconnect each predecessor directly to its corresponding successor.

     Since the deleted operation belongs to a valid quantum circuit,
     every newly created edge reconnects nodes that already lie on the
     same valid qubit wire. Boundary nodes are unchanged, and every
     remaining operation node is unchanged. Consequently, deleting an
     operation preserves the well-formedness of the circuit.
  *)
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

proof -

  have boundary_nodes:
    "are_well_formed_boundary_nodes
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
      delete_operation_preserves_boundary_nodes
    by simp

  have operation_nodes:
    "are_well_formed_operation_nodes
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
      delete_operation_preserves_operation_nodes
    by simp

  have edges:
    "are_well_formed_edges
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
      delete_operation_preserves_well_formed_edges
    by simp

  show ?thesis
    unfolding is_well_formed_circuit_def
    using
      boundary_nodes
      operation_nodes
      edges
    by simp
qed

lemma delete_operation_reachability_preserved:
  (* Every non-empty directed path that exists after deleting an operation
     corresponds to a non-empty directed path that already existed in the
     original circuit.

     Edges unaffected by deletion are original circuit edges. Every new
     predecessor-to-successor edge introduced by reconnect_wire replaces
     the original two-edge path

         predecessor \<rightarrow> operation_node_id \<rightarrow> successor.

     Consequently, deletion may shorten directed paths, but it cannot
     introduce reachability between nodes that were not already reachable
     in the original circuit.
  *)
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
proof

  fix node_pair

  assume reachable_after_deletion:
    "node_pair
     \<in>
     (edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+"

  (*
    Expose the source and target components of the pair so that the
    transitive-closure induction can reason about the path endpoints.
  *)
  obtain source_id target_id where
    node_pair:
      "node_pair = (source_id, target_id)"
    by (cases node_pair)

  have source_reaches_target_after_deletion:
    "(source_id, target_id)
     \<in>
     (edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+"
    using reachable_after_deletion node_pair
    by simp

  (*
    Induct over the non-empty path in the deleted circuit.

    The base case contains one deleted-circuit edge. The helper
    delete_operation_edge_preserves_reachability maps that edge to a
    non-empty path in the original circuit.

    In the induction step, the prefix has already been mapped to an
    original-circuit path. The final deleted-circuit edge is independently
    mapped to another original-circuit path, and the two paths are then
    concatenated.
  *)
  have source_reaches_target_original:
    "(source_id, target_id)
     \<in>
     (edge_relation circuit)\<^sup>+"
    using source_reaches_target_after_deletion
  proof (induction rule: trancl_induct)

    case (base intermediate_id)

    (*
      A one-edge path after deletion corresponds either to the same
      original edge or to the original two-edge path through the deleted
      operation node.
    *)
    show ?case
      using
        valid_circuit
        operation_exists
        base.hyps
      by (rule delete_operation_edge_preserves_reachability)

  next

    case (step intermediate_id final_id)

    (*
      The induction hypothesis provides an original-circuit path from the
      fixed source to intermediate_id.
    *)
    have prefix_reachable_original:
      "(source_id, intermediate_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using step.IH .

    (*
      Map the final edge of the deleted-circuit path to a non-empty path
      from intermediate_id to final_id in the original circuit.
    *)
    have final_segment_reachable_original:
      "(intermediate_id, final_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using
        valid_circuit
        operation_exists
        step.hyps(2)
      by (rule delete_operation_edge_preserves_reachability)

    (*
      Concatenate the mapped prefix and final segment to obtain the full
      original-circuit reachability result.
    *)
    show ?case
      using
        prefix_reachable_original
        final_segment_reachable_original
      by (rule trancl_trans)
  qed

  show
    "node_pair \<in> (edge_relation circuit)\<^sup>+"
    using source_reaches_target_original node_pair
    by simp
qed

lemma reconnect_wire_successor_has_unique_predecessor:
  (* The successor of the reconnected operation retains exactly one
     predecessor on q. Its old predecessor, operation_node_id, is replaced
     by predecessor_id through the inserted bypass edge. *)
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

proof -

  have old_incoming_original:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have old_incoming_current:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation current_circuit q"
    using old_incoming_original same_relation
    by simp

  have every_old_predecessor_is_operation:
    "\<And>source_id.
       (source_id, successor_id)
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       source_id = operation_node_id"
    using unique_predecessor old_incoming_current
    unfolding has_unique_wire_predecessor_def
    by blast

  have relation_after:
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
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have bypass_exists:
    "(predecessor_id, successor_id)
       \<in> wire_edge_relation
            (reconnect_wire
               original_circuit
               operation_node_id
               q
               current_circuit)
            q"
    by (simp add: relation_after)

  show ?thesis
    using
      Diff_insert0
      Pair_inject
      every_old_predecessor_is_operation
      has_unique_wire_predecessor_def
      relation_after
    by auto
qed

lemma reconnect_wire_predecessor_has_unique_successor:
  (* The predecessor of the reconnected operation retains exactly one
     successor on q. Its old successor, operation_node_id, is replaced by
     successor_id through the inserted bypass edge. *)
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

proof -

  have old_outgoing_original:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have old_outgoing_current:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation current_circuit q"
    using old_outgoing_original same_relation
    by simp

  have every_old_successor_is_operation:
    "\<And>target_id.
       (predecessor_id, target_id)
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       target_id = operation_node_id"
    using unique_successor old_outgoing_current
    unfolding has_unique_wire_successor_def
    by blast

  have relation_after:
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
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have bypass_exists:
    "(predecessor_id, successor_id)
       \<in> wire_edge_relation
            (reconnect_wire
               original_circuit
               operation_node_id
               q
               current_circuit)
            q"
    by (simp add: relation_after)

  show ?thesis
    using
      every_old_successor_is_operation
      has_unique_wire_successor_def
      relation_after
    by auto
qed

lemma reconnect_wire_other_node_has_unique_predecessor:
  (* A node that is neither the deleted operation nor its successor keeps
     exactly the same incoming q-edges after reconnection. Therefore, its
     unique-predecessor property is preserved. *)
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

proof -
  let ?updated_circuit =
    "reconnect_wire
       original_circuit
       operation_node_id
       q
       current_circuit"

  have relation_after:
    "wire_edge_relation ?updated_circuit q =
       insert
         (predecessor_id, successor_id)
         (wire_edge_relation current_circuit q
            -
            {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have incoming_relation_iff:
    "\<And>source_id.
       (source_id, node_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (source_id, node_id)
         \<in> wire_edge_relation current_circuit q"
  proof -
    fix source_id

    show
      "(source_id, node_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (source_id, node_id)
         \<in> wire_edge_relation current_circuit q"
      using
        relation_after
        not_deleted
        not_successor
      by auto
  qed

  show ?thesis
    using has_unique_wire_predecessor_def incoming_relation_iff unique_predecessor
    by fastforce
qed

lemma reconnect_wire_other_node_has_unique_successor:
  (* A node that is neither the deleted operation nor its predecessor keeps
     exactly the same outgoing q-edges after reconnection. Therefore, its
     unique-successor property is preserved. *)
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

proof -

  let ?updated_circuit =
    "reconnect_wire
       original_circuit
       operation_node_id
       q
       current_circuit"

  have relation_after:
    "wire_edge_relation ?updated_circuit q =
       insert
         (predecessor_id, successor_id)
         (wire_edge_relation current_circuit q
            -
            {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have outgoing_relation_iff:
    "\<And>target_id.
       (node_id, target_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q"
  proof -
    fix target_id

    show
      "(node_id, target_id)
         \<in> wire_edge_relation ?updated_circuit q
       \<longleftrightarrow>
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q"
      using
        relation_after
        not_deleted
        not_predecessor
      by auto
  qed

  have old_exists:
    "\<exists>target_id.
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q"
    using unique_successor
    unfolding has_unique_wire_successor_def
    by blast

  have old_unique:
    "\<And>target_id target_id'.
       (node_id, target_id)
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       (node_id, target_id')
         \<in> wire_edge_relation current_circuit q
       \<Longrightarrow>
       target_id = target_id'"
    using unique_successor
    unfolding has_unique_wire_successor_def
    by blast

  show ?thesis
    using
      has_unique_wire_successor_def
      old_exists
      old_unique
      outgoing_relation_iff
    by auto
qed

lemma reconnect_wire_preserves_remaining_node_degrees:
  (* Reconnecting predecessor -> operation -> successor preserves the unique
     predecessor and successor properties of every node other than the
     deleted operation.

     There are three cases:
       1. node_id is the predecessor: its outgoing edge is redirected;
       2. node_id is the successor: its incoming edge is redirected;
       3. node_id is neither: both incident edge sets remain unchanged.
  *)
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
  by (metis
      predecessor
      reconnect_wire_other_node_has_unique_predecessor
      reconnect_wire_other_node_has_unique_successor
      reconnect_wire_predecessor_has_unique_successor
      reconnect_wire_successor_has_unique_predecessor
      remaining_node
      same_relation
      successor
      unique_predecessor
      unique_successor)

lemma fold_reconnect_preserves_operation_degrees:
  (* Reconnecting a distinct list of wires preserves the predecessor and
     successor degrees of a remaining node on q.

     Reconnections before q do not alter q's wire relation. The reconnection
     of q preserves the node's degrees using the local theorem. Reconnections
     after q again leave q's relation unchanged.
  *)
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

proof -
  obtain before after where
    qs_decomposition:
      "qs = before @ q # after"
    using used_wire
    by (meson split_list)

  have q_not_in_before:
    "q \<notin> set before"
    using distinct_wires qs_decomposition
    by auto

  have q_not_in_after:
    "q \<notin> set after"
    using distinct_wires qs_decomposition
    by auto

  let ?before_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       before
       circuit"

  let ?q_circuit =
    "reconnect_wire
       circuit
       operation_node_id
       q
       ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q =
       wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_before
    by simp

  have predecessor_before:
    "has_unique_wire_predecessor
       ?before_circuit q node_id"
    using unique_predecessor before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have successor_before:
    "has_unique_wire_successor
       ?before_circuit q node_id"
    using unique_successor before_same_relation
    unfolding has_unique_wire_successor_def
    by simp

  have degrees_after_q:
    "has_unique_wire_predecessor
       ?q_circuit q node_id
     \<and>
     has_unique_wire_successor
       ?q_circuit q node_id"
    using
      before_same_relation
      predecessor
      predecessor_before
      predecessor_not_deleted
      predecessor_not_successor
      reconnect_wire_preserves_remaining_node_degrees
      remaining_node
      successor
      successor_before
      successor_not_deleted
    by simp
    
  have after_same_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
     =
     wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_after
    by simp
    
  have predecessor_after:
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
       node_id"
    using
      degrees_after_q
      after_same_relation
      has_unique_wire_predecessor_def
    by simp

  have successor_after:
    "has_unique_wire_successor
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
       node_id"
    using degrees_after_q after_same_relation
    unfolding has_unique_wire_successor_def
    by auto

  show ?thesis
    using
      predecessor_after
      successor_after
      qs_decomposition
    by simp

qed

lemma delete_operation_preserves_acyclicity:
  (* Deleting an operation from a valid quantum circuit preserves
     acyclicity.

     Assume, for contradiction, that the circuit obtained after deletion
     contains a directed cycle. Such a cycle gives a non-empty path from
     some node back to itself.

     By delete_operation_reachability_preserved, the same node was already
     reachable from itself in the original circuit. This contradicts the
     original circuit's acyclicity. Therefore, deleting the operation
     cannot create a directed cycle.
  *)
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

proof -

  have original_acyclic:
    "acyclic (edge_relation circuit)"
    using valid_circuit
    unfolding is_valid_circuit_def
              is_acyclic_circuit_def
    by simp

  have reachability_preserved:
    "(edge_relation
        (delete_operation circuit operation_node_id))\<^sup>+
       \<subseteq>
     (edge_relation circuit)\<^sup>+"
    using valid_circuit operation_exists
    by (rule delete_operation_reachability_preserved)

  show ?thesis
    unfolding is_acyclic_circuit_def acyclic_def
  proof
    fix node_id

    show
      "(node_id, node_id)
         \<notin> (edge_relation
              (delete_operation circuit operation_node_id))\<^sup>+"
    proof
      assume cycle_after_deletion:
        "(node_id, node_id)
           \<in> (edge_relation
                (delete_operation circuit operation_node_id))\<^sup>+"

      then have cycle_before_deletion:
        "(node_id, node_id) \<in> (edge_relation circuit)\<^sup>+"
        using reachability_preserved
        by auto

      moreover have
        "(node_id, node_id) \<notin> (edge_relation circuit)\<^sup>+"
        using original_acyclic
        unfolding acyclic_def
        by simp

      ultimately show False
        by simp
    qed
  qed

qed

lemma delete_operation_preserves_unused_wire_relation:
  (* If the deleted operation does not use q, delete_operation never invokes
     reconnect_wire on q.

     The final node-table update removes the operation node but does not
     modify the edge set. Therefore, the q-labelled edge relation is
     exactly the same before and after deletion.
  *)
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

proof -
  have folded_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
       q
     =
     wire_edge_relation circuit q"
    using unused_wire
    by (rule fold_reconnect_preserves_other_wire_relation)

  show ?thesis
    using
      operation_exists
      folded_relation 
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp
qed

lemma delete_operation_preserves_linear_unused_wire:
  (* If the deleted operation does not use q, deletion does not modify
     the q-labelled edge relation.

     reconnect_wire is applied only to qubits in op_qargs op. Since q is
     absent from that list, no q-edge is removed or inserted. The deleted
     operation node also does not use q, so removing that node does not
     remove a node belonging to the q-wire.

     Consequently, every component of wire_is_linear on q is unchanged:
       - comparability;
       - the input boundary conditions;
       - the output boundary conditions;
       - unique predecessors and successors of operation nodes using q.
  *)
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

proof -
  assume original_linear:
    "wire_is_linear circuit q"

  let ?deleted =
    "delete_operation circuit operation_node_id"

  have same_wire_relation:
    "wire_edge_relation ?deleted q =
     wire_edge_relation circuit q"
    using operation_exists unused_wire
    by (rule delete_operation_preserves_unused_wire_relation)

  have deleted_node_does_not_use_q:
    "\<not> node_uses_qubit (OperationNode op) q"
    using unused_wire
    by simp

  have remaining_node_origin:
    "\<And>node_id node_value.
       nodes ?deleted node_id = Some node_value
       \<Longrightarrow>
       nodes circuit node_id = Some node_value"
  proof -
    fix node_id node_value

    assume node_after:
      "nodes ?deleted node_id = Some node_value"

    have node_id_not_deleted:
      "node_id \<noteq> operation_node_id"
    proof
      assume
        "node_id = operation_node_id"

      then have
        "nodes ?deleted node_id = None"
        using operation_exists
        by simp

      with node_after show False
        by simp
    qed

    show
      "nodes circuit node_id = Some node_value"
      using
        node_after
        node_id_not_deleted
        operation_exists
        fold_reconnect_wire_preserves_nodes
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed

  have original_q_node_survives:
    "\<And>node_id node_value.
       nodes circuit node_id = Some node_value
       \<Longrightarrow>
       node_uses_qubit node_value q
       \<Longrightarrow>
       nodes ?deleted node_id = Some node_value"
  proof -

    fix node_id node_value

    assume node_before:
      "nodes circuit node_id = Some node_value"

    assume uses_q:
      "node_uses_qubit node_value q"

    have node_id_not_deleted:
      "node_id \<noteq> operation_node_id"
    proof
      assume same_id:
        "node_id = operation_node_id"

      from node_before operation_exists same_id
      have
        "node_value = OperationNode op"
        by simp

      then have
        "node_uses_qubit (OperationNode op) q"
        using uses_q
        by simp

      with deleted_node_does_not_use_q
      show False
        by simp
    qed

    show
      "nodes ?deleted node_id = Some node_value"
      using
        node_before
        node_id_not_deleted
        operation_exists
        fold_reconnect_wire_preserves_nodes
      unfolding
        delete_operation_def
        Let_def
      by simp

  qed

  have comparable_after:
    "nodes_comparable_on_wire ?deleted q"
  proof -
    have comparable_before:
      "nodes_comparable_on_wire circuit q"
      using original_linear
      unfolding wire_is_linear_def
      by simp

    show ?thesis
      unfolding nodes_comparable_on_wire_def

    proof (intro allI impI)

      fix node_a node_b node_a_value node_b_value

      assume node_a_after:
        "nodes ?deleted node_a = Some node_a_value"

      assume node_b_after:
        "nodes ?deleted node_b = Some node_b_value"

      assume node_a_uses_q:
        "node_uses_qubit node_a_value q"

      assume node_b_uses_q:
        "node_uses_qubit node_b_value q"

      have node_a_before:
        "nodes circuit node_a = Some node_a_value"
        using node_a_after
        by (rule remaining_node_origin)

      have node_b_before:
        "nodes circuit node_b = Some node_b_value"
        using node_b_after
        by (rule remaining_node_origin)

      have original_comparison:
        "node_a = node_b
         \<or> wire_reaches circuit q node_a node_b
         \<or> wire_reaches circuit q node_b node_a"
        using
          comparable_before
          node_a_before
          node_b_before
          node_a_uses_q
          node_b_uses_q
        unfolding nodes_comparable_on_wire_def
        by blast

      show
        "node_a = node_b
         \<or> wire_reaches ?deleted q node_a node_b
         \<or> wire_reaches ?deleted q node_b node_a"
        using original_comparison same_wire_relation
        unfolding wire_reaches_def
        by simp

    qed

  qed

  have operation_nodes_after:
    "\<forall>node_id remaining_op.
       nodes ?deleted node_id = Some (OperationNode remaining_op)
       \<longrightarrow>
       node_uses_qubit (OperationNode remaining_op) q
       \<longrightarrow>
       has_unique_wire_predecessor ?deleted q node_id
       \<and>
       has_unique_wire_successor ?deleted q node_id"
  proof (intro allI impI)

    fix node_id remaining_op

    assume node_after:
      "nodes ?deleted node_id =
         Some (OperationNode remaining_op)"

    assume uses_q:
      "node_uses_qubit (OperationNode remaining_op) q"

    have node_before:
      "nodes circuit node_id =
         Some (OperationNode remaining_op)"
      using node_after
      by (rule remaining_node_origin)

    have original_operation_condition:
      "has_unique_wire_predecessor circuit q node_id
       \<and>
       has_unique_wire_successor circuit q node_id"
      using original_linear node_before uses_q
      unfolding wire_is_linear_def
      by blast

    show
      "has_unique_wire_predecessor ?deleted q node_id
       \<and>
       has_unique_wire_successor ?deleted q node_id"
      using original_operation_condition same_wire_relation
      unfolding
        has_unique_wire_predecessor_def
        has_unique_wire_successor_def
      by simp

  qed

  show
    "wire_is_linear ?deleted q"
    using
      original_linear
      comparable_after
      operation_nodes_after
      same_wire_relation
    unfolding
      wire_is_linear_def
      has_unique_wire_predecessor_def
      has_unique_wire_successor_def
    by simp
qed

lemma reconnect_wire_preserves_surviving_reachability:
  (* Contracting

         predecessor_id -> operation_node_id -> successor_id

     into

         predecessor_id -> successor_id

     preserves q-reachability between endpoints other than the contracted
     operation node.

     The uniqueness assumptions ensure that any path entering the contracted
     node must enter through predecessor_id, and any path leaving it must
     leave through successor_id. Hence every occurrence of the two-edge
     segment can be replaced by the bypass edge.
  *)
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

proof -

  let ?old_relation =
    "wire_edge_relation current_circuit q"

  let ?new_relation =
    "wire_edge_relation
       (reconnect_wire
          original_circuit
          operation_node_id
          q
          current_circuit)
       q"

  have predecessor_edge_original:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have predecessor_edge_current:
    "(predecessor_id, operation_node_id)
       \<in> ?old_relation"
    using predecessor_edge_original same_relation
    by simp

  have successor_edge_original:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have successor_edge_current:
    "(operation_node_id, successor_id)
       \<in> ?old_relation"
    using successor_edge_original same_relation
    by simp

  have every_operation_predecessor:
    "\<And>source_id.
       (source_id, operation_node_id) \<in> ?old_relation
       \<Longrightarrow>
       source_id = predecessor_id"
    using
      unique_operation_predecessor
      predecessor_edge_current
    unfolding has_unique_wire_predecessor_def
    by blast

  have every_operation_successor:
    "\<And>target_id.
       (operation_node_id, target_id) \<in> ?old_relation
       \<Longrightarrow>
       target_id = successor_id"
    using
      unique_operation_successor
      successor_edge_current
    unfolding has_unique_wire_successor_def
    by blast

  have relation_after:
    "?new_relation =
       insert
         (predecessor_id, successor_id)
         (?old_relation
            -
            {(predecessor_id, operation_node_id),
             (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    .

  have bypass_edge:
    "(predecessor_id, successor_id) \<in> ?new_relation"
    using relation_after
    by simp

  have surviving_edge_preserved:
    "\<And>source_id target_id.
       (source_id, target_id) \<in> ?old_relation
       \<Longrightarrow>
       source_id \<noteq> operation_node_id
       \<Longrightarrow>
       target_id \<noteq> operation_node_id
       \<Longrightarrow>
       (source_id, target_id) \<in> ?new_relation"
    using relation_after
    by auto

  have old_path:
    "(node_a, node_b) \<in> ?old_relation\<^sup>+"
    using old_reachability
    unfolding wire_reaches_def
    .

  have strengthened_path:
    "\<And>target_id.
       (node_a, target_id) \<in> ?old_relation\<^sup>+
       \<Longrightarrow>
       (target_id = operation_node_id
        \<longrightarrow>
          node_a = predecessor_id
          \<or>
          (node_a, predecessor_id) \<in> ?new_relation\<^sup>+)
       \<and>
       (target_id \<noteq> operation_node_id
        \<longrightarrow>
          (node_a, target_id) \<in> ?new_relation\<^sup>+)"
  proof -

    fix target_id

    assume old_target_path:
      "(node_a, target_id) \<in> ?old_relation\<^sup>+"

    show
      "(target_id = operation_node_id
        \<longrightarrow>
          node_a = predecessor_id
          \<or>
          (node_a, predecessor_id) \<in> ?new_relation\<^sup>+)
       \<and>
       (target_id \<noteq> operation_node_id
        \<longrightarrow>
          (node_a, target_id) \<in> ?new_relation\<^sup>+)"

      using old_target_path
    proof (induction rule: trancl_induct)

      case (base target_id)
      
      show ?case
        using
          base
          every_operation_predecessor
          source_survives
          surviving_edge_preserved
        by auto

    next

      case (step middle_id target_id)

      show ?case
        by (metis
            bypass_edge
            every_operation_predecessor
            every_operation_successor
            step.IH
            step.hyps(2)
            surviving_edge_preserved
            trancl.simps)
    qed
  qed

  have new_path:
    "(node_a, node_b) \<in> ?new_relation\<^sup>+"
    using
      strengthened_path[OF old_path]
      target_survives
    by blast

  show ?thesis
    using new_path
    unfolding wire_reaches_def
    .
qed

lemma fold_reconnect_preserves_surviving_reachability:
  (* In a distinct list of affected wires containing q, reconnections on
     wires other than q leave q's relation unchanged. The single
     reconnection on q contracts the deleted operation while preserving
     reachability between surviving endpoints.
  *)
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

proof -
  obtain before after where
    qs_decomposition:
      "qs = before @ q # after"
    using used_wire
    by (meson split_list)

  have q_not_in_before:
    "q \<notin> set before"
    using distinct_wires qs_decomposition
    by auto

  have q_not_in_after:
    "q \<notin> set after"
    using distinct_wires qs_decomposition
    by auto

  let ?before_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       before
       circuit"

  let ?q_circuit =
    "reconnect_wire
       circuit
       operation_node_id
       q
       ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q =
       wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_before
    by simp

  have predecessor_before:
    "has_unique_wire_predecessor
       ?before_circuit q operation_node_id"
    using
      unique_operation_predecessor
      before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have successor_before:
    "has_unique_wire_successor
       ?before_circuit q operation_node_id"
    using
      unique_operation_successor
      before_same_relation
    unfolding has_unique_wire_successor_def
    by auto

  have reachability_before:
    "wire_reaches ?before_circuit q node_a node_b"
    using
      old_reachability
      before_same_relation
    unfolding wire_reaches_def
    by simp

  have reachability_after_q:
    "wire_reaches ?q_circuit q node_a node_b"
    using
      before_same_relation
      predecessor
      predecessor_before
      reachability_before
      reconnect_wire_preserves_surviving_reachability
      source_survives
      successor
      successor_before
      target_survives
    by simp

  have after_same_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
     =
     wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation
      q_not_in_after
    by simp

  have reachability_after:
    "wire_reaches
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
       node_a
       node_b"
    using
      reachability_after_q
      after_same_relation
    unfolding wire_reaches_def
    by simp

  show ?thesis
    using
      reachability_after
      qs_decomposition
    by simp
qed

lemma delete_operation_preserves_surviving_wire_reachability:
  (* Deleting an operation preserves q-reachability between any two
     surviving endpoints on a wire used by that operation.

     The fold contracts the operation on every used wire. The final update
     removes only the operation from the node table and does not alter the
     already-reconnected edge relation.
  *)
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

proof -
  have unique_operation_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  have unique_operation_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_relation_id where
    predecessor_relation:
      "(predecessor_relation_id, operation_node_id)
         \<in> wire_edge_relation circuit q"
    using unique_operation_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_relation_id where
    successor_relation:
      "(operation_node_id, successor_relation_id)
         \<in> wire_edge_relation circuit q"
    using unique_operation_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire
       circuit operation_node_id q
     \<noteq> None"
    using predecessor_relation
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  obtain predecessor_id where
    predecessor:
      "predecessor_on_wire
         circuit operation_node_id q =
       Some predecessor_id"
    using predecessor_not_none
    by (cases
        "predecessor_on_wire
           circuit operation_node_id q")
       auto

  have successor_not_none:
    "successor_on_wire
       circuit operation_node_id q
     \<noteq> None"
    using successor_relation
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  obtain successor_id where
    successor:
      "successor_on_wire
         circuit operation_node_id q =
       Some successor_id"
    using successor_not_none
    by (cases
        "successor_on_wire
           circuit operation_node_id q")
       auto

  have valid_operation:
    "is_valid_operation op"
    using
      valid_circuit
      operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_wires:
    "distinct (op_qargs op)"
    using valid_operation
    unfolding is_valid_operation_def
    by auto

  let ?reconnected_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       (op_qargs op)
       circuit"

  have reachability_after_fold:
    "wire_reaches
       ?reconnected_circuit
       q
       node_a
       node_b"
    using
      fold_reconnect_preserves_surviving_reachability
      unique_operation_predecessor
      unique_operation_successor
      predecessor
      successor
      old_reachability
      source_survives
      target_survives
      distinct_wires
      used_wire
    by simp

  have relation_after_delete:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation
       ?reconnected_circuit
       q"
    using operation_exists
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp

  show ?thesis
    using
      reachability_after_fold
      relation_after_delete
    unfolding wire_reaches_def
    by simp
qed

lemma delete_operation_used_wire_preserves_comparability:
  (* Deleting an operation that uses q preserves comparability among all
     remaining nodes on q.

     In the original linear wire, every pair of q-nodes is ordered by
     q-reachability. Deletion contracts

         predecessor \<rightarrow> operation_node_id \<rightarrow> successor

     into

         predecessor \<rightarrow> successor.

     Any original path between two remaining q-nodes either avoids the
     deleted node and remains unchanged, or passes through the deleted
     node and is shortened through the new bypass edge.

     Therefore, every pair of remaining q-nodes remains comparable.
  *)
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

proof -
  have original_comparability:
    "nodes_comparable_on_wire circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  show ?thesis
    unfolding nodes_comparable_on_wire_def
  proof (intro allI impI)

    fix node_a node_b node_a_value node_b_value

    assume node_a_exists_after:
      "nodes
         (delete_operation circuit operation_node_id)
         node_a
       =
       Some node_a_value"

    assume node_b_exists_after:
      "nodes
         (delete_operation circuit operation_node_id)
         node_b
       =
       Some node_b_value"

    assume node_a_uses_q:
      "node_uses_qubit node_a_value q"

    assume node_b_uses_q:
      "node_uses_qubit node_b_value q"

    have node_a_survives:
      "node_a \<noteq> operation_node_id"
      using
        node_a_exists_after
        operation_exists
      by auto

    have node_b_survives:
      "node_b \<noteq> operation_node_id"
      using
        node_b_exists_after
        operation_exists
      by auto

    have node_a_exists_before:
      "nodes circuit node_a = Some node_a_value"
      using
        node_a_exists_after
        node_a_survives
        operation_exists
      by auto

    have node_b_exists_before:
      "nodes circuit node_b = Some node_b_value"
      using
        node_b_exists_after
        node_b_survives
        operation_exists
      by auto

    have comparable_before:
      "node_a = node_b
       \<or> wire_reaches circuit q node_a node_b
       \<or> wire_reaches circuit q node_b node_a"
      using
        original_comparability
        node_a_exists_before
        node_b_exists_before
        node_a_uses_q
        node_b_uses_q
      unfolding nodes_comparable_on_wire_def
      by blast

    show
      "node_a = node_b
       \<or>
       wire_reaches
         (delete_operation circuit operation_node_id)
         q
         node_a
         node_b
       \<or>
       wire_reaches
         (delete_operation circuit operation_node_id)
         q
         node_b
         node_a"
      using
        comparable_before
        delete_operation_preserves_surviving_wire_reachability
        node_a_survives
        node_b_survives
        operation_exists
        original_linear
        used_wire
        valid_circuit
      by blast
  qed
qed

lemma delete_operation_used_wire_preserves_input_boundary:
  (* Deleting an operation preserves the input boundary on every wire used
     by that operation.

     Since the original wire is linear, the operation node has exactly one
     predecessor and one successor on q. The operation is valid, so its
     qubit list is distinct. Therefore, the fold reconnects q exactly once,
     preserving the input boundary, while reconnections on the other wires
     do not affect q. Removing the operation from the node table afterward
     does not change the edge relation.
  *)
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

proof -

  have no_input_predecessor:
    "\<nexists>predecessor_id.
       (predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have unique_input_successor:
    "has_unique_wire_successor
       circuit q (get_input_node_id q)"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have operation_has_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have operation_has_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_id where predecessor_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation circuit q"
    using operation_has_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_id where successor_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation circuit q"
    using operation_has_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire circuit operation_node_id q \<noteq> None"
    using predecessor_edge
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_predecessor where predecessor:
    "predecessor_on_wire circuit operation_node_id q =
       Some selected_predecessor"
    by (cases "predecessor_on_wire circuit operation_node_id q") auto

  have successor_not_none:
    "successor_on_wire circuit operation_node_id q \<noteq> None"
    using successor_edge
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_successor where successor:
    "successor_on_wire circuit operation_node_id q =
       Some selected_successor"
    by (cases "successor_on_wire circuit operation_node_id q") auto

  have valid_operation:
    "is_valid_operation op"
    using valid_circuit operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_wires:
    "distinct (op_qargs op)"
    using
      valid_operation
      are_well_formed_operation_nodes_def
      is_valid_circuit_def
      is_valid_operation_def
      is_well_formed_circuit_def
      operation_exists
      operation_in_circuit_def
      valid_circuit
    by blast

  let ?reconnected_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       (op_qargs op)
       circuit"

  have boundary_after_reconnection:
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation ?reconnected_circuit q)
     \<and>
     has_unique_wire_successor
       ?reconnected_circuit
       q
       (get_input_node_id q)"
    using
      fold_reconnect_preserves_input_boundary[
        OF
          no_input_predecessor
          unique_input_successor
          predecessor
          successor
          distinct_wires
          used_wire]
    by simp

  have deleted_wire_relation:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation ?reconnected_circuit q"
    
    using operation_exists
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp

  show ?thesis
    using boundary_after_reconnection deleted_wire_relation
    unfolding has_unique_wire_successor_def
    by auto

qed

lemma reconnect_wire_preserves_output_boundary:
  (* Reconnecting predecessor -> operation_node_id -> successor into
     predecessor -> successor preserves the output boundary of wire q.

     The original output node has exactly one incoming q-edge and no
     outgoing q-edge. The bypass edge cannot leave the output node. If the
     output node is the successor, its old incoming edge from
     operation_node_id is replaced by exactly one incoming edge from
     predecessor_id. Otherwise, its incoming edge is unaffected.
  *)
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

proof -
  have incoming_operation_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have operation_not_output:
    "operation_node_id \<noteq> get_output_node_id q"
  proof
    assume
      "operation_node_id = get_output_node_id q"

    then have
      "(get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have predecessor_not_output:
    "predecessor_id \<noteq> get_output_node_id q"
  proof
    assume
      "predecessor_id = get_output_node_id q"

    then have
      "(get_output_node_id q, operation_node_id)
         \<in> wire_edge_relation circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have relation_after:
    "wire_edge_relation
       (reconnect_wire
          circuit
          operation_node_id
          q
          circuit)
       q
     =
     insert
       (predecessor_id, successor_id)
       (wire_edge_relation circuit q
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  show ?thesis
    using
      unique_output_predecessor
      no_output_successor
      outgoing_operation_edge
      operation_not_output
      predecessor_not_output
      relation_after
    unfolding has_unique_wire_predecessor_def
    by auto

qed

lemma reconnect_wire_preserves_output_boundary_from_same_relation:
  (* During a fold, predecessor and successor are looked up in the fixed
     original circuit, while the edge rewrite is applied to the current
     accumulator.

     If the q-edge relation of the accumulator is the same as that of the
     original circuit, reconnecting q preserves the output boundary.
  *)
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

proof -
  have incoming_operation_edge_original:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation original_circuit q"
    using predecessor_on_wire_correct[OF predecessor]
    unfolding wire_edge_relation_def
    by simp

  have incoming_operation_edge:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation current_circuit q"
    using incoming_operation_edge_original same_relation
    by simp

  have outgoing_operation_edge_original:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation original_circuit q"
    using successor_on_wire_correct[OF successor]
    unfolding wire_edge_relation_def
    by simp

  have outgoing_operation_edge:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation current_circuit q"
    using outgoing_operation_edge_original same_relation
    by simp

  have operation_not_output:
    "operation_node_id \<noteq> get_output_node_id q"
  proof
    assume
      operation_is_output:
        "operation_node_id = get_output_node_id q"

    then have
      "(get_output_node_id q, successor_id)
         \<in> wire_edge_relation current_circuit q"
      using outgoing_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have predecessor_not_output:
    "predecessor_id \<noteq> get_output_node_id q"
  proof
    assume
      predecessor_is_output:
        "predecessor_id = get_output_node_id q"

    then have
      "(get_output_node_id q, operation_node_id)
         \<in> wire_edge_relation current_circuit q"
      using incoming_operation_edge
      by simp

    then show False
      using no_output_successor
      by blast
  qed

  have relation_after:
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
          -
          {(predecessor_id, operation_node_id),
           (operation_node_id, successor_id)})"
    using
      reconnect_wire_successor_predecessor_characterisation[
        OF predecessor successor]
    by simp

  show ?thesis
    using
      unique_output_predecessor
      no_output_successor
      outgoing_operation_edge
      operation_not_output
      predecessor_not_output
      relation_after
    unfolding has_unique_wire_predecessor_def
    by auto
qed

lemma fold_reconnect_preserves_output_boundary:
  (* In a distinct list of affected wires containing q, reconnections on
     wires before and after q leave q's edge relation unchanged. The single
     reconnection of q preserves its output boundary. *)
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

proof -
  obtain before after where
    qs_decomposition:
      "qs = before @ q # after"
    using used_wire
    by (meson split_list)

  have q_not_in_before:
    "q \<notin> set before"
    using distinct_wires qs_decomposition
    by auto

  have q_not_in_after:
    "q \<notin> set after"
    using distinct_wires qs_decomposition
    by auto

  let ?before_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       before
       circuit"

  let ?q_circuit =
    "reconnect_wire
       circuit
       operation_node_id
       q
       ?before_circuit"

  have before_same_relation:
    "wire_edge_relation ?before_circuit q =
       wire_edge_relation circuit q"
    using
      fold_reconnect_preserves_other_wire_relation[
        where original_circuit = circuit
          and operation_node_id = operation_node_id
          and qs = before
          and current_circuit = circuit
          and r = q,
        OF q_not_in_before]
    by simp

  have unique_output_predecessor_before:
    "has_unique_wire_predecessor
       ?before_circuit q (get_output_node_id q)"
    using
      unique_output_predecessor
      before_same_relation
    unfolding has_unique_wire_predecessor_def
    by auto

  have no_output_successor_before:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation ?before_circuit q"
    using
      no_output_successor
      before_same_relation
    by simp

  have boundary_after_q:
    "has_unique_wire_predecessor
       ?q_circuit
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation ?q_circuit q)"
    using
      reconnect_wire_preserves_output_boundary_from_same_relation[
        OF
          unique_output_predecessor_before
          no_output_successor_before
          before_same_relation
          predecessor
          successor]
    by simp

  have after_same_relation:
    "wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          after
          ?q_circuit)
       q
     =
     wire_edge_relation ?q_circuit q"
    using
      fold_reconnect_preserves_other_wire_relation[
        where original_circuit = circuit
          and operation_node_id = operation_node_id
          and qs = after
          and current_circuit = ?q_circuit
          and r = q,
        OF q_not_in_after]
    by simp

  show ?thesis
    using
      boundary_after_q
      after_same_relation
      qs_decomposition
    unfolding has_unique_wire_predecessor_def
    by auto
qed

lemma delete_operation_used_wire_preserves_output_boundary:
  (* Deleting an operation on wire q preserves the output boundary of q.

     The fold reconnects every affected wire. Since reconnections on other
     wires do not affect q, and reconnecting q preserves its output
     boundary, the final removal of the operation node from the node table
     leaves the output boundary unchanged.
  *)
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

proof -
  have unique_output_predecessor:
    "has_unique_wire_predecessor
       circuit q (get_output_node_id q)"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have no_output_successor:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
    using original_linear
    unfolding wire_is_linear_def
    by blast

  have operation_has_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have operation_has_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using original_linear operation_exists used_wire
    unfolding wire_is_linear_def
    by auto

  have predecessor_exists:
    "\<exists>predecessor_id.
       predecessor_on_wire
         circuit
         operation_node_id
         q
       =
       Some predecessor_id"
  
  proof -
    obtain predecessor_id where
      predecessor_relation:
        "(predecessor_id, operation_node_id)
           \<in> wire_edge_relation circuit q"
      using operation_has_predecessor
      unfolding has_unique_wire_predecessor_def
      by blast

    have incoming_edge_exists:
      "make_edge predecessor_id operation_node_id q
         \<in> edges circuit"
      using predecessor_relation
      unfolding wire_edge_relation_def
      by simp

    have incoming_exists:
      "\<exists>incoming \<in> edges circuit.
         edge_target incoming = operation_node_id
         \<and>
         edge_wire incoming = q"
    proof
      show
        "make_edge predecessor_id operation_node_id q
           \<in> edges circuit"
        using incoming_edge_exists .

      show
        "edge_target
           (make_edge predecessor_id operation_node_id q)
           =
           operation_node_id
         \<and>
         edge_wire
           (make_edge predecessor_id operation_node_id q)
           =
           q"
        unfolding make_edge_def
        by simp
    qed

    show ?thesis
      using incoming_exists
      unfolding
        predecessor_on_wire_def
        incoming_edge_def
      by simp
  qed

  obtain predecessor_id where
    predecessor:
      "predecessor_on_wire
         circuit
         operation_node_id
         q
       =
       Some predecessor_id"
    using predecessor_exists
    by blast

  have successor_exists:
    "\<exists>successor_id.
       successor_on_wire
         circuit
         operation_node_id
         q
       =
       Some successor_id"
  proof -

    obtain successor_id where
      successor_relation:
        "(operation_node_id, successor_id)
           \<in> wire_edge_relation circuit q"
      using operation_has_successor
      unfolding has_unique_wire_successor_def
      by blast

    have outgoing_edge_exists:
      "make_edge operation_node_id successor_id q
         \<in> edges circuit"
      using successor_relation
      unfolding wire_edge_relation_def
      by simp

    have outgoing_exists:
      "\<exists>outgoing \<in> edges circuit.
         edge_source outgoing = operation_node_id
         \<and>
         edge_wire outgoing = q"
    proof
      show
        "make_edge operation_node_id successor_id q
           \<in> edges circuit"
        using outgoing_edge_exists .

      show
        "edge_source
           (make_edge operation_node_id successor_id q)
           =
           operation_node_id
         \<and>
         edge_wire
           (make_edge operation_node_id successor_id q)
           =
           q"
        unfolding make_edge_def
        by simp
    qed

    show ?thesis
      using outgoing_exists
      unfolding
        successor_on_wire_def
        outgoing_edge_def
      by simp
  qed

  obtain successor_id where
    successor:
      "successor_on_wire
         circuit
         operation_node_id
         q
       =
       Some successor_id"
    using successor_exists
    by blast


  have valid_operation:
    "is_valid_operation op"
    using
      valid_circuit
      operation_exists
      are_well_formed_operation_nodes_def
      is_valid_operation_def
      is_well_formed_circuit_def
      operation_in_circuit_def
    unfolding
      is_valid_circuit_def
      is_valid_operation_def
    by simp

  then have distinct_wires:
    "distinct (op_qargs op)"
    unfolding is_valid_operation_def
    by auto

  have boundary_after_fold:
    "has_unique_wire_predecessor
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
       q
       (get_output_node_id q)
     \<and>
     (\<nexists>successor_id.
        (get_output_node_id q, successor_id)
          \<in> wire_edge_relation
               (fold
                  (reconnect_wire circuit operation_node_id)
                  (op_qargs op)
                  circuit)
               q)"
    using
      fold_reconnect_preserves_output_boundary[
        OF
          unique_output_predecessor
          no_output_successor
          predecessor
          successor
          distinct_wires
          used_wire]
    by simp

  have relation_preserved:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q =
     wire_edge_relation
       (fold
          (reconnect_wire circuit operation_node_id)
          (op_qargs op)
          circuit)
       q"
    unfolding
      delete_operation_def
    using operation_exists
    by (simp add: Let_def wire_edge_relation_def)

  show ?thesis
    using
      boundary_after_fold
      relation_preserved
    unfolding has_unique_wire_predecessor_def
    by auto

qed

lemma delete_operation_used_wire_preserves_operation_degrees:
  (* Every remaining operation node using q retains exactly one immediate
     predecessor and exactly one immediate successor on q.

     Nodes not adjacent to the deleted operation keep their incident
     q-edges unchanged.

     The deleted operation's predecessor loses its edge to the deleted
     node but gains the new bypass edge to the deleted node's successor.

     Similarly, the deleted operation's successor loses its incoming edge
     from the deleted node but gains the new bypass edge from the deleted
     node's predecessor.

     Since the original q-wire was linear, these rewrites preserve degree
     one and introduce no branching.
  *)
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

proof (intro allI impI)

  fix node_id remaining_op

  assume remaining_operation_exists:
    "nodes
       (delete_operation circuit operation_node_id)
       node_id
     =
     Some (OperationNode remaining_op)"

  assume remaining_operation_uses_q:
    "node_uses_qubit (OperationNode remaining_op) q"

  have remaining_node:
    "node_id \<noteq> operation_node_id"
    using
      operation_exists
      remaining_operation_exists
    by auto

  have remaining_operation_exists_originally:
    "nodes circuit node_id =
       Some (OperationNode remaining_op)"
    using
      operation_exists
      remaining_node
      remaining_operation_exists
    by simp

  have remaining_unique_predecessor:
    "has_unique_wire_predecessor
       circuit q node_id"
    using
      original_linear
      remaining_operation_exists_originally
      remaining_operation_uses_q
    unfolding wire_is_linear_def
    by blast

  have remaining_unique_successor:
    "has_unique_wire_successor
       circuit q node_id"
    using
      original_linear
      remaining_operation_exists_originally
      remaining_operation_uses_q
    unfolding wire_is_linear_def
    by blast

  have deleted_operation_has_predecessor:
    "has_unique_wire_predecessor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  have deleted_operation_has_successor:
    "has_unique_wire_successor
       circuit q operation_node_id"
    using
      original_linear
      operation_exists
      used_wire
    unfolding wire_is_linear_def
    by auto

  obtain predecessor_id where predecessor_relation:
    "(predecessor_id, operation_node_id)
       \<in> wire_edge_relation circuit q"
    using deleted_operation_has_predecessor
    unfolding has_unique_wire_predecessor_def
    by blast

  obtain successor_id where successor_relation:
    "(operation_node_id, successor_id)
       \<in> wire_edge_relation circuit q"
    using deleted_operation_has_successor
    unfolding has_unique_wire_successor_def
    by blast

  have predecessor_not_none:
    "predecessor_on_wire
       circuit operation_node_id q
     \<noteq>
     None"
    using predecessor_relation
    unfolding
      predecessor_on_wire_def
      incoming_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_predecessor where predecessor:
    "predecessor_on_wire
       circuit operation_node_id q
     =
     Some selected_predecessor"
    by (cases
        "predecessor_on_wire
           circuit operation_node_id q")
       auto

  have successor_not_none:
    "successor_on_wire
       circuit operation_node_id q
     \<noteq>
     None"
    using successor_relation
    unfolding
      successor_on_wire_def
      outgoing_edge_def
      wire_edge_relation_def
      make_edge_def
    by force

  then obtain selected_successor where successor:
    "successor_on_wire
       circuit operation_node_id q
     =
     Some selected_successor"
    by (cases
        "successor_on_wire
           circuit operation_node_id q")
       auto

  have original_acyclic:
    "is_acyclic_circuit circuit"
    using valid_circuit
    unfolding is_valid_circuit_def
    by simp

  have predecessor_not_deleted:
    "selected_predecessor \<noteq> operation_node_id"
  proof
    assume predecessor_is_deleted:
      "selected_predecessor = operation_node_id"

    have self_loop_edge:
      "make_edge
         operation_node_id
         operation_node_id
         q
       \<in>
       edges circuit"
      using
        predecessor_on_wire_correct[OF predecessor]
        predecessor_is_deleted
      by simp

    have self_loop_relation:
      "(operation_node_id, operation_node_id)
       \<in>
       edge_relation circuit"
      using self_loop_edge
      unfolding edge_relation_def make_edge_def
      by force

    have self_reachable:
      "(operation_node_id, operation_node_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using self_loop_relation
      by (rule r_into_trancl)

    show False
      using original_acyclic self_reachable
      unfolding is_acyclic_circuit_def acyclic_def
      by simp
  qed

  have successor_not_deleted:
    "selected_successor \<noteq> operation_node_id"
  proof
    assume successor_is_deleted:
      "selected_successor = operation_node_id"

    have self_loop_edge:
      "make_edge
         operation_node_id
         operation_node_id
         q
       \<in>
       edges circuit"
      using
        successor_on_wire_correct[OF successor]
        successor_is_deleted
      by simp

    have self_loop_relation:
      "(operation_node_id, operation_node_id)
       \<in>
       edge_relation circuit"
      using self_loop_edge
      unfolding edge_relation_def make_edge_def
      by force

    have self_reachable:
      "(operation_node_id, operation_node_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using self_loop_relation
      by (rule r_into_trancl)

    show False
      using original_acyclic self_reachable
      unfolding is_acyclic_circuit_def acyclic_def
      by simp
  qed

  have predecessor_not_successor:
    "selected_predecessor \<noteq> selected_successor"
  proof
    assume endpoints_equal:
      "selected_predecessor = selected_successor"

    have incoming_edge:
      "make_edge
         selected_predecessor
         operation_node_id
         q
       \<in>
       edges circuit"
      using predecessor_on_wire_correct[OF predecessor]
      .

    have outgoing_edge:
      "make_edge
         operation_node_id
         selected_successor
         q
       \<in>
       edges circuit"
      using successor_on_wire_correct[OF successor]
      .

    have incoming_relation:
      "(selected_predecessor, operation_node_id)
       \<in>
       edge_relation circuit"
      using incoming_edge
      unfolding edge_relation_def make_edge_def
      by force

    have outgoing_relation:
      "(operation_node_id, selected_successor)
       \<in>
       edge_relation circuit"
      using outgoing_edge
      unfolding edge_relation_def make_edge_def
      by force

    have incoming_path:
      "(selected_predecessor, operation_node_id)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using incoming_relation
      by (rule r_into_trancl)

    have outgoing_path:
      "(operation_node_id, selected_successor)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using outgoing_relation
      by (rule r_into_trancl)

    have endpoint_cycle:
      "(selected_predecessor, selected_successor)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using incoming_path outgoing_path
      by (rule trancl_trans)

    then have self_reachable:
      "(selected_predecessor, selected_predecessor)
       \<in>
       (edge_relation circuit)\<^sup>+"
      using endpoints_equal
      by simp

    show False
      using
        original_acyclic
        self_reachable
      unfolding
        is_acyclic_circuit_def
        acyclic_def
      by simp
  qed

  have valid_operation:
    "is_valid_operation op"
    using
      valid_circuit
      operation_exists
    unfolding
      is_valid_circuit_def
      is_well_formed_circuit_def
      are_well_formed_operation_nodes_def
      operation_in_circuit_def
    by blast

  have distinct_wires:
    "distinct (op_qargs op)"
    using valid_operation
    unfolding is_valid_operation_def
    by auto

  let ?reconnected_circuit =
    "fold
       (reconnect_wire circuit operation_node_id)
       (op_qargs op)
       circuit"

  have degrees_after_reconnection:
    "has_unique_wire_predecessor
       ?reconnected_circuit
       q
       node_id
     \<and>
     has_unique_wire_successor
       ?reconnected_circuit
       q
       node_id"
    using
      distinct_wires
      fold_reconnect_preserves_operation_degrees
      predecessor
      predecessor_not_deleted
      predecessor_not_successor
      remaining_node
      remaining_unique_predecessor
      remaining_unique_successor
      successor
      successor_not_deleted
      used_wire
    by simp

  have deleted_wire_relation:
    "wire_edge_relation
       (delete_operation circuit operation_node_id)
       q
     =
     wire_edge_relation
       ?reconnected_circuit
       q"
    using operation_exists
    unfolding
      delete_operation_def
      wire_edge_relation_def
      Let_def
    by simp

  show
    "has_unique_wire_predecessor
       (delete_operation circuit operation_node_id)
       q
       node_id
     \<and>
     has_unique_wire_successor
       (delete_operation circuit operation_node_id)
       q
       node_id"
    using
      degrees_after_reconnection
      deleted_wire_relation
    unfolding
      has_unique_wire_predecessor_def
      has_unique_wire_successor_def
    by auto

qed

lemma delete_operation_preserves_linear_used_wire:
  (* If the deleted operation uses q, deletion contracts one internal node
     of the linear q-wire.

     In the original circuit, wire linearity gives the deleted node a
     unique predecessor and a unique successor on q:

         predecessor \<rightarrow> operation_node_id \<rightarrow> successor.

     reconnect_wire removes those two edges and inserts:

         predecessor \<rightarrow> successor.

     Thus:
       - the input still has no predecessor and one successor;
       - the output still has one predecessor and no successor;
       - every remaining operation node has one predecessor and one
         successor;
       - no branch is introduced;
       - comparability of all remaining q-nodes is preserved.

     Hence the contracted q-wire remains linear.
  *)
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

proof -
  assume original_linear:
    "wire_is_linear circuit q"

  have comparability_after:
    "nodes_comparable_on_wire
       (delete_operation circuit operation_node_id)
       q"
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_comparability)

  have input_boundary_after:
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
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_input_boundary)

  have output_boundary_after:
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
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_output_boundary)

  have operation_degrees_after:
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
    using
      valid_circuit
      operation_exists
      used_wire
      original_linear
    by (rule delete_operation_used_wire_preserves_operation_degrees)

  show
    "wire_is_linear
       (delete_operation circuit operation_node_id)
       q"
    using
      comparability_after
      input_boundary_after
      output_boundary_after
      operation_degrees_after
    unfolding wire_is_linear_def
    by simp
qed

lemma delete_operation_preserves_wire_is_linear:
  (* Deleting an operation preserves the linear structure of one valid wire.

     There are two cases for wire q:

       1. The deleted operation does not use q.

          In this case, delete_operation does not reconnect q. The edges
          on q remain unchanged, and removing an operation that does not
          use q does not remove any node belonging to q. Therefore, the
          original linear chain on q is preserved.

       2. The deleted operation uses q.

          Since the original wire is linear, operation_node_id has exactly
          one predecessor and exactly one successor on q. Deletion removes

              predecessor \<rightarrow> operation_node_id
              operation_node_id \<rightarrow> successor

          and replaces them with

              predecessor \<rightarrow> successor.

          This contracts one internal node of the wire chain. It does not
          introduce branching, disconnect the wire, alter the boundary-node
          conditions, or destroy comparability among the remaining nodes.

     Therefore, every valid wire remains linear after deletion.
  *)
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
  by (metis
      all_wires_linear_def
      delete_operation_preserves_linear_unused_wire
      delete_operation_preserves_linear_used_wire
      delete_operation_preserves_num_qubits
      is_valid_circuit_def
      operation_exists
      qubit_in_circuit_def
      valid_circuit
      valid_wire_after)

lemma delete_operation_preserves_wire_linearity:
  (* Deleting an operation preserves linearity of every circuit wire.

     The number of qubits is unchanged by deletion. Hence, any qubit that
     is valid after deletion was also valid before deletion.

     The original circuit satisfies all_wires_linear because it is a valid
     circuit. For an arbitrary valid wire q, the preceding helper theorem
     shows that deleting operation_node_id preserves wire_is_linear on q.

     Since q was arbitrary, every valid wire in the resulting circuit is
     linear.
  *)
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

proof -
  show ?thesis
    unfolding all_wires_linear_def

  proof (intro allI impI)

    fix q

    assume valid_wire_after:
      "qubit_in_circuit
         (delete_operation circuit operation_node_id)
         q"

    show
      "wire_is_linear
         (delete_operation circuit operation_node_id)
         q"
      using
        valid_circuit
        operation_exists
        valid_wire_after
      by (rule delete_operation_preserves_wire_is_linear)
  qed
qed

lemma delete_operation_preserves_valid_circuit:
  (* Deleting an operation preserves every structural invariant of a
     valid circuit: well-formedness, acyclicity, and wire linearity.
  *)
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

proof -
  have well_formed:
    "is_well_formed_circuit
       (delete_operation circuit operation_node_id)"
    using
      valid_state
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_well_formed_circuit)

  have acyclic:
    "is_acyclic_circuit
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_acyclicity)

  have linear:
    "all_wires_linear
       (delete_operation circuit operation_node_id)"
    using
      valid_circuit
      operation_exists
    by (rule delete_operation_preserves_wire_linearity)

  show ?thesis
    unfolding is_valid_circuit_def
    using well_formed acyclic linear
    by simp
qed

(* ------------------- Replacement Section begins ------------------ *)

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

(* ------------------- Replacement Section ends ------------------ *)

section \<open>Subcircuit Replacement\<close>

record subcircuit =
  subgraph :: quantum_circuit
    (* The circuit fragment that will replace an operation node. *)

  input_interface :: "qubit \<Rightarrow> node_id option"
    (* For each wire entering the subcircuit, gives the corresponding
       entry node inside the fragment. Wires not used by the fragment
       map to None. *)

  output_interface :: "qubit \<Rightarrow> node_id option"
    (* For each wire leaving the subcircuit, gives the corresponding
       exit node inside the fragment. Wires not used by the fragment
       map to None. *)

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
           nodes :=
             (nodes circuit)
               (operation_node_id := None),
  
           edges :=
             {e \<in> edges circuit.
                edge_source e \<noteq> operation_node_id
              \<and> edge_target e \<noteq> operation_node_id}
         \<rparr>"

lemma remove_operation_node_selected[simp]:
  (* Looking up the removed node ID after removal returns None. *)
  "nodes
     (remove_operation_node circuit operation_node_id)
     operation_node_id
   = None"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_other[simp]:
  (* Removing one node does not alter the node-table entry stored at
     any different node ID. *)
  assumes different_node:
    "other_node_id \<noteq> operation_node_id"

  shows
    "nodes
       (remove_operation_node circuit operation_node_id)
       other_node_id
     =
     nodes circuit other_node_id"

  using different_node
  unfolding remove_operation_node_def
  by simp

lemma edges_remove_operation_node[simp]:
  (* The resulting edge set contains exactly the original edges that
     are not incident on the removed node. *)
  "edges
     (remove_operation_node circuit operation_node_id)
   =
   {e \<in> edges circuit.
      edge_source e \<noteq> operation_node_id
    \<and> edge_target e \<noteq> operation_node_id}"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_has_no_outgoing_edge:
  (* After removal, no remaining edge has the removed node as its
     source. *)
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  shows
    "edge_source e \<noteq> operation_node_id"

  using edge_remains
  by simp

lemma remove_operation_node_has_no_incoming_edge:
  (* After removal, no remaining edge has the removed node as its
     target. *)
  assumes edge_remains:
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

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
    "e \<in> edges
       (remove_operation_node circuit operation_node_id)"

  using
    edge_exists
    source_different
    target_different
  by simp

lemma remove_operation_node_preserves_num_qubits[simp]:
  (* Removing a node does not change the circuit's qubit count. *)
  "num_qubits
     (remove_operation_node circuit operation_node_id)
   =
   num_qubits circuit"

  unfolding remove_operation_node_def
  by simp

lemma remove_operation_node_preserves_next_id[simp]:
  (* Removing a node does not allocate any IDs, so next_id remains
     unchanged. *)
  "next_id
     (remove_operation_node circuit operation_node_id)
   =
   next_id circuit"

  unfolding remove_operation_node_def
  by simp

definition insert_subcircuit_nodes ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
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
         \<and>
         ?local_node_id
           \<in> subcircuit_operation_node_ids replacement
      then
        nodes
          (subgraph replacement)
          ?local_node_id
      else
        nodes circuit node_id)
     =
     Some node"
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

  using existing_namespace
  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_edges[simp]:
  (* Copying nodes does not yet insert any subcircuit edges. *)
  "edges
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   edges current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_num_qubits[simp]:
  (* Copying replacement nodes does not change the host's qubit
     universe. *)
  "num_qubits
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

lemma insert_subcircuit_nodes_preserves_next_id[simp]:
  (* Copying the replacement nodes does not yet advance the host
     circuit's allocation boundary. The complete replacement
     transformation will update next_id once all nodes and edges have
     been installed. *)
  "next_id
     (insert_subcircuit_nodes
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  unfolding insert_subcircuit_nodes_def
  by simp

definition insert_subcircuit_internal_edges ::
  "quantum_circuit
    \<Rightarrow> quantum_circuit
    \<Rightarrow> subcircuit
    \<Rightarrow> quantum_circuit"
where
  (* Inserts all internal edges of the replacement subcircuit into the
     current host circuit.

     original_circuit fixes the renaming offset through its next_id.
     current_circuit is the intermediate circuit being transformed.

     Only edges whose source and target are both operation nodes of the
     replacement are inserted here. Connections between the host
     circuit and the replacement interfaces are added by later helpers.
  *)
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

  unfolding insert_subcircuit_internal_edges_def
  by simp

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

  using existing_edge
  unfolding insert_subcircuit_internal_edges_def
  by simp

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

  using renamed_edge
  unfolding insert_subcircuit_internal_edges_def
  by simp

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

  using
    renamed_subcircuit_internal_edge[
      OF internal_edge,
      of original_circuit]
  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_nodes[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   nodes current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_node[simp]:
  "nodes
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
     node_id
   =
   nodes current_circuit node_id"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_num_qubits[simp]:
  "num_qubits
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   num_qubits current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

lemma insert_subcircuit_internal_edges_preserves_next_id[simp]:
  "next_id
     (insert_subcircuit_internal_edges
        original_circuit
        current_circuit
        replacement)
   =
   next_id current_circuit"

  unfolding insert_subcircuit_internal_edges_def
  by simp

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

(* -------- Subcircuit replacement preservation begins -------- *)


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


lemma valid_subcircuit_replacement_is_acyclic:
  (* A valid subcircuit replacement contains a valid replacement subgraph.

     Validity of the subcircuit includes validity of its underlying circuit,
     and validity of that circuit includes acyclicity. *)
  assumes valid_replacement:
    "is_valid_subcircuit_replacement
       circuit
       operation_node_id
       replacement"

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
       \<in>
       {(rename source, rename target) |
          source target.
          (source, target) \<in> relation}\<^sup>+"

  shows
    "\<exists>local_node.
       (local_node, local_node) \<in> relation\<^sup>+"
proof -

  let ?renamed_relation =
    "{(rename source, rename target) |
       source target.
       (source, target) \<in> relation}"

  have reflect_renamed_path:
    "(renamed_source, renamed_target)
       \<in> ?renamed_relation\<^sup>+
     \<Longrightarrow>
     \<exists>local_source local_target.
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

proof -
  let ?rename =
    "rename_subcircuit_node_id circuit"

  let ?internal_relation =
    "{(edge_source e, edge_target e) |
       e.
       e \<in> subcircuit_internal_edges replacement}"

  have rename_injective:
    "inj ?rename"
    unfolding inj_def
    using rename_subcircuit_node_id_injective
    by blast

  have renamed_relation_eq:
    "{(edge_source e, edge_target e) |
       e.
       e \<in>
         renamed_subcircuit_internal_edges
           circuit
           replacement}
     =
     {(?rename source, ?rename target) |
        source target.
        (source, target) \<in> ?internal_relation}"
  proof (rule set_eqI)
    fix renamed_pair

    show
      "renamed_pair
         \<in>
         {(edge_source e, edge_target e) |
            e.
            e \<in>
              renamed_subcircuit_internal_edges
                circuit
                replacement}
       \<longleftrightarrow>
       renamed_pair
         \<in>
         {(?rename source, ?rename target) |
            source target.
            (source, target) \<in> ?internal_relation}"
    proof

      assume renamed_pair_in:
        "renamed_pair
           \<in>
           {(edge_source e, edge_target e) |
              e.
              e \<in>
                renamed_subcircuit_internal_edges
                  circuit
                  replacement}"

      then obtain renamed_edge where
        renamed_edge:
          "renamed_edge
             \<in>
             renamed_subcircuit_internal_edges
               circuit
               replacement"
      and renamed_pair_eq:
          "renamed_pair =
             (edge_source renamed_edge,
              edge_target renamed_edge)"
        by auto

      from renamed_edge obtain local_edge where
        local_edge:
          "local_edge
             \<in> subcircuit_internal_edges replacement"
      and renamed_edge_eq:
          "renamed_edge =
             rename_subcircuit_edge circuit local_edge"
        unfolding renamed_subcircuit_internal_edges_def
        by auto

      have local_pair:
        "(edge_source local_edge, edge_target local_edge)
           \<in> ?internal_relation"
        using local_edge
        by auto

      show
        "renamed_pair
           \<in>
           {(?rename source, ?rename target) |
              source target.
              (source, target) \<in> ?internal_relation}"
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
        "renamed_pair
           \<in>
           {(?rename source, ?rename target) |
              source target.
              (source, target) \<in> ?internal_relation}"

      then obtain source target where
        local_pair:
          "(source, target) \<in> ?internal_relation"
      and renamed_pair_eq:
          "renamed_pair = (?rename source, ?rename target)"
        by auto

      from local_pair obtain local_edge where
        local_edge:
          "local_edge
             \<in> subcircuit_internal_edges replacement"
      and source_eq:
          "source = edge_source local_edge"
      and target_eq:
          "target = edge_target local_edge"
        by auto

      have renamed_edge:
        "rename_subcircuit_edge circuit local_edge
           \<in>
           renamed_subcircuit_internal_edges
             circuit
             replacement"
        using local_edge
        unfolding renamed_subcircuit_internal_edges_def
        by simp

      show
        "renamed_pair
           \<in>
           {(edge_source e, edge_target e) |
              e.
              e \<in>
                renamed_subcircuit_internal_edges
                  circuit
                  replacement}"
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
    "(renamed_node, renamed_node)
       \<in>
       {(?rename source, ?rename target) |
          source target.
          (source, target) \<in> ?internal_relation}\<^sup>+"
    unfolding renamed_relation_eq
    by simp

  from injective_renaming_trancl_reflects_cycle[
      OF rename_injective renamed_internal_relation_cycle]
  obtain local_node where
    local_internal_cycle:
      "(local_node, local_node)
         \<in> ?internal_relation\<^sup>+"
    by auto

  have internal_relation_subset:
    "?internal_relation
       \<subseteq>
       edge_relation (subgraph replacement)"
  proof
    fix pair

    assume pair_in:
      "pair \<in> ?internal_relation"

    then obtain local_edge where
      local_edge:
        "local_edge
           \<in> subcircuit_internal_edges replacement"
    and pair_eq:
        "pair =
           (edge_source local_edge,
            edge_target local_edge)"
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
    "?internal_relation\<^sup>+
       \<subseteq>
       (edge_relation (subgraph replacement))\<^sup>+"
    
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

  using
    valid_replacement
    result_cycle
    replace_operation_by_subcircuit_edge_cases
proof -

  let ?result =
    "fst
       (replace_operation_by_subcircuit
          circuit
          frontier
          operation_node_id
          replacement)"

  let ?renamed_nodes =
    "rename_subcircuit_node_id circuit `
       subcircuit_operation_node_ids replacement"

  let ?internal_relation =
    "{(edge_source e, edge_target e) |
       e.
       e \<in>
         renamed_subcircuit_internal_edges
           circuit
           replacement}"

  let ?collapse =
    "\<lambda>n.
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
      "nodes circuit operation_node_id =
         Some (OperationNode original_op)"
  and replacement_valid:
      "is_valid_subcircuit replacement"
    unfolding is_valid_subcircuit_replacement_def
    by blast

  have renamed_fresh:
    "local_node \<in>
       subcircuit_operation_node_ids replacement
     \<Longrightarrow>
     nodes circuit
       (rename_subcircuit_node_id circuit local_node)
     =
     None"
    for local_node
    using allocation
    by (metis
        all_existing_node_ids_below_next_id_def
        linorder_not_less
        renamed_subcircuit_node_id_is_unused)


  have existing_node_not_renamed:
    "nodes circuit original_node \<noteq> None
     \<Longrightarrow>
     original_node \<notin> ?renamed_nodes"
    for original_node
    using renamed_fresh
    by fastforce


  have result_edge_cases:
    "(u, v) \<in> edge_relation ?result
     \<Longrightarrow>
       ((u, v) \<in> ?internal_relation)
       \<or>
       ((?collapse u, ?collapse v)
          \<in> edge_relation circuit)"
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

    from replace_operation_by_subcircuit_edge_cases[
        OF valid_replacement edge_in_result]
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
        "(edge_source e, edge_target e)
           \<in> edge_relation circuit"
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
        "e \<in>
           renamed_subcircuit_internal_edges
             circuit
             replacement
         \<or>
         (\<exists>q predecessor_node renamed_input_node.
            q \<in> subcircuit_interface_qubits replacement
            \<and>
            predecessor_on_wire
              circuit
              operation_node_id
              q
            =
            Some predecessor_node
            \<and>
            renamed_input_interface
              circuit
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
              circuit
              replacement
              q
            =
            Some renamed_output_node
            \<and>
            successor_on_wire
              circuit
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

      from remaining_cases show ?thesis
      proof

        assume internal_edge:
          "e \<in>
             renamed_subcircuit_internal_edges
               circuit
               replacement"

        have
          "(edge_source e, edge_target e)
             \<in> ?internal_relation"
          using internal_edge
          by blast

        then show ?thesis
          using source_eq target_eq
          by simp

      next

        assume connection_cases:
          "(\<exists>q predecessor_node renamed_input_node.
              q \<in> subcircuit_interface_qubits replacement
              \<and>
              predecessor_on_wire
                circuit
                operation_node_id
                q
              =
              Some predecessor_node
              \<and>
              renamed_input_interface
                circuit
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
                circuit
                replacement
                q
              =
              Some renamed_output_node
              \<and>
              successor_on_wire
                circuit
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

        from connection_cases show ?thesis
        proof

          assume input_case:
            "\<exists>q predecessor_node renamed_input_node.
               q \<in> subcircuit_interface_qubits replacement
               \<and>
               predecessor_on_wire
                 circuit
                 operation_node_id
                 q
               =
               Some predecessor_node
               \<and>
               renamed_input_interface
                 circuit
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

          then obtain q predecessor_node renamed_input_node where
            predecessor:
              "predecessor_on_wire
                 circuit
                 operation_node_id
                 q
               =
               Some predecessor_node"
          and renamed_input:
              "renamed_input_interface
                 circuit
                 replacement
                 q
               =
               Some renamed_input_node"
          and edge_eq:
              "e =
                 make_edge
                   predecessor_node
                   renamed_input_node
                   q"
            by blast

          from predecessor_on_wire_correct[OF predecessor]
          have predecessor_edge:
            "make_edge
               predecessor_node
               operation_node_id
               q
             \<in> edges circuit" .

          from original_edges_well_formed predecessor_edge
          have predecessor_edge_well_formed:
            "is_well_formed_edge
               circuit
               (make_edge
                  predecessor_node
                  operation_node_id
                  q)"
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
              "input_interface replacement q =
                 Some local_input_node"
          and renamed_input_eq:
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
               \<in>
               subcircuit_operation_node_ids replacement"
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
            "(?collapse predecessor_node,
              ?collapse renamed_input_node)
             =
             (predecessor_node, operation_node_id)"
            using
              predecessor_not_renamed
              renamed_input_in
            by simp

          have original_relation:
            "(predecessor_node, operation_node_id)
               \<in> edge_relation circuit"
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
               \<and>
               renamed_output_interface
                 circuit
                 replacement
                 q
               =
               Some renamed_output_node
               \<and>
               successor_on_wire
                 circuit
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

          then obtain q renamed_output_node successor_node where
            renamed_output:
              "renamed_output_interface
                 circuit
                 replacement
                 q
               =
               Some renamed_output_node"
          and successor:
              "successor_on_wire
                 circuit
                 operation_node_id
                 q
               =
               Some successor_node"
          and edge_eq:
              "e =
                 make_edge
                   renamed_output_node
                   successor_node
                   q"
            by blast

          from successor_on_wire_correct[OF successor]
          have successor_edge:
            "make_edge
               operation_node_id
               successor_node
               q
             \<in> edges circuit" .

          from original_edges_well_formed successor_edge
          have successor_edge_well_formed:
            "is_well_formed_edge
               circuit
               (make_edge
                  operation_node_id
                  successor_node
                  q)"
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
              "output_interface replacement q =
                 Some local_output_node"
          and renamed_output_eq:
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
               \<in>
               subcircuit_operation_node_ids replacement"
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
            "(?collapse renamed_output_node,
              ?collapse successor_node)
             =
             (operation_node_id, successor_node)"
            using
              renamed_output_in
              successor_not_renamed
            by simp

          have original_relation:
            "(operation_node_id, successor_node)
               \<in> edge_relation circuit"
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
    "(u, v) \<in> (edge_relation ?result)\<^sup>+
     \<Longrightarrow>
       (u, v) \<in> ?internal_relation\<^sup>+
       \<or>
       (?collapse u, ?collapse v)
         \<in> (edge_relation circuit)\<^sup>+"
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
          "(?collapse v, ?collapse w)
             \<in> edge_relation circuit"

        have internal_endpoints_renamed:
          "u \<in> ?renamed_nodes \<and>
           v \<in> ?renamed_nodes"
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
          "(?collapse u, ?collapse w)
             \<in> (edge_relation circuit)\<^sup>+"
          using final_original collapse_uv
          by auto 

        then show ?case
          by blast
      qed

    next

      assume prefix_original:
        "(?collapse u, ?collapse v)
           \<in> (edge_relation circuit)\<^sup>+"

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
          "(?collapse u, ?collapse w)
             \<in> (edge_relation circuit)\<^sup>+"
          using prefix_original collapse_vw
          by simp

        then show ?case
          by blast

      next

        assume final_original:
          "(?collapse v, ?collapse w)
             \<in> edge_relation circuit"

        have
          "(?collapse u, ?collapse w)
             \<in> (edge_relation circuit)\<^sup>+"
          using prefix_original final_original
          by (rule trancl_into_trancl)

        then show ?case
          by blast
      qed
    qed
  qed

  from path_cases[OF result_cycle]
  show ?thesis
  proof

    assume internal_cycle:
      "(node, node) \<in> ?internal_relation\<^sup>+"

    then show ?thesis
      by blast

  next

    assume original_cycle:
      "(?collapse node, ?collapse node)
         \<in> (edge_relation circuit)\<^sup>+"

    then show ?thesis
      by blast
  qed
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

proof -
  from replacement_cycle_internal_or_original[
      OF valid_state valid_replacement result_cycle]
  have cycle_classification:
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
    by simp

  from cycle_classification show ?thesis
    using
      renamed_internal_cycle_implies_subcircuit_cycle
    by auto
qed


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

proof -
  let ?result =
    "fst
       (replace_operation_by_subcircuit
          circuit
          frontier
          operation_node_id
          replacement)"

  have replacement_acyclic:
    "is_acyclic_circuit (subgraph replacement)"
    using valid_replacement
    by (rule valid_subcircuit_replacement_is_acyclic)

  show ?thesis
    unfolding
      is_acyclic_circuit_def
      acyclic_def
    by (meson
        acyclic_def
        is_acyclic_circuit_def
        original_acyclic
        replacement_acyclic
        replacement_cycle_cases
        valid_replacement
        valid_state)
qed

(* -------- Subcircuit replacement preservation ends -------- *)

(* Example definitions to demonstrate gate and operation *)

definition ex_h_q0 :: operation where
  "ex_h_q0 = \<lparr>op_gate = Gate_H, op_qargs = [Qubit 0]\<rparr>"

definition ex_cnot_q0_q1 :: operation where
  "ex_cnot_q0_q1 =
     \<lparr>op_gate = Gate_CNOT, op_qargs = [Qubit 0, Qubit 1]\<rparr>"

value "ex_cnot_q0_q1"

end