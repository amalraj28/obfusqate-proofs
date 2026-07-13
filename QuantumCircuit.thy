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


definition valid_operation :: "operation \<Rightarrow> bool" where
  (* Defines a valid operation. An operation is valid iff
      1. Number of elements in q_args is equal to arity of the gate
      2. All elements in q_args are distinct
  *)

  "valid_operation op \<longleftrightarrow>
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

(* -------- Edge well-formedness definitions end --------- *)

(* ---- Check validity of OperationNodes in the circuit ---------- *)

definition operation_in_circuit :: "quantum_circuit \<Rightarrow> operation \<Rightarrow> bool" where
  (* Checks whether a given operation belongs to the given quantum circuit. An operation belongs to the given circuit iff
      1. The operation itself is valid (correct arity and distinct qubits)
      2. Every qubit used by the operation belongs to the circuit
  *)
  "operation_in_circuit circuit op \<longleftrightarrow>
      valid_operation op
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

lemma nodes_insert_node_other[simp]: (* helper lemma *)
  (* All other node ids apart from the one where insertion happen, remain unchanged *)
  assumes "other_node_id \<noteq> node_id"
  shows "nodes (insert_node node_id node circuit) other_node_id =
         nodes circuit other_node_id"
  using assms
  unfolding insert_node_def
  by simp

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

(* ---------------- Frontier definition begins ------------------ *)

type_synonym frontier = "qubit \<Rightarrow> node_id" (* Frontier is a mapping from qubit \<Rightarrow> node_id, where node_id means the last operation encountered on this qubit *)

definition initial_frontier :: frontier where
  (* Initially, frontier (map) would be from qubit to its input node (since circuit is empty) *)
  "initial_frontier q = get_input_node_id q"

definition update_frontier :: "frontier \<Rightarrow> qubit \<Rightarrow> node_id \<Rightarrow> frontier" where
  (* Updating frontier for a qubit q means that we are updating the existing entry of the qubit q in the map with the id of the new node *)
  "update_frontier frontier q new_node_id = frontier(q := new_node_id)"

(* ---------------- Frontier definition ends ------------------ *)

(* -------- Construction-state validity definitions begin -------- *)

definition is_valid_frontier :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  (* A frontier is valid when, for every valid qubit:
       1. the frontier points to an existing node on that wire, and
       2. that node is connected directly to the output node on that wire.
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
           \<in> edges circuit))"


definition next_id_is_unused :: "quantum_circuit \<Rightarrow> bool" where
  (* The circuit's next_id is unused when no node is currently stored at that ID. This prevents the next insertion from overwriting an existing node *)
  "next_id_is_unused circuit \<longleftrightarrow> nodes circuit (next_id circuit) = None"


definition is_valid_construction_state :: "quantum_circuit \<Rightarrow> frontier \<Rightarrow> bool" where
  (* A circuit and frontier form a valid construction state when:
       1. the circuit is structurally well formed;
       2. the frontier correctly describes the current end of every wire;
       3. next_id is unused and can safely identify the next operation node.
  *)
  "is_valid_construction_state circuit frontier \<longleftrightarrow>
       is_well_formed_circuit circuit
     \<and> is_valid_frontier circuit frontier
     \<and> next_id_is_unused circuit"

(* -------- Construction-state validity definitions end -------- *)

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
         \<in> edges (initial_circuit number_of_qubits)"
      using q_lt q_form
      unfolding initial_frontier_def
      by (intro exI[of _ "InputNode (Qubit qubit_number)"])
         (simp add:
            initial_circuit_input_node
            initial_circuit_has_wire_edge)
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

lemma initial_construction_state_is_valid:
  (* The initial circuit together with the initial frontier forms a
     valid starting state for repeated operation insertion. *)
  "is_valid_construction_state (initial_circuit number_of_qubits) initial_frontier"
  unfolding is_valid_construction_state_def
  using initial_circuit_is_well_formed
        initial_frontier_is_valid
        initial_next_id_is_unused
  by simp

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

lemma fst_splice_wire[simp]:
  (* Says that the first part of splice_wire response is the updated circuit *)
  "fst (splice_wire circuit frontier q new_node_id) =
   splice_wire_without_updating_frontier circuit frontier q new_node_id"
  unfolding splice_wire_def
  by simp

lemma snd_splice_wire[simp]:
  (* Says that the second part of splice_wire response is the updated frontier map *)
  "snd (splice_wire circuit frontier q new_node_id) =
   update_frontier frontier q new_node_id"
  unfolding splice_wire_def
  by simp


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

lemma splice_wire_preserves_num_qubits[simp]:
  (* Splicing a node into one wire changes only the circuit edges, so the number of qubits remains unchanged. *)
  "num_qubits (fst (splice_wire circuit frontier q new_node_id)) = num_qubits circuit"

  unfolding
    splice_wire_def
    splice_wire_without_updating_frontier_def
    insert_edge_def
    delete_edge_def
 
  by (cases circuit; metis fst_conv quantum_circuit.select_convs(1) quantum_circuit.update_convs(3))


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


lemma insert_edge_preserves_nodes[simp]:
  "nodes (insert_edge e circuit) node_id = nodes circuit node_id"
  unfolding insert_edge_def
  by simp

lemma delete_edge_preserves_nodes[simp]:
  "nodes (delete_edge e circuit) node_id = nodes circuit node_id"
  unfolding delete_edge_def
  by simp

lemma splice_wire_without_updating_frontier_preserves_nodes[simp]:
  "nodes
     (splice_wire_without_updating_frontier
        circuit frontier q new_node_id)
     node_id
   = nodes circuit node_id"
proof -
  let ?old_node_id = "frontier q" (* The node currently stored in the frontier for wire q. *)
  let ?out_node_id = "get_output_node_id q"  (* The output boundary node of wire q. *)

  let ?old_edge = "make_edge ?old_node_id ?out_node_id q" (* The edge currently connecting the frontier node directly to the output node. *)

  let ?new_in_edge = "make_edge ?old_node_id new_node_id q" (* The new edge from the old frontier node to the inserted node. *)

  let ?new_out_edge = "make_edge new_node_id ?out_node_id q" (* The new edge from the inserted node to the output node *)

  have deleting_old_edge_preserves_nodes:
    "nodes (delete_edge ?old_edge circuit) node_id = nodes circuit node_id" \<comment>\<open>Deleting "old_edge" from the circuit does not change the nodes field \<close>
    unfolding delete_edge_def
    by simp

  have inserting_first_edge_preserves_nodes:
    "nodes
       (insert_edge ?new_in_edge
          (delete_edge ?old_edge circuit))
       node_id
     =
     nodes
       (delete_edge ?old_edge circuit)
       node_id"
    \<comment>\<open>Inserting new_in_edge does not change the nodes field\<close>
    unfolding insert_edge_def
    by simp

  have inserting_second_edge_preserves_nodes:
    "nodes
       (insert_edge ?new_out_edge
          (insert_edge ?new_in_edge
             (delete_edge ?old_edge circuit)))
       node_id
     =
     nodes
       (insert_edge ?new_in_edge
          (delete_edge ?old_edge circuit))
       node_id"
    \<comment>\<open>Inserting new_out_edge does not change the nodes field\<close>
    unfolding insert_edge_def
    by simp

  have final_circuit_preserves_nodes:
    "nodes
       (insert_edge
          ?new_out_edge
          (insert_edge
             ?new_in_edge
             (delete_edge ?old_edge circuit)))
       node_id
     = nodes circuit node_id" \<comment>\<open>Deleting old edge and inserting new edges from old node to new node, and new node to out node, keeps the nodes field of the circuit unchanged from the original circuit\<close>
  proof -
    have
      "nodes
         (insert_edge
            ?new_out_edge
            (insert_edge
               ?new_in_edge
               (delete_edge ?old_edge circuit)))
       node_id
       =
       nodes
         (insert_edge
            ?new_in_edge
            (delete_edge ?old_edge circuit))
       node_id"  \<comment>\<open>Deleting old edge and inserting new edges from old node to new node, and new node to out node, keeps the nodes field of the circuit same as it was immediately before inserting the second new edge\<close>

      using inserting_second_edge_preserves_nodes .

    also have
      "nodes
         (insert_edge
            ?new_in_edge
            (delete_edge ?old_edge circuit))
       node_id
       =
       nodes
         (delete_edge ?old_edge circuit)
       node_id" \<comment>\<open>Deleting old edge and inserting new edge from old node to new node keeps the nodes field of the circuit same as it was immediately before inserting the first new edge\<close>
      using inserting_first_edge_preserves_nodes .

    also have
      "nodes
         (delete_edge ?old_edge circuit)
       node_id
       =
       nodes circuit node_id" \<comment>\<open>Deleting old edge keeps the nodes field of the circuit same as it was in the original circuit\<close>
      using deleting_old_edge_preserves_nodes .

    finally show ?thesis .
  qed
  
  show ?thesis
    unfolding splice_wire_without_updating_frontier_def
    using final_circuit_preserves_nodes
    by metis
qed
  

lemma splice_wire_preserves_nodes[simp]:
  "nodes
     (fst (splice_wire circuit frontier q new_node_id))
     node_id
   = nodes circuit node_id"
  unfolding splice_wire_def
  by simp


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

  
(* ---------------- Operation insertion ends ---------------- *)

(* Example definitions to demonstrate gate and operation *)

definition ex_h_q0 :: operation where
  "ex_h_q0 = \<lparr>op_gate = Gate_H, op_qargs = [Qubit 0]\<rparr>"

definition ex_cnot_q0_q1 :: operation where
  "ex_cnot_q0_q1 =
     \<lparr>op_gate = Gate_CNOT, op_qargs = [Qubit 0, Qubit 1]\<rparr>"

value "ex_cnot_q0_q1"

end