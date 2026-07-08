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

(* Example definitions to demonstrate gate and operation *)

definition ex_h_q0 :: operation where
  "ex_h_q0 = \<lparr>op_gate = Gate_H, op_qargs = [Qubit 0]\<rparr>"

definition ex_cnot_q0_q1 :: operation where
  "ex_cnot_q0_q1 =
     \<lparr>op_gate = Gate_CNOT, op_qargs = [Qubit 0, Qubit 1]\<rparr>"

value "ex_cnot_q0_q1"

end