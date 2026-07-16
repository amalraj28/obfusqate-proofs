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

(* -------- Edge well-formedness definitions end --------- *)

(* ---- Check validity of OperationNodes in the circuit ---------- *)

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
                 \<in> edges (insert_node new_node_id new_node circuit)"

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
    using valid_frontier
    unfolding is_valid_frontier_def
    by (simp add: qubit_in_circuit_def)

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

lemma splice_wire_preserves_valid_frontier:
  (* Splicing an existing node into a valid qubit wire preserves the
     frontier invariant, provided the inserted node belongs to that wire. *)
  assumes valid_frontier:
    "is_valid_frontier circuit frontier"

  assumes new_node_exists:
    "nodes circuit new_node_id = Some new_node"

  assumes new_node_uses_wire:
    "node_uses_qubit new_node q"

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
           \<in> edges ?updated_circuit"
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
             (* splice_wire_contains_new_input_edge[
                where circuit = circuit
                  and frontier = frontier
                  and q = q
                  and new_node_id = new_node_id] ---> This commented block is not needed (error)*)
        by simp
      show ?thesis
        (* Choose new_node as the witness for the existential statement. *)
        using 
          updated_frontier_lookup
          new_node_exists_after_splice
          new_node_uses_queried_wire
          new_output_edge_exists
        by (intro exI[of _ new_node]) simp

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
      using valid_frontier queried_wire_valid_before
      unfolding is_valid_frontier_def
      by blast

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

      show ?thesis
        (* For an unaffected wire, reuse its original frontier node.
           Its frontier lookup, stored node, wire membership, and final
           output edge all remain valid after the splice. *)
        using
          updated_frontier_unchanged
          old_frontier_node_still_exists
          old_frontier_node_uses_wire
          old_output_edge_still_exists
        by (intro exI[of _ old_frontier_node]) simp
    qed
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

  shows
    "is_valid_frontier \<comment>\<open>The final frontier correctly describes the final circuit\<close>
       (fst (splice_wires circuit frontier qs new_node_id))
       (snd (splice_wires circuit frontier qs new_node_id))"
  
  using valid_frontier new_node_exists new_node_uses_all_wires \<comment>\<open>Passes assumptions to the induction proof\<close>

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

  have first_splice_preserves_frontier:
    (* Splicing the first wire produces a circuit and frontier that still satisfy the valid-frontier invariant. *)
    "is_valid_frontier updated_circuit updated_frontier"
  proof -
    have "is_valid_frontier 
        (fst (splice_wire circuit frontier q new_node_id))
        (snd (splice_wire circuit frontier q new_node_id))"
      using splice_wire_preserves_valid_frontier[
        OF Cons.prems(1) Cons.prems(2) new_node_uses_first_wire
      ] . (* . means finish proof using the previous fact *)

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
      OF first_splice_preserves_frontier
         new_node_still_exists
         new_node_uses_remaining_wires] .
    
  show ?case
    using splice_result remaining_splices_preserve_frontier
    by simp
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
  assumes valid_frontier: "is_valid_frontier circuit frontier"
  assumes valid_operation: "is_valid_operation op"
  assumes next_id_unused: "next_id_is_unused circuit"

  shows "is_valid_frontier
    (fst (insert_operation circuit frontier op))
    (snd (insert_operation circuit frontier op))"

proof -
  let ?circuit1 = "insert_node (next_id circuit) (OperationNode op) circuit"
  let ?splice_result = "splice_wires ?circuit1 frontier (op_qargs op) (next_id circuit)"

  let ?circuit2 = "fst ?splice_result"
  let ?frontier2 = "snd ?splice_result"

  let ?final_circuit = "?circuit2 \<lparr> next_id := increment_node_id (next_id circuit) \<rparr>"

  have operation_node_uses_all_qubits:
    "\<forall>q \<in> set (op_qargs op). 
      node_uses_qubit (OperationNode op) q"
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

  have frontier_after_splice:
    (* Splicing the newly inserted operation node into all of its qubit
       wires preserves the frontier invariant. *)
    "is_valid_frontier ?circuit2 ?frontier2"
    using frontier_after_insert_is_valid
          operation_node_exists
          operation_node_uses_all_qubits
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
    
(* ---------------- Operation insertion ends ---------------- *)

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

(* Example definitions to demonstrate gate and operation *)

definition ex_h_q0 :: operation where
  "ex_h_q0 = \<lparr>op_gate = Gate_H, op_qargs = [Qubit 0]\<rparr>"

definition ex_cnot_q0_q1 :: operation where
  "ex_cnot_q0_q1 =
     \<lparr>op_gate = Gate_CNOT, op_qargs = [Qubit 0, Qubit 1]\<rparr>"

value "ex_cnot_q0_q1"

end