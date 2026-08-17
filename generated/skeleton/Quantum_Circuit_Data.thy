theory Quantum_Circuit_Data
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

end
