theory Examples
  imports Transformations
begin

section ‹Small structural example›

datatype example_gate = GH | GCNOT | GX

abbreviation q0_initial_edge :: dag_edge where
  "q0_initial_edge ≡ mk_edge (input_node_id 0) (output_node_id 0) 0"

abbreviation q1_initial_edge :: dag_edge where
  "q1_initial_edge ≡ mk_edge (input_node_id 1) (output_node_id 1) 1"

definition empty_two_qubit :: "example_gate quantum_circuit_dag" where
  "empty_two_qubit = empty_dag 2"

definition h_cuts :: "qubit ⇒ dag_edge" where
  "h_cuts i = q0_initial_edge"

definition after_h :: "example_gate quantum_circuit_dag" where
  "after_h = insert_single_operation empty_two_qubit GH 1 h_cuts"

text ‹
  The first fresh operation identifier in a two-qubit circuit is 4. After the
  H insertion, the q0 wire is Input(0) → H → Output(0), while q1 still has its
  direct input-output edge.
›

lemma after_h_num_qubits[simp]:
  "dag_num_qubits after_h = 2"
  unfolding after_h_def empty_two_qubit_def
  by simp

lemma after_h_next_id[simp]:
  "dag_next_id after_h = 5"
  unfolding after_h_def empty_two_qubit_def first_operation_id_def
  by simp

lemma after_h_operation_node:
  "dag_nodes after_h 4 = Some (OperationNode GH [0])"
  unfolding after_h_def empty_two_qubit_def h_cuts_def
    insert_single_operation_def insert_fragment_at_cuts_def
    merge_fragment_nodes_def lift_fragment_node_def
    singleton_fragment_def cut_wire_map_def first_operation_id_def
    empty_dag_def empty_dag_nodes_def
  by simp

text ‹
  The next example inserts a CNOT after H on q0 and at the initial position on
  q1. The inserted H node has identifier 4, so the q0 cut is 4 → Output(0).
›

definition cnot_cuts :: "qubit ⇒ dag_edge" where
  "cnot_cuts i =
     (if i = 0
      then mk_edge 4 (output_node_id 0) 0
      else q1_initial_edge)"

definition bell_prefix :: "example_gate quantum_circuit_dag" where
  "bell_prefix = insert_single_operation after_h GCNOT 2 cnot_cuts"

lemma bell_prefix_num_qubits[simp]:
  "dag_num_qubits bell_prefix = 2"
  unfolding bell_prefix_def
  by simp

lemma bell_prefix_next_id[simp]:
  "dag_next_id bell_prefix = 6"
  unfolding bell_prefix_def
  by simp

lemma bell_prefix_cnot_node:
  "dag_nodes bell_prefix 5 = Some (OperationNode GCNOT [0, 1])"
  unfolding bell_prefix_def cnot_cuts_def after_h_def empty_two_qubit_def
    h_cuts_def insert_single_operation_def insert_fragment_at_cuts_def
    merge_fragment_nodes_def lift_fragment_node_def singleton_fragment_def
    cut_wire_map_def first_operation_id_def empty_dag_def empty_dag_nodes_def
  by simp

end
