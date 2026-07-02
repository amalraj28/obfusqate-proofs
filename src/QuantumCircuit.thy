theory QuantumCircuit
  imports Main
begin

section ‹Basic identifiers›

type_synonym node_id = nat
type_synonym qubit = nat

section ‹Nodes and labelled wire edges›

datatype 'gate dag_node =
    InputNode qubit
  | OutputNode qubit
  | OperationNode 'gate "qubit list"

record dag_edge =
  edge_source :: node_id
  edge_target :: node_id
  edge_qubit :: qubit

record 'gate quantum_circuit_dag =
  dag_num_qubits :: nat
  dag_nodes :: "node_id ⇒ 'gate dag_node option"
  dag_edges :: "dag_edge set"
  dag_next_id :: node_id

section ‹Canonical boundary identifiers›

definition input_node_id :: "qubit ⇒ node_id" where
  "input_node_id q = 2 * q"

definition output_node_id :: "qubit ⇒ node_id" where
  "output_node_id q = 2 * q + 1"

definition first_operation_id :: "nat ⇒ node_id" where
  "first_operation_id n = 2 * n"

lemma input_output_ids_distinct[simp]:
  "input_node_id q ≠ output_node_id r"
  unfolding input_node_id_def output_node_id_def
  by arith

lemma input_node_id_injective:
  "input_node_id q = input_node_id r ⟹ q = r"
  unfolding input_node_id_def
  by simp

lemma output_node_id_injective:
  "output_node_id q = output_node_id r ⟹ q = r"
  unfolding output_node_id_def
  by simp

section ‹Node and edge queries›

definition node_ids :: "'gate quantum_circuit_dag ⇒ node_id set" where
  "node_ids G = {v. dag_nodes G v ≠ None}"

definition operation_node_ids :: "'gate quantum_circuit_dag ⇒ node_id set" where
  "operation_node_ids G =
     {v. ∃gate qs. dag_nodes G v = Some (OperationNode gate qs)}"

fun node_uses_qubit :: "'gate dag_node ⇒ qubit ⇒ bool" where
  "node_uses_qubit (InputNode q) r = (q = r)"
| "node_uses_qubit (OutputNode q) r = (q = r)"
| "node_uses_qubit (OperationNode gate qs) r = (r ∈ set qs)"

definition mk_edge :: "node_id ⇒ node_id ⇒ qubit ⇒ dag_edge" where
  "mk_edge u v q =
     ⦇edge_source = u, edge_target = v, edge_qubit = q⦈"

lemma edge_selectors[simp]:
  "edge_source (mk_edge u v q) = u"
  "edge_target (mk_edge u v q) = v"
  "edge_qubit (mk_edge u v q) = q"
  unfolding mk_edge_def
  by simp_all

definition incoming_edges_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ dag_edge set"
where
  "incoming_edges_on G v q =
     {e ∈ dag_edges G. edge_target e = v ∧ edge_qubit e = q}"

definition outgoing_edges_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ dag_edge set"
where
  "outgoing_edges_on G v q =
     {e ∈ dag_edges G. edge_source e = v ∧ edge_qubit e = q}"

definition incident_edges ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ dag_edge set"
where
  "incident_edges G v =
     {e ∈ dag_edges G. edge_source e = v ∨ edge_target e = v}"

definition edge_relation ::
  "'gate quantum_circuit_dag ⇒ (node_id × node_id) set"
where
  "edge_relation G =
     {(u, v). ∃e ∈ dag_edges G.
        edge_source e = u ∧ edge_target e = v}"

section ‹Structural validity›

definition finite_graph :: "'gate quantum_circuit_dag ⇒ bool" where
  "finite_graph G ⟷ finite (node_ids G) ∧ finite (dag_edges G)"

definition edge_well_formed ::
  "'gate quantum_circuit_dag ⇒ dag_edge ⇒ bool"
where
  "edge_well_formed G e ⟷
     edge_source e ≠ edge_target e ∧
     edge_source e ∈ node_ids G ∧
     edge_target e ∈ node_ids G ∧
     edge_qubit e < dag_num_qubits G ∧
     (∃source_node target_node.
        dag_nodes G (edge_source e) = Some source_node ∧
        dag_nodes G (edge_target e) = Some target_node ∧
        node_uses_qubit source_node (edge_qubit e) ∧
        node_uses_qubit target_node (edge_qubit e))"

definition all_edges_well_formed ::
  "'gate quantum_circuit_dag ⇒ bool"
where
  "all_edges_well_formed G ⟷
     (∀e ∈ dag_edges G. edge_well_formed G e)"

definition valid_operation_payload ::
  "nat ⇒ qubit list ⇒ bool"
where
  "valid_operation_payload n qs ⟷
     qs ≠ [] ∧
     distinct qs ∧
     set qs ⊆ {..<n}"

definition operation_nodes_well_formed ::
  "'gate quantum_circuit_dag ⇒ bool"
where
  "operation_nodes_well_formed G ⟷
     (∀v gate qs.
        dag_nodes G v = Some (OperationNode gate qs) ⟶
        first_operation_id (dag_num_qubits G) ≤ v ∧
        valid_operation_payload (dag_num_qubits G) qs)"

definition boundary_nodes_well_formed ::
  "'gate quantum_circuit_dag ⇒ bool"
where
  "boundary_nodes_well_formed G ⟷
     (∀q < dag_num_qubits G.
        dag_nodes G (input_node_id q) = Some (InputNode q) ∧
        dag_nodes G (output_node_id q) = Some (OutputNode q)) ∧
     (∀v q.
        dag_nodes G v = Some (InputNode q) ⟶
        q < dag_num_qubits G ∧ v = input_node_id q) ∧
     (∀v q.
        dag_nodes G v = Some (OutputNode q) ⟶
        q < dag_num_qubits G ∧ v = output_node_id q)"

definition has_unique_predecessor_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ bool"
where
  "has_unique_predecessor_on G v q ⟷
     (∃!u. mk_edge u v q ∈ dag_edges G)"

definition has_unique_successor_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ bool"
where
  "has_unique_successor_on G v q ⟷
     (∃!w. mk_edge v w q ∈ dag_edges G)"

definition has_no_predecessor_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ bool"
where
  "has_no_predecessor_on G v q ⟷
     ¬ (∃u. mk_edge u v q ∈ dag_edges G)"

definition has_no_successor_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ bool"
where
  "has_no_successor_on G v q ⟷
     ¬ (∃w. mk_edge v w q ∈ dag_edges G)"

definition wire_degrees_well_formed ::
  "'gate quantum_circuit_dag ⇒ bool"
where
  "wire_degrees_well_formed G ⟷
     (∀q < dag_num_qubits G.
        has_no_predecessor_on G (input_node_id q) q ∧
        has_unique_successor_on G (input_node_id q) q ∧
        has_unique_predecessor_on G (output_node_id q) q ∧
        has_no_successor_on G (output_node_id q) q) ∧
     (∀v gate qs.
        dag_nodes G v = Some (OperationNode gate qs) ⟶
        (∀q ∈ set qs.
           has_unique_predecessor_on G v q ∧
           has_unique_successor_on G v q))"

definition identifiers_well_formed ::
  "'gate quantum_circuit_dag ⇒ bool"
where
  "identifiers_well_formed G ⟷
     (∀v ∈ node_ids G. v < dag_next_id G) ∧
     first_operation_id (dag_num_qubits G) ≤ dag_next_id G"

definition valid_dag :: "'gate quantum_circuit_dag ⇒ bool" where
  "valid_dag G ⟷
     finite_graph G ∧
     boundary_nodes_well_formed G ∧
     operation_nodes_well_formed G ∧
     all_edges_well_formed G ∧
     wire_degrees_well_formed G ∧
     acyclic (edge_relation G) ∧
     identifiers_well_formed G"

section ‹The empty graph circuit›

definition empty_dag_nodes ::
  "nat ⇒ node_id ⇒ 'gate dag_node option"
where
  "empty_dag_nodes n v =
     (if v < 2 * n then
        if even v
        then Some (InputNode (v div 2))
        else Some (OutputNode (v div 2))
      else None)"

definition empty_dag_edges :: "nat ⇒ dag_edge set" where
  "empty_dag_edges n =
     {e. ∃q < n.
        e = mk_edge (input_node_id q) (output_node_id q) q}"

definition empty_dag :: "nat ⇒ 'gate quantum_circuit_dag" where
  "empty_dag n =
     ⦇dag_num_qubits = n,
      dag_nodes = empty_dag_nodes n,
      dag_edges = empty_dag_edges n,
      dag_next_id = first_operation_id n⦈"

lemma empty_dag_num_qubits[simp]:
  "dag_num_qubits (empty_dag n) = n"
  unfolding empty_dag_def
  by simp

lemma empty_dag_next_id[simp]:
  "dag_next_id (empty_dag n) = first_operation_id n"
  unfolding empty_dag_def
  by simp

lemma empty_dag_input_node:
  assumes "q < n"
  shows "dag_nodes (empty_dag n) (input_node_id q) = Some (InputNode q)"
  using assms
  unfolding empty_dag_def empty_dag_nodes_def input_node_id_def
  by simp

lemma empty_dag_output_node:
  assumes "q < n"
  shows "dag_nodes (empty_dag n) (output_node_id q) = Some (OutputNode q)"
  using assms
  unfolding empty_dag_def empty_dag_nodes_def output_node_id_def
  by simp

lemma empty_dag_edge_iff:
  "e ∈ dag_edges (empty_dag n) ⟷
   (∃q < n. e = mk_edge (input_node_id q) (output_node_id q) q)"
  unfolding empty_dag_def empty_dag_edges_def
  by simp

lemma empty_dag_has_wire_edge:
  assumes "q < n"
  shows "mk_edge (input_node_id q) (output_node_id q) q
         ∈ dag_edges (empty_dag n)"
  using assms
  by (simp add: empty_dag_edge_iff)

section ‹Node-map updates›

definition put_node ::
  "node_id ⇒ 'gate dag_node ⇒ 'gate quantum_circuit_dag ⇒
   'gate quantum_circuit_dag"
where
  "put_node v node G = G⦇dag_nodes := (dag_nodes G)(v := Some node)⦈"

definition remove_node ::
  "node_id ⇒ 'gate quantum_circuit_dag ⇒ 'gate quantum_circuit_dag"
where
  "remove_node v G =
     G⦇dag_nodes := (dag_nodes G)(v := None),
       dag_edges := dag_edges G - incident_edges G v⦈"

lemma put_node_lookup_same[simp]:
  "dag_nodes (put_node v node G) v = Some node"
  unfolding put_node_def
  by simp

lemma put_node_lookup_other[simp]:
  assumes "u ≠ v"
  shows "dag_nodes (put_node v node G) u = dag_nodes G u"
  using assms
  unfolding put_node_def
  by simp

lemma remove_node_lookup_same[simp]:
  "dag_nodes (remove_node v G) v = None"
  unfolding remove_node_def
  by simp

lemma remove_node_preserves_num_qubits[simp]:
  "dag_num_qubits (remove_node v G) = dag_num_qubits G"
  unfolding remove_node_def
  by simp

end
