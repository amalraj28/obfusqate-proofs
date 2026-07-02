theory Fragments
  imports QuantumCircuit
begin

section ‹Open graph fragments›

record 'gate dag_fragment =
  fragment_num_wires :: nat
  fragment_nodes :: "node_id ⇒ 'gate dag_node option"
  fragment_edges :: "dag_edge set"
  fragment_entry :: "qubit ⇒ node_id option"
  fragment_exit :: "qubit ⇒ node_id option"
  fragment_next_id :: node_id

definition fragment_node_ids :: "'gate dag_fragment ⇒ node_id set" where
  "fragment_node_ids F = {v. fragment_nodes F v ≠ None}"

definition fragment_operation_only :: "'gate dag_fragment ⇒ bool" where
  "fragment_operation_only F ⟷
     (∀v node.
        fragment_nodes F v = Some node ⟶
        (∃gate qs. node = OperationNode gate qs))"

definition fragment_payloads_well_formed :: "'gate dag_fragment ⇒ bool" where
  "fragment_payloads_well_formed F ⟷
     (∀v gate qs.
        fragment_nodes F v = Some (OperationNode gate qs) ⟶
        valid_operation_payload (fragment_num_wires F) qs)"

definition fragment_edge_well_formed ::
  "'gate dag_fragment ⇒ dag_edge ⇒ bool"
where
  "fragment_edge_well_formed F e ⟷
     edge_source e ≠ edge_target e ∧
     edge_source e ∈ fragment_node_ids F ∧
     edge_target e ∈ fragment_node_ids F ∧
     edge_qubit e < fragment_num_wires F ∧
     (∃source_gate source_qs target_gate target_qs.
        fragment_nodes F (edge_source e) =
          Some (OperationNode source_gate source_qs) ∧
        fragment_nodes F (edge_target e) =
          Some (OperationNode target_gate target_qs) ∧
        edge_qubit e ∈ set source_qs ∧
        edge_qubit e ∈ set target_qs)"

definition fragment_boundary_well_formed :: "'gate dag_fragment ⇒ bool" where
  "fragment_boundary_well_formed F ⟷
     (∀q < fragment_num_wires F.
        (fragment_entry F q = None ⟷ fragment_exit F q = None)) ∧
     (∀q v.
        fragment_entry F q = Some v ⟶
        q < fragment_num_wires F ∧ v ∈ fragment_node_ids F) ∧
     (∀q v.
        fragment_exit F q = Some v ⟶
        q < fragment_num_wires F ∧ v ∈ fragment_node_ids F)"

definition valid_fragment :: "'gate dag_fragment ⇒ bool" where
  "valid_fragment F ⟷
     finite (fragment_node_ids F) ∧
     finite (fragment_edges F) ∧
     fragment_operation_only F ∧
     fragment_payloads_well_formed F ∧
     (∀e ∈ fragment_edges F. fragment_edge_well_formed F e) ∧
     fragment_boundary_well_formed F ∧
     acyclic {(u, v). ∃e ∈ fragment_edges F.
        edge_source e = u ∧ edge_target e = v} ∧
     (∀v ∈ fragment_node_ids F. v < fragment_next_id F)"

section ‹Basic fragment constructors›

definition identity_fragment :: "nat ⇒ 'gate dag_fragment" where
  "identity_fragment k =
     ⦇fragment_num_wires = k,
      fragment_nodes = (λv. None),
      fragment_edges = {},
      fragment_entry = (λq. None),
      fragment_exit = (λq. None),
      fragment_next_id = 0⦈"

definition singleton_fragment :: "'gate ⇒ nat ⇒ 'gate dag_fragment" where
  "singleton_fragment gate k =
     ⦇fragment_num_wires = k,
      fragment_nodes =
        (λv. if v = 0
             then Some (OperationNode gate [0..<k])
             else None),
      fragment_edges = {},
      fragment_entry = (λq. if q < k then Some 0 else None),
      fragment_exit = (λq. if q < k then Some 0 else None),
      fragment_next_id = 1⦈"

lemma identity_fragment_num_wires[simp]:
  "fragment_num_wires (identity_fragment k) = k"
  unfolding identity_fragment_def
  by simp

lemma identity_fragment_has_no_nodes[simp]:
  "fragment_nodes (identity_fragment k) v = None"
  unfolding identity_fragment_def
  by simp

lemma identity_fragment_has_no_edges[simp]:
  "fragment_edges (identity_fragment k) = {}"
  unfolding identity_fragment_def
  by simp

lemma singleton_fragment_num_wires[simp]:
  "fragment_num_wires (singleton_fragment gate k) = k"
  unfolding singleton_fragment_def
  by simp

lemma singleton_fragment_root[simp]:
  "fragment_nodes (singleton_fragment gate k) 0 =
   Some (OperationNode gate [0..<k])"
  unfolding singleton_fragment_def
  by simp

lemma singleton_fragment_fresh_bound[simp]:
  "fragment_next_id (singleton_fragment gate k) = 1"
  unfolding singleton_fragment_def
  by simp

section ‹Renaming a fragment into a host circuit›

fun map_node_qubits ::
  "(qubit ⇒ qubit) ⇒ 'gate dag_node ⇒ 'gate dag_node"
where
  "map_node_qubits f (InputNode q) = InputNode (f q)"
| "map_node_qubits f (OutputNode q) = OutputNode (f q)"
| "map_node_qubits f (OperationNode gate qs) =
     OperationNode gate (map f qs)"

definition lift_fragment_node ::
  "'gate dag_fragment ⇒ node_id ⇒ (qubit ⇒ qubit) ⇒ node_id ⇒
   'gate dag_node option"
where
  "lift_fragment_node F offset wire_map v =
     (if offset ≤ v
      then map_option (map_node_qubits wire_map)
             (fragment_nodes F (v - offset))
      else None)"

definition lift_fragment_edge ::
  "node_id ⇒ (qubit ⇒ qubit) ⇒ dag_edge ⇒ dag_edge"
where
  "lift_fragment_edge offset wire_map e =
     mk_edge
       (offset + edge_source e)
       (offset + edge_target e)
       (wire_map (edge_qubit e))"

definition lifted_fragment_edges ::
  "'gate dag_fragment ⇒ node_id ⇒ (qubit ⇒ qubit) ⇒ dag_edge set"
where
  "lifted_fragment_edges F offset wire_map =
     lift_fragment_edge offset wire_map ` fragment_edges F"

lemma lift_fragment_edge_source[simp]:
  "edge_source (lift_fragment_edge offset f e) =
   offset + edge_source e"
  unfolding lift_fragment_edge_def
  by simp

lemma lift_fragment_edge_target[simp]:
  "edge_target (lift_fragment_edge offset f e) =
   offset + edge_target e"
  unfolding lift_fragment_edge_def
  by simp

lemma lift_fragment_edge_qubit[simp]:
  "edge_qubit (lift_fragment_edge offset f e) = f (edge_qubit e)"
  unfolding lift_fragment_edge_def
  by simp

end
