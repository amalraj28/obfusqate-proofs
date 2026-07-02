theory Transformations
  imports Fragments
begin

section ‹Cut specifications›

text ‹
  A cut is represented by an existing host edge. For local fragment wire i,
  cuts i is the host edge that will be removed and replaced by the fragment
  path for i. The edge label supplies the local-to-global wire mapping.
›

definition cut_wire_map :: "(qubit ⇒ dag_edge) ⇒ qubit ⇒ qubit" where
  "cut_wire_map cuts i = edge_qubit (cuts i)"

definition selected_cut_edges ::
  "nat ⇒ (qubit ⇒ dag_edge) ⇒ dag_edge set"
where
  "selected_cut_edges k cuts = cuts ` {..<k}"

definition valid_cuts ::
  "'gate quantum_circuit_dag ⇒ nat ⇒ (qubit ⇒ dag_edge) ⇒ bool"
where
  "valid_cuts G k cuts ⟷
     (∀i < k. cuts i ∈ dag_edges G) ∧
     inj_on (cut_wire_map cuts) {..<k}"

section ‹Bridge construction›

definition bridge_edges_for_wire ::
  "node_id ⇒ 'gate dag_fragment ⇒ dag_edge ⇒ qubit ⇒ dag_edge set"
where
  "bridge_edges_for_wire offset F cut i =
     (case (fragment_entry F i, fragment_exit F i) of
        (None, None) ⇒ {cut}
      | (Some first, Some last) ⇒
          {mk_edge (edge_source cut) (offset + first) (edge_qubit cut),
           mk_edge (offset + last) (edge_target cut) (edge_qubit cut)}
      | _ ⇒ {})"

definition fragment_bridge_edges ::
  "node_id ⇒ 'gate dag_fragment ⇒ (qubit ⇒ dag_edge) ⇒ dag_edge set"
where
  "fragment_bridge_edges offset F cuts =
     ⋃i ∈ {..<fragment_num_wires F}.
       bridge_edges_for_wire offset F (cuts i) i"

section ‹Node-map merge›

definition merge_fragment_nodes ::
  "'gate quantum_circuit_dag ⇒ 'gate dag_fragment ⇒
   (qubit ⇒ dag_edge) ⇒ node_id ⇒ 'gate dag_node option"
where
  "merge_fragment_nodes G F cuts v =
     (case dag_nodes G v of
        Some node ⇒ Some node
      | None ⇒
          lift_fragment_node F (dag_next_id G)
            (cut_wire_map cuts) v)"

section ‹Graph-native fragment insertion›

definition insert_fragment_at_cuts ::
  "'gate quantum_circuit_dag ⇒ 'gate dag_fragment ⇒
   (qubit ⇒ dag_edge) ⇒ 'gate quantum_circuit_dag"
where
  "insert_fragment_at_cuts G F cuts =
     ⦇dag_num_qubits = dag_num_qubits G,
      dag_nodes = merge_fragment_nodes G F cuts,
      dag_edges =
        (dag_edges G - selected_cut_edges (fragment_num_wires F) cuts) ∪
        lifted_fragment_edges F (dag_next_id G) (cut_wire_map cuts) ∪
        fragment_bridge_edges (dag_next_id G) F cuts,
      dag_next_id = dag_next_id G + fragment_next_id F⦈"

lemma insert_fragment_preserves_num_qubits[simp]:
  "dag_num_qubits (insert_fragment_at_cuts G F cuts) =
   dag_num_qubits G"
  unfolding insert_fragment_at_cuts_def
  by simp

lemma insert_fragment_advances_next_id[simp]:
  "dag_next_id (insert_fragment_at_cuts G F cuts) =
   dag_next_id G + fragment_next_id F"
  unfolding insert_fragment_at_cuts_def
  by simp

lemma insert_identity_fragment_nodes:
  "dag_nodes (insert_fragment_at_cuts G (identity_fragment k) cuts) =
   dag_nodes G"
  unfolding insert_fragment_at_cuts_def merge_fragment_nodes_def
    lift_fragment_node_def identity_fragment_def
  by (rule ext, auto split: option.splits)

lemma insert_identity_fragment_edges:
  assumes cuts_in_graph: "∀i < k. cuts i ∈ dag_edges G"
  shows "dag_edges (insert_fragment_at_cuts G (identity_fragment k) cuts) =
         dag_edges G"
proof -
  have bridges:
    "fragment_bridge_edges (dag_next_id G) (identity_fragment k) cuts =
     selected_cut_edges k cuts"
    unfolding fragment_bridge_edges_def bridge_edges_for_wire_def
      selected_cut_edges_def identity_fragment_def
    by auto
  show ?thesis
    using cuts_in_graph
    unfolding insert_fragment_at_cuts_def identity_fragment_def
      lifted_fragment_edges_def
    using bridges
    by auto
qed

lemma insert_identity_fragment_is_unchanged:
  assumes cuts_in_graph: "∀i < k. cuts i ∈ dag_edges G"
  shows "insert_fragment_at_cuts G (identity_fragment k) cuts = G"
  using insert_identity_fragment_nodes
    insert_identity_fragment_edges[OF cuts_in_graph]
  unfolding insert_fragment_at_cuts_def identity_fragment_def
  by (cases G, simp)

section ‹Operation-node replacement›

definition operation_qubits ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit list"
where
  "operation_qubits G v =
     (case dag_nodes G v of
        Some (OperationNode gate qs) ⇒ qs
      | _ ⇒ [])"

definition predecessor_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ node_id"
where
  "predecessor_on G v q =
     (THE u. mk_edge u v q ∈ dag_edges G)"

definition successor_on ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ node_id"
where
  "successor_on G v q =
     (THE w. mk_edge v w q ∈ dag_edges G)"

definition replacement_cut ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ dag_edge"
where
  "replacement_cut G v q =
     mk_edge (predecessor_on G v q) (successor_on G v q) q"

definition replacement_cuts ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ qubit ⇒ dag_edge"
where
  "replacement_cuts G v i =
     replacement_cut G v (operation_qubits G v ! i)"

definition replace_operation_with_fragment ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ 'gate dag_fragment ⇒
   'gate quantum_circuit_dag"
where
  "replace_operation_with_fragment G v F =
     insert_fragment_at_cuts (remove_node v G) F (replacement_cuts G v)"

definition replacement_applicable ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ 'gate dag_fragment ⇒ bool"
where
  "replacement_applicable G v F ⟷
     (∃gate qs.
        dag_nodes G v = Some (OperationNode gate qs) ∧
        length qs = fragment_num_wires F ∧
        (∀q ∈ set qs.
           has_unique_predecessor_on G v q ∧
           has_unique_successor_on G v q))"

lemma replace_operation_preserves_num_qubits[simp]:
  "dag_num_qubits (replace_operation_with_fragment G v F) =
   dag_num_qubits G"
  unfolding replace_operation_with_fragment_def
  by simp

lemma replaced_node_is_removed_before_splicing:
  "dag_nodes (remove_node v G) v = None"
  by simp

section ‹Convenience transformations›

definition insert_single_operation ::
  "'gate quantum_circuit_dag ⇒ 'gate ⇒ nat ⇒
   (qubit ⇒ dag_edge) ⇒ 'gate quantum_circuit_dag"
where
  "insert_single_operation G gate arity cuts =
     insert_fragment_at_cuts G (singleton_fragment gate arity) cuts"

definition replace_operation_with_single ::
  "'gate quantum_circuit_dag ⇒ node_id ⇒ 'gate ⇒ nat ⇒
   'gate quantum_circuit_dag"
where
  "replace_operation_with_single G v gate arity =
     replace_operation_with_fragment G v (singleton_fragment gate arity)"

lemma insert_single_operation_next_id[simp]:
  "dag_next_id (insert_single_operation G gate arity cuts) =
   dag_next_id G + 1"
  unfolding insert_single_operation_def
  by simp

end
