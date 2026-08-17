theory Quantum_Circuit_Navigation
  imports Quantum_Circuit_Insert_Validity

begin



definition incoming_edge ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> edge option"
  where
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
  "predecessor_on_wire circuit node_id q =
     map_option edge_source
       (incoming_edge circuit node_id q)"

definition successor_on_wire ::
  "quantum_circuit \<Rightarrow> node_id \<Rightarrow> qubit \<Rightarrow> node_id option"
where
  "successor_on_wire circuit node_id q =
     map_option edge_target
       (outgoing_edge circuit node_id q)"

lemma incoming_edge_correct:
  "incoming_edge circuit node_id q = Some e
   \<Longrightarrow> e \<in> edges circuit
     \<and> edge_target e = node_id
     \<and> edge_wire e = q"
  sorry

lemma outgoing_edge_correct:
  "outgoing_edge circuit node_id q = Some e
   \<Longrightarrow> e \<in> edges circuit
     \<and> edge_source e = node_id
     \<and> edge_wire e = q"

sorry

lemma predecessor_on_wire_correct:
  "predecessor_on_wire circuit node_id q = Some predecessor
   \<Longrightarrow> make_edge predecessor node_id q \<in> edges circuit"

sorry

lemma successor_on_wire_correct:
  "successor_on_wire circuit node_id q = Some successor
   \<Longrightarrow> make_edge node_id successor q \<in> edges circuit"

sorry

lemma predecessor_on_wire_not_self:
  assumes acyclic:
    "is_acyclic_circuit circuit"

  assumes predecessor:
    "predecessor_on_wire circuit node_id q =
       Some predecessor_node"

  shows
    "predecessor_node \<noteq> node_id"
sorry

lemma successor_on_wire_not_self:
  assumes acyclic:
    "is_acyclic_circuit circuit"

  assumes successor:
    "successor_on_wire circuit node_id q =
       Some successor_node"

  shows
    "successor_node \<noteq> node_id"
sorry

end
