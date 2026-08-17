theory Quantum_Circuit_Subcircuit_Replace_Acyclicity
  imports Quantum_Circuit_Subcircuit_Replace_Core

begin

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

end
