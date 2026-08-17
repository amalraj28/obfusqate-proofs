theory Quantum_Circuit_Insert_Validity
  imports Quantum_Circuit_Insert_Core

begin

lemma wire_node_reaches_frontier_or_is_output:
  (* On a linear wire with a valid frontier, every existing node using q
     is either:
       1. the output node;
       2. the frontier node itself; or
       3. ordered before the frontier and therefore reaches it.

     The alternative that the frontier reaches the chosen node is
     impossible unless that node is the output, because the frontier has
     a direct edge to the output and the output has no outgoing q-edge.
  *)
  assumes linear_before:
    "wire_is_linear circuit q"

assumes frontier_valid:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes node_lookup:
  "nodes circuit node_id = Some node_value"

assumes node_uses_q:
  "node_uses_qubit node_value q"

assumes frontier_unique_successor:
  (* The frontier-to-output edge is the frontier node's only immediate
       outgoing edge on q. *)
  "has_unique_wire_successor circuit q (frontier q)"

shows
  "node_id = get_output_node_id q
       \<or> node_id = frontier q
       \<or> wire_reaches circuit q node_id (frontier q)"

proof -
  have comparable:
    "nodes_comparable_on_wire circuit q"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  from frontier_valid q_valid
  obtain frontier_node where
    frontier_lookup:
    "nodes circuit (frontier q) = Some frontier_node"
    and frontier_uses_q:
    "node_uses_qubit frontier_node q"
    and frontier_output_edge:
    "make_edge
         (frontier q)
         (get_output_node_id q)
         q
       \<in> edges circuit"
    unfolding is_valid_frontier_def
    by blast

  have frontier_reaches_output:
    "wire_reaches
       circuit q
       (frontier q)
       (get_output_node_id q)"
    unfolding
      wire_reaches_def
      wire_edge_relation_def
    using frontier_output_edge
    by (simp add: r_into_trancl)

  from comparable
    node_lookup
    frontier_lookup
    node_uses_q
    frontier_uses_q
  have ordering:
    "node_id = frontier q
     \<or> wire_reaches circuit q node_id (frontier q)
     \<or> wire_reaches circuit q (frontier q) node_id"
    unfolding nodes_comparable_on_wire_def
    by simp

  from ordering consider
    (same)
    "node_id = frontier q"
    | (before)
      "wire_reaches circuit q node_id (frontier q)"
    | (after)
      "wire_reaches circuit q (frontier q) node_id"
    by blast

  then show ?thesis
  proof cases
    case same

    then show ?thesis
      by simp

  next
    case before

    then show ?thesis
      by simp

  next
    case after

    have output_has_no_successor:
      "\<nexists>successor_id.
         (get_output_node_id q, successor_id)
           \<in> wire_edge_relation circuit q"
      using linear_before
      unfolding wire_is_linear_def
      by simp

    have frontier_output_relation:
      "(frontier q, get_output_node_id q)
         \<in> wire_edge_relation circuit q"
      using frontier_output_edge
      unfolding wire_edge_relation_def
      by simp

    have frontier_successor_is_output:
      "\<And>successor_id.
         (frontier q, successor_id)
           \<in> wire_edge_relation circuit q
         \<Longrightarrow> successor_id = get_output_node_id q"
      using
        frontier_unique_successor
        frontier_output_relation
      unfolding has_unique_wire_successor_def
      by auto

    have frontier_reaches_only_output:
      "\<And>target_id.
         wire_reaches circuit q (frontier q) target_id
         \<Longrightarrow> target_id = get_output_node_id q"
    proof -
      fix target_id

      assume reaches_target:
        "wire_reaches circuit q (frontier q) target_id"

      then have path:
        "(frontier q, target_id)
           \<in> (wire_edge_relation circuit q)\<^sup>+"
        unfolding wire_reaches_def
        .

      then show
        "target_id = get_output_node_id q"
      proof (induction rule: trancl_induct)
        case base

        then show ?case
          using frontier_successor_is_output
          by blast

      next
        case (step intermediate_id final_id)

        from step.IH have intermediate_is_output:
          "intermediate_id = get_output_node_id q"
          .

        from step.hyps have
          "(intermediate_id, final_id)
             \<in> wire_edge_relation circuit q"
          by simp

        then have
          "(get_output_node_id q, final_id)
             \<in> wire_edge_relation circuit q"
          using intermediate_is_output
          by simp

        with output_has_no_successor show ?case
          by blast
      qed
    qed

    have node_is_output:
      "node_id = get_output_node_id q"
      using after
      by (rule frontier_reaches_only_output)

    then show ?thesis
      by simp
  qed
qed

lemma subdividing_final_edge_preserves_old_reachability:
  (* Replacing frontier-to-output by frontier-to-new-to-output preserves
     every directed path that existed before subdivision.

     Any old path that did not use the removed edge remains unchanged.
     Any old path that used the removed edge can replace that edge by
     the two new edges.
  *)
  assumes old_reachability:
    "wire_reaches circuit q node_a node_b"

assumes output_has_no_successor:
  "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "wire_reaches updated_circuit q node_a node_b"

proof -
  let ?old_relation =
    "wire_edge_relation circuit q"

  let ?new_relation =
    "wire_edge_relation updated_circuit q"

  have every_old_edge_has_new_path:
    "\<And>source_id target_id.
       (source_id, target_id) \<in> ?old_relation
       \<Longrightarrow>
       (source_id, target_id) \<in> ?new_relation\<^sup>+"
  proof -
    fix source_id target_id

    assume old_edge:
      "(source_id, target_id) \<in> ?old_relation"

    show
      "(source_id, target_id) \<in> ?new_relation\<^sup>+"
    proof (
        cases
        "(source_id, target_id) =
         (frontier q, get_output_node_id q)"
        )
      case True

      have frontier_to_new:
        "(frontier q, new_node_id) \<in> ?new_relation"
        using relation_after
        by simp

      have new_to_output:
        "(new_node_id, get_output_node_id q) \<in> ?new_relation"
        using relation_after
        by simp

      have frontier_reaches_new:
        "(frontier q, new_node_id) \<in> ?new_relation\<^sup>+"
        using frontier_to_new
        by (rule r_into_trancl)

      have frontier_reaches_output:
        "(frontier q, get_output_node_id q)
          \<in> ?new_relation\<^sup>+"
        using frontier_reaches_new new_to_output
        by (rule trancl_into_trancl)

      show ?thesis
        using True frontier_reaches_output
        by simp

    next
      case False

      have edge_still_exists:
        "(source_id, target_id) \<in> ?new_relation"
        using
          old_edge
          False
          relation_after
        by auto

      then show ?thesis
        by (rule r_into_trancl)
    qed
  qed

  from old_reachability have old_path:
    "(node_a, node_b) \<in> ?old_relation\<^sup>+"
    unfolding wire_reaches_def
    .

  have new_path:
    "(node_a, node_b) \<in> ?new_relation\<^sup>+"
    using old_path
  proof (induction rule: trancl_induct)
    case base

    then show ?case
      using every_old_edge_has_new_path
      by blast

  next
    case step

    then show ?case
      using
        every_old_edge_has_new_path
        trancl_trans
      by metis
  qed

  show ?thesis
    using new_path
    unfolding wire_reaches_def
    .
qed

lemma subdividing_final_edge_preserves_wire_comparability:
  (* Subdividing the final frontier-to-output edge of a linear wire by
     one previously unused node preserves comparability of all nodes
     using that wire.

     Every old node retains its original ordering relative to every
     other old node. Any old path that previously ended with

         frontier_node \<rightarrow> output_node

     can instead use

         frontier_node \<rightarrow> new_node_id \<rightarrow> output_node.

     The inserted node is after every old non-output node on the wire
     and before the output boundary node.
  *)
  assumes comparable_before:
    "nodes_comparable_on_wire circuit q"

assumes circuit_well_formed:
  "is_well_formed_circuit circuit"

assumes linear_before:
  "wire_is_linear circuit q"

assumes frontier_valid:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused:
  "nodes circuit new_node_id = None"

assumes new_node_exists_after:
  "nodes updated_circuit new_node_id = Some new_node"

assumes new_node_uses_q:
  "node_uses_qubit new_node q"

assumes old_nodes_unchanged:
  "\<And>node_id.
         node_id \<noteq> new_node_id
         \<Longrightarrow> nodes updated_circuit node_id =
             nodes circuit node_id"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
         insert
           (new_node_id, get_output_node_id q)
           (insert
             (frontier q, new_node_id)
             (wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}))"

shows
  "nodes_comparable_on_wire updated_circuit q"

proof -
  have frontier_to_new_edge:
    "(frontier q, new_node_id)
       \<in> wire_edge_relation updated_circuit q"
    using relation_after
    by simp

  have new_to_output_edge:
    "(new_node_id, get_output_node_id q)
       \<in> wire_edge_relation updated_circuit q"
    using relation_after
    by simp

  have frontier_reaches_new:
    "wire_reaches updated_circuit q (frontier q) new_node_id"
    unfolding wire_reaches_def
    using frontier_to_new_edge
    by (rule r_into_trancl)

  have new_reaches_output:
    "wire_reaches
       updated_circuit q
       new_node_id
       (get_output_node_id q)"
    unfolding wire_reaches_def
    using new_to_output_edge
    by (rule r_into_trancl)

  show ?thesis
    unfolding nodes_comparable_on_wire_def
  proof (intro allI impI)
    fix node_a node_b node_a_value node_b_value

    assume node_a_lookup_after:
      "nodes updated_circuit node_a = Some node_a_value"

    assume node_b_lookup_after:
      "nodes updated_circuit node_b = Some node_b_value"

    assume node_a_uses_q:
      "node_uses_qubit node_a_value q"

    assume node_b_uses_q:
      "node_uses_qubit node_b_value q"

    show
      "node_a = node_b
       \<or> wire_reaches updated_circuit q node_a node_b
       \<or> wire_reaches updated_circuit q node_b node_a"
    proof (cases "node_a = new_node_id")
      case True

      have node_a_value_is_new:
        "node_a_value = new_node"
        using
          node_a_lookup_after
          new_node_exists_after
          True
        by simp

      show ?thesis
      proof (cases "node_b = new_node_id")
        case True

        then show ?thesis
          using \<open>node_a = new_node_id\<close>
          by simp

      next
        case False

        have node_b_not_new:
          "node_b \<noteq> new_node_id"
          using False .

        have node_b_lookup_before:
          "nodes circuit node_b = Some node_b_value"
          using
            node_b_lookup_after
            old_nodes_unchanged[OF False]
          by simp

        have node_b_position:
          "node_b = get_output_node_id q
           \<or> node_b = frontier q
           \<or> wire_reaches circuit q node_b (frontier q)"
          using
            linear_before
            frontier_valid
            q_valid
            node_b_lookup_before
            node_b_uses_q
            valid_frontier_has_unique_successor
            wire_node_reaches_frontier_or_is_output
          by simp

        from node_b_position consider
          (output_node_b)
          "node_b = get_output_node_id q"
          | (frontier)
            "node_b = frontier q"
          | (before_frontier)
            "wire_reaches circuit q node_b (frontier q)"
          by auto

        then show ?thesis
        proof cases
          case output_node_b

          have
            "wire_reaches updated_circuit q node_a node_b"
            using
              True
              output_node_b
              new_reaches_output
            by simp

          then show ?thesis
            by simp

        next
          case frontier

          have
            "wire_reaches updated_circuit q node_b node_a"
            using
              True
              frontier
              frontier_reaches_new
            by simp

          then show ?thesis
            by blast

        next
          case before_frontier

          have node_b_reaches_frontier_after:
            "wire_reaches
               updated_circuit q
               node_b
               (frontier q)"
            using
              before_frontier
              relation_after
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          have node_b_reaches_new:
            "wire_reaches
               updated_circuit q
               node_b
               new_node_id"
          proof -
            have old_path:
              "(node_b, frontier q)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using node_b_reaches_frontier_after
              unfolding wire_reaches_def
              by simp

            have
              "(node_b, new_node_id)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using old_path frontier_to_new_edge
              by (rule trancl_into_trancl)

            then show ?thesis
              unfolding wire_reaches_def
              .
          qed

          have
            "wire_reaches updated_circuit q node_b node_a"
            using True node_b_reaches_new
            by simp

          then show ?thesis
            by simp
        qed
      qed

    next
      case False

      have node_a_not_new:
        "node_a \<noteq> new_node_id"
        using False .

      have node_a_lookup_before:
        "nodes circuit node_a = Some node_a_value"
        using
          node_a_lookup_after
          old_nodes_unchanged[OF False]
        by simp

      show ?thesis
      proof (cases "node_b = new_node_id")
        case True

        have node_b_value_is_new:
          "node_b_value = new_node"
          using
            node_b_lookup_after
            new_node_exists_after
            True
          by simp

        have node_a_position:
          "node_a = get_output_node_id q
           \<or> node_a = frontier q
           \<or> wire_reaches circuit q node_a (frontier q)"
          using
            linear_before
            frontier_valid
            q_valid
            node_a_lookup_before
            node_a_uses_q
            valid_frontier_has_unique_successor
            wire_node_reaches_frontier_or_is_output
          by simp

        from node_a_position consider
          (output_node_a)
          "node_a = get_output_node_id q"
          | (frontier)
            "node_a = frontier q"
          | (before_frontier)
            "wire_reaches circuit q node_a (frontier q)"
          by auto

        then show ?thesis
        proof cases
          case output_node_a

          have
            "wire_reaches updated_circuit q node_b node_a"
            using
              True
              output_node_a
              new_reaches_output
            by simp

          then show ?thesis
            by simp

        next
          case frontier

          have
            "wire_reaches updated_circuit q node_a node_b"
            using
              True
              frontier
              frontier_reaches_new
            by simp

          then show ?thesis
            by simp

        next
          case before_frontier

          have node_a_reaches_frontier_after:
            "wire_reaches
               updated_circuit q
               node_a
               (frontier q)"
            using
              before_frontier
              relation_after
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          have node_a_reaches_new:
            "wire_reaches
               updated_circuit q
               node_a
               new_node_id"
          proof -
            have old_path:
              "(node_a, frontier q)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using node_a_reaches_frontier_after
              unfolding wire_reaches_def
              .

            have
              "(node_a, new_node_id)
                 \<in> (wire_edge_relation updated_circuit q)\<^sup>+"
              using old_path frontier_to_new_edge
              by (rule trancl_into_trancl)

            then show ?thesis
              unfolding wire_reaches_def
              .
          qed

          have
            "wire_reaches updated_circuit q node_a node_b"
            using True node_a_reaches_new
            by simp

          then show ?thesis
            by blast
        qed

      next
        case False

        have node_b_lookup_before:
          "nodes circuit node_b = Some node_b_value"
          using
            node_b_lookup_after
            old_nodes_unchanged[OF False]
          by simp

        from comparable_before
          node_a_lookup_before
          node_b_lookup_before
          node_a_uses_q
          node_b_uses_q
        have old_comparability:
          "node_a = node_b
           \<or> wire_reaches circuit q node_a node_b
           \<or> wire_reaches circuit q node_b node_a"
          unfolding nodes_comparable_on_wire_def
          by blast

        from old_comparability consider
          (same)
          "node_a = node_b"
          | (a_before_b)
            "wire_reaches circuit q node_a node_b"
          | (b_before_a)
            "wire_reaches circuit q node_b node_a"
          by auto

        then show ?thesis
        proof cases
          case same

          then show ?thesis
            by simp

        next
          case a_before_b

          have
            "wire_reaches updated_circuit q node_a node_b"
            using
              a_before_b
              relation_after
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          then show ?thesis
            by simp

        next
          case b_before_a

          have
            "wire_reaches updated_circuit q node_b node_a"
            using
              b_before_a
              relation_after
            using
              linear_before
              subdividing_final_edge_preserves_old_reachability
              wire_is_linear_def
            by simp

          then show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed

lemma subdividing_final_edge_preserves_input_boundary:
  (* Subdividing the final frontier-to-output edge of a linear wire
     preserves both input-boundary conditions.

     The input node still has no predecessor on q.

     It also still has exactly one successor:
       - if the input node is not the frontier, its outgoing edge is
         unchanged;
       - if the input node is the frontier, its old edge to the output
         node is replaced by exactly one edge to new_node_id.
  *)
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused_before:
  "nodes circuit new_node_id = None"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
           insert
             (new_node_id, get_output_node_id q)
             (insert
               (frontier q, new_node_id)
               (wire_edge_relation circuit q -
                  {(frontier q, get_output_node_id q)}))"

assumes new_node_not_input:
  (* The newly allocated internal node cannot use the canonical input
         boundary-node ID. *)
  "new_node_id \<noteq> get_input_node_id q"

shows
  "(\<nexists>predecessor_id.
            (predecessor_id, get_input_node_id q)
              \<in> wire_edge_relation updated_circuit q)
         \<and>
         has_unique_wire_successor
           updated_circuit q (get_input_node_id q)"

proof -
  have input_node_has_no_predecessor:
    "(\<nexists>predecessor_id.
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation circuit q)
     \<and>
     has_unique_wire_successor
       circuit q (get_input_node_id q)"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have output_not_input:
    (* The canonical output and input IDs of the same wire are distinct. *)
    "get_output_node_id q \<noteq> get_input_node_id q"
    using
      get_output_node_id_def
      get_input_node_id_def
    by simp

  show ?thesis
  proof (cases "frontier q = get_input_node_id q")
    case True

    have no_input_predecessor_after:
      "\<nexists>predecessor_id.
         (predecessor_id, get_input_node_id q)
           \<in> wire_edge_relation updated_circuit q"

    proof
      assume
        "\<exists>predecessor_id.
           (predecessor_id, get_input_node_id q)
             \<in> wire_edge_relation updated_circuit q"

      then obtain predecessor_id where predecessor_edge_after:
        "(predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation updated_circuit q"
        by auto

      from predecessor_edge_after relation_after have
        "(predecessor_id, get_input_node_id q)
          =
          (new_node_id, get_output_node_id q)
       \<or>
        (predecessor_id, get_input_node_id q)
          =
          (frontier q, new_node_id)
       \<or>
        (predecessor_id, get_input_node_id q)
          \<in> wire_edge_relation circuit q -
             {(frontier q, get_output_node_id q)}"
        by simp

      have no_input_predecessor_before:
        "\<nexists>predecessor_id.
           (predecessor_id, get_input_node_id q)
             \<in> wire_edge_relation circuit q"
        using input_node_has_no_predecessor
        by simp

      from
        \<open>(predecessor_id, get_input_node_id q)
            =
            (new_node_id, get_output_node_id q)
         \<or>
          (predecessor_id, get_input_node_id q)
            =
            (frontier q, new_node_id)
         \<or>
          (predecessor_id, get_input_node_id q)
            \<in> wire_edge_relation circuit q -
               {(frontier q, get_output_node_id q)}\<close>
      show False
        using
          output_not_input
          new_node_not_input
          no_input_predecessor_before
        by auto
    qed

    have unique_input_successor_before:
      "has_unique_wire_successor
         circuit q (get_input_node_id q)"
      using input_node_has_no_predecessor
      by simp

    have old_frontier_output_edge:
      "(frontier q, get_output_node_id q)
        \<in> wire_edge_relation circuit q"
      using valid_frontier_before q_valid
      unfolding
        is_valid_frontier_def
        wire_edge_relation_def
      by auto

    have old_input_output_edge:
      "(get_input_node_id q, get_output_node_id q)
        \<in> wire_edge_relation circuit q"
      using old_frontier_output_edge True
      by simp

    have old_input_successor_is_output:
      "\<And>successor_id.
         (get_input_node_id q, successor_id)
           \<in> wire_edge_relation circuit q
         \<Longrightarrow> successor_id = get_output_node_id q"
      using
        unique_input_successor_before
        old_input_output_edge
      unfolding has_unique_wire_successor_def
      by auto

    have unique_input_successor_after:
      "has_unique_wire_successor
         updated_circuit q (get_input_node_id q)"
      unfolding has_unique_wire_successor_def
    proof (rule ex1I[of _ new_node_id])

      show
        "(get_input_node_id q, new_node_id)
          \<in> wire_edge_relation updated_circuit q"
        using relation_after True
        by simp

    next
      fix successor_id

      assume successor_edge_after:
        "(get_input_node_id q, successor_id)
          \<in> wire_edge_relation updated_circuit q"

      from
        successor_edge_after
        relation_after
      have successor_cases:
        "(get_input_node_id q, successor_id)
            =
            (new_node_id, get_output_node_id q)
         \<or>
          (get_input_node_id q, successor_id)
            =
            (frontier q, new_node_id)
         \<or>
          (get_input_node_id q, successor_id)
            \<in> wire_edge_relation circuit q -
               {(frontier q, get_output_node_id q)}"
        by simp

      from successor_cases consider
        (first)
        "(get_input_node_id q, successor_id)
             =
           (new_node_id, get_output_node_id q)"
        | (second)
          "(get_input_node_id q, successor_id)
             =
           (frontier q, new_node_id)"
        | (third)
          "(get_input_node_id q, successor_id)
             \<in> wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}"
        by auto

      then show "successor_id = new_node_id"
      proof cases
        case first

        from first have
          "get_input_node_id q = new_node_id"
          by simp

        with new_node_not_input show ?thesis
          by simp

      next
        case second

        then show ?thesis
          using True
          by simp

      next
        case third

        from third have old_edge:
          "(get_input_node_id q, successor_id)
             \<in> wire_edge_relation circuit q"
          by simp

        from old_input_successor_is_output[OF old_edge]
        have successor_is_output:
          "successor_id = get_output_node_id q"
          .

        from third have edge_not_removed:
          "(get_input_node_id q, successor_id)
             \<noteq>
           (frontier q, get_output_node_id q)"
          by simp

        show ?thesis
          using
            edge_not_removed
            True
            successor_is_output
          by simp
      qed
    qed

    show ?thesis
      using
        no_input_predecessor_after
        unique_input_successor_after
      by simp

  next
    case False

    have input_predecessor_edges_unchanged:
      (* Since neither newly inserted edge targets the input node, and the removed edge targets the output node, subdivision does not alter any edge entering the input node. *)
      "((predecessor_id, get_input_node_id q) \<in> wire_edge_relation updated_circuit q)
       \<longleftrightarrow>
        ((predecessor_id, get_input_node_id q) \<in> wire_edge_relation circuit q)"
      for predecessor_id
      using
        relation_after
        output_not_input
        new_node_not_input
      by simp

    have no_input_predecessor_after:
      "\<nexists>predecessor_id.
     (predecessor_id, get_input_node_id q)
       \<in> wire_edge_relation updated_circuit q"
    proof
      assume predecessor_exists_after:
        "\<exists>predecessor_id.
       (predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation updated_circuit q"

      then obtain predecessor_id where predecessor_after:
        "(predecessor_id, get_input_node_id q)
      \<in> wire_edge_relation updated_circuit q"
        by blast

      from input_predecessor_edges_unchanged predecessor_after have
        "(predecessor_id, get_input_node_id q)
      \<in> wire_edge_relation circuit q"
        by blast

      moreover from input_node_has_no_predecessor have
        "\<nexists>predecessor_id.
       (predecessor_id, get_input_node_id q)
         \<in> wire_edge_relation circuit q"
        by simp

      ultimately show False
        by blast
    qed

    have input_successor_edges_unchanged:
      (* Because the frontier is not the input node, the removed edge is not
     an outgoing input edge. Neither inserted edge has the input node as
     its source, because both frontier and new_node_id differ from the
     input node. *)
      "((get_input_node_id q, successor_id)
      \<in> wire_edge_relation updated_circuit q)
   \<longleftrightarrow>
   ((get_input_node_id q, successor_id)
      \<in> wire_edge_relation circuit q)"
      for successor_id
      using
        relation_after
        False
        new_node_not_input
      by auto

    have unique_input_successor_after:
      "has_unique_wire_successor
     updated_circuit q (get_input_node_id q)"
    proof -
      from input_node_has_no_predecessor have unique_before:
        "has_unique_wire_successor
       circuit q (get_input_node_id q)"
        by simp

      show ?thesis
        using unique_before input_successor_edges_unchanged
        unfolding has_unique_wire_successor_def
        by blast
    qed

    show ?thesis
      using
        no_input_predecessor_after
        unique_input_successor_after
      by simp

  qed
qed

lemma subdividing_final_edge_preserves_output_no_successor:
  (* Subdividing the final edge does not introduce any outgoing edge
     from the output node. Therefore, the output node continues to have
     no successor on q.

     The valid frontier supplies the old frontier-to-output edge.
     Since the output previously had no successor, the frontier cannot
     itself be the output node. The newly inserted node is also assumed
     to have a different ID from the output boundary node.
  *)
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_not_output:
  "new_node_id \<noteq> get_output_node_id q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation updated_circuit q"

proof -
  have no_output_successor_before:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have frontier_output_edge_before:
    "(frontier q, get_output_node_id q)
       \<in> wire_edge_relation circuit q"
    using valid_frontier_before q_valid
    unfolding
      is_valid_frontier_def
      wire_edge_relation_def
    by auto

  have frontier_not_output:
    "frontier q \<noteq> get_output_node_id q"
  proof
    assume frontier_is_output:
      "frontier q = get_output_node_id q"

    from frontier_output_edge_before frontier_is_output have
      "(get_output_node_id q, get_output_node_id q)
         \<in> wire_edge_relation circuit q"
      by simp

    with no_output_successor_before show False
      by blast
  qed

  show ?thesis
    using
      relation_after
      no_output_successor_before
      new_node_not_output
      frontier_not_output
    by auto
qed

lemma subdividing_final_edge_preserves_output_predecessor:
  (* Subdividing the final frontier-to-output edge preserves the unique
     predecessor of the output node.

     Before subdivision, frontier(q) is the unique predecessor of the
     output node.

     After subdivision, the old edge

         frontier(q) \<rightarrow> output(q)

     is removed and replaced by

         frontier(q) \<rightarrow> new_node_id
         new_node_id \<rightarrow> output(q).

     Therefore, new_node_id becomes the unique predecessor of the
     output node.
  *)
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_not_output:
  "new_node_id \<noteq> get_output_node_id q"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

shows
  "has_unique_wire_predecessor
       updated_circuit q (get_output_node_id q)"

proof -
  have unique_output_predecessor_before:
    "has_unique_wire_predecessor
       circuit q (get_output_node_id q)"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have frontier_output_edge_before:
    "(frontier q, get_output_node_id q)
       \<in> wire_edge_relation circuit q"
    using valid_frontier_before q_valid
    unfolding
      is_valid_frontier_def
      wire_edge_relation_def
    by auto

  have old_output_predecessor_is_frontier:
    "\<And>predecessor_id.
       (predecessor_id, get_output_node_id q)
         \<in> wire_edge_relation circuit q
       \<Longrightarrow> predecessor_id = frontier q"
    using
      unique_output_predecessor_before
      frontier_output_edge_before
    unfolding has_unique_wire_predecessor_def
    by blast

  show ?thesis
    unfolding has_unique_wire_predecessor_def
  proof (rule ex1I[of _ new_node_id])

    show
      "(new_node_id, get_output_node_id q)
         \<in> wire_edge_relation updated_circuit q"
      using relation_after
      by simp

  next
    fix predecessor_id

    assume predecessor_edge_after:
      "(predecessor_id, get_output_node_id q)
         \<in> wire_edge_relation updated_circuit q"

    from predecessor_edge_after relation_after have predecessor_cases:
      "(predecessor_id, get_output_node_id q)
          =
        (new_node_id, get_output_node_id q)
       \<or>
       (predecessor_id, get_output_node_id q)
          =
        (frontier q, new_node_id)
       \<or>
       (predecessor_id, get_output_node_id q)
          \<in> wire_edge_relation circuit q -
             {(frontier q, get_output_node_id q)}"
      by auto

    from predecessor_cases consider
      (new_edge)
      "(predecessor_id, get_output_node_id q)
             =
           (new_node_id, get_output_node_id q)"
      | (frontier_new_edge)
        "(predecessor_id, get_output_node_id q)
             =
           (frontier q, new_node_id)"
      | (old_edge)
        "(predecessor_id, get_output_node_id q)
             \<in> wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}"
      by blast

    then show "predecessor_id = new_node_id"
    proof cases
      case new_edge

      then show ?thesis
        by simp

    next
      case frontier_new_edge

      from frontier_new_edge have
        "get_output_node_id q = new_node_id"
        by simp

      with new_node_not_output show ?thesis
        by simp

    next
      case old_edge

      from old_edge have old_output_edge:
        "(predecessor_id, get_output_node_id q)
           \<in> wire_edge_relation circuit q"
        by simp

      from old_output_predecessor_is_frontier[OF old_output_edge]
      have predecessor_is_frontier:
        "predecessor_id = frontier q"
        .

      from old_edge have edge_not_removed:
        "(predecessor_id, get_output_node_id q)
           \<noteq>
         (frontier q, get_output_node_id q)"
        by simp

      from edge_not_removed predecessor_is_frontier
      show ?thesis
        by simp
    qed
  qed
qed

lemma subdividing_final_edge_preserves_operation_node_degrees:
  (* Subdividing the final edge of a linear wire preserves the required
     predecessor and successor degrees of every operation node using q.

     For old operation nodes:
       - nodes other than the old frontier keep their q-labelled edges;
       - if the old frontier is an operation node, its old successor
         output(q) is replaced by the single successor new_node_id.

     For the newly inserted operation node:
       - frontier(q) is its unique predecessor;
       - output(q) is its unique successor.
  *)
  assumes linear_before:
    "wire_is_linear circuit q"

assumes valid_frontier_before:
  "is_valid_frontier circuit frontier"

assumes q_valid:
  "qubit_in_circuit circuit q"

assumes new_node_unused_before:
  "nodes circuit new_node_id = None"

assumes new_node_exists_after:
  "nodes updated_circuit new_node_id =
         Some (OperationNode new_op)"

assumes new_node_uses_q:
  "node_uses_qubit (OperationNode new_op) q"

assumes circuit_well_formed:
  "is_well_formed_circuit circuit"

assumes old_nodes_unchanged:
  "\<And>node_id.
         node_id \<noteq> new_node_id
         \<Longrightarrow> nodes updated_circuit node_id =
             nodes circuit node_id"

assumes relation_after:
  "wire_edge_relation updated_circuit q =
         insert
           (new_node_id, get_output_node_id q)
           (insert
             (frontier q, new_node_id)
             (wire_edge_relation circuit q -
                {(frontier q, get_output_node_id q)}))"

shows
  "\<forall>node_id stored_op.
         nodes updated_circuit node_id =
           Some (OperationNode stored_op)
         \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
         \<longrightarrow> has_unique_wire_predecessor
               updated_circuit q node_id
           \<and> has_unique_wire_successor
               updated_circuit q node_id"

proof -
  have old_operation_degrees:
    "\<forall>node_id stored_op.
       nodes circuit node_id = Some (OperationNode stored_op)
       \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
       \<longrightarrow> has_unique_wire_predecessor circuit q node_id
         \<and> has_unique_wire_successor circuit q node_id"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have old_output_has_no_successor:
    "\<nexists>successor_id.
       (get_output_node_id q, successor_id)
         \<in> wire_edge_relation circuit q"
    using linear_before
    unfolding wire_is_linear_def
    by simp

  have old_edges_well_formed:
    "are_well_formed_edges circuit"
    using circuit_well_formed
    unfolding is_well_formed_circuit_def
    by simp

  have no_old_edge_to_new_node:
    "\<And>source_id.
       (source_id, new_node_id)
         \<notin> wire_edge_relation circuit q"
  proof
    fix source_id

    assume old_edge:
      "(source_id, new_node_id)
        \<in> wire_edge_relation circuit q"

    then have edge_in:
      "make_edge source_id new_node_id q
        \<in> edges circuit"
      unfolding wire_edge_relation_def
      by simp

    from old_edges_well_formed edge_in have
      "node_exists circuit new_node_id"
      unfolding
        are_well_formed_edges_def
        is_well_formed_edge_def
        make_edge_def
      by auto

    then have
      "nodes circuit new_node_id \<noteq> None"
      unfolding node_exists_def
      .

    with new_node_unused_before show False
      by simp
  qed

  have no_old_edge_from_new_node:
    "\<And>target_id.
       (new_node_id, target_id)
         \<notin> wire_edge_relation circuit q"
  proof
    fix target_id

    assume old_edge:
      "(new_node_id, target_id)
        \<in> wire_edge_relation circuit q"

    then have edge_in:
      "make_edge new_node_id target_id q
        \<in> edges circuit"
      unfolding wire_edge_relation_def
      by simp

    from old_edges_well_formed edge_in have
      "node_exists circuit new_node_id"
      unfolding
        are_well_formed_edges_def
        is_well_formed_edge_def
        make_edge_def
      by auto

    then have
      "nodes circuit new_node_id \<noteq> None"
      unfolding node_exists_def
      .

    with new_node_unused_before show False
      by simp
  qed

  have old_frontier_output_edge:
    "(frontier q, get_output_node_id q)
      \<in> wire_edge_relation circuit q"
    using valid_frontier_before q_valid
    unfolding
      is_valid_frontier_def
      wire_edge_relation_def
    by auto

  have frontier_not_new:
    "frontier q \<noteq> new_node_id"
  proof
    assume
      "frontier q = new_node_id"

    with old_frontier_output_edge have
      "(new_node_id, get_output_node_id q)
        \<in> wire_edge_relation circuit q"
      by simp

    with no_old_edge_from_new_node show False
      by blast
  qed

  have output_not_new:
    "get_output_node_id q \<noteq> new_node_id"
  proof
    assume
      "get_output_node_id q = new_node_id"

    with old_frontier_output_edge have
      "(frontier q, new_node_id)
        \<in> wire_edge_relation circuit q"
      by simp

    with no_old_edge_to_new_node show False
      by blast
  qed

  show ?thesis
  proof (intro allI impI)
    fix node_id stored_op

    assume operation_lookup_after:
      "nodes updated_circuit node_id =
       Some (OperationNode stored_op)"

    assume operation_uses_q:
      "node_uses_qubit (OperationNode stored_op) q"

    show
      "has_unique_wire_predecessor
         updated_circuit q node_id
       \<and>
       has_unique_wire_successor
         updated_circuit q node_id"
    proof (cases "node_id = new_node_id")
      case True

      have stored_op_is_new_op:
        "stored_op = new_op"
        using
          operation_lookup_after
          new_node_exists_after
          True
        by simp

      have unique_new_predecessor:
        "has_unique_wire_predecessor
           updated_circuit q new_node_id"
        unfolding has_unique_wire_predecessor_def
      proof (rule ex1I[of _ "frontier q"])
        show
          "(frontier q, new_node_id)
            \<in> wire_edge_relation updated_circuit q"
          using relation_after
          by simp

      next
        fix predecessor_id

        assume predecessor_edge:
          "(predecessor_id, new_node_id)
            \<in> wire_edge_relation updated_circuit q"

        from predecessor_edge relation_after show
          "predecessor_id = frontier q"
          using
            output_not_new
            no_old_edge_to_new_node
          by auto
      qed

      have unique_new_successor:
        "has_unique_wire_successor
           updated_circuit q new_node_id"
        unfolding has_unique_wire_successor_def
      proof (rule ex1I[of _ "get_output_node_id q"])
        show
          "(new_node_id, get_output_node_id q)
            \<in> wire_edge_relation updated_circuit q"
          using relation_after
          by simp

      next
        fix successor_id

        assume successor_edge:
          "(new_node_id, successor_id)
            \<in> wire_edge_relation updated_circuit q"

        from successor_edge relation_after show
          "successor_id = get_output_node_id q"
          using
            frontier_not_new
            no_old_edge_from_new_node
          by auto
      qed

      show ?thesis
        using
          True
          unique_new_predecessor
          unique_new_successor
        by simp

    next
      case False

      have operation_lookup_before:
        "nodes circuit node_id =
         Some (OperationNode stored_op)"
        using
          operation_lookup_after
          old_nodes_unchanged[OF False]
        by simp

      have old_degrees:
        "has_unique_wire_predecessor circuit q node_id
         \<and>
         has_unique_wire_successor circuit q node_id"
        using
          old_operation_degrees
          operation_lookup_before
          operation_uses_q
        by blast

      have node_not_output:
        "node_id \<noteq> get_output_node_id q"
      proof
        assume node_is_output:
          "node_id = get_output_node_id q"

        from old_degrees have
          "has_unique_wire_successor circuit q node_id"
          by simp

        then obtain successor_id where
          "(node_id, successor_id)
            \<in> wire_edge_relation circuit q"
          unfolding has_unique_wire_successor_def
          by blast

        with node_is_output old_output_has_no_successor
        show False
          by blast
      qed

      have predecessor_edges_unchanged:
        "\<And>predecessor_id.
           ((predecessor_id, node_id)
              \<in> wire_edge_relation updated_circuit q)
           \<longleftrightarrow>
           ((predecessor_id, node_id)
              \<in> wire_edge_relation circuit q)"
        using
          relation_after
          False
          node_not_output
        by auto

      have unique_predecessor_after:
        "has_unique_wire_predecessor
           updated_circuit q node_id"
        using
          old_degrees
          predecessor_edges_unchanged
        unfolding has_unique_wire_predecessor_def
        by blast

      have unique_successor_after:
        "has_unique_wire_successor
           updated_circuit q node_id"
      proof (cases "node_id = frontier q")
        case True

        have old_frontier_unique_successor:
          "has_unique_wire_successor
             circuit q (frontier q)"
          using old_degrees True
          by simp

        have old_frontier_successor_is_output:
          "\<And>successor_id.
             (frontier q, successor_id)
               \<in> wire_edge_relation circuit q
             \<Longrightarrow> successor_id = get_output_node_id q"
          using
            old_frontier_unique_successor
            old_frontier_output_edge
          unfolding has_unique_wire_successor_def
          by blast

        show ?thesis
          unfolding has_unique_wire_successor_def
        proof (rule ex1I[of _ new_node_id])
          show
            "(node_id, new_node_id)
              \<in> wire_edge_relation updated_circuit q"
            using relation_after True
            by simp

        next
          fix successor_id

          assume successor_edge:
            "(node_id, successor_id)
              \<in> wire_edge_relation updated_circuit q"

          from successor_edge relation_after True show
            "successor_id = new_node_id"
            using
              frontier_not_new
              no_old_edge_from_new_node
              old_frontier_successor_is_output
            by auto
        qed

      next
        case False

        have successor_edges_unchanged:
          "\<And>successor_id.
             ((node_id, successor_id)
                \<in> wire_edge_relation updated_circuit q)
             \<longleftrightarrow>
             ((node_id, successor_id)
                \<in> wire_edge_relation circuit q)"
          using
            relation_after
            False
            new_node_unused_before
            operation_lookup_before
          by auto

        show ?thesis
          using
            old_degrees
            successor_edges_unchanged
          unfolding has_unique_wire_successor_def
          by blast
      qed

      show ?thesis
        using
          unique_predecessor_after
          unique_successor_after
        by simp
    qed
  qed
qed

lemma insert_operation_preserves_wire_linearity:
  (* Inserting a valid operation at the current construction frontier
     preserves the linear-chain structure of every valid qubit wire.

     For each wire used by the new operation, the existing final edge

         frontier(q) \<rightarrow> output(q)

     is replaced by exactly two edges

         frontier(q) \<rightarrow> new_node
         new_node \<rightarrow> output(q).

     Therefore, the old frontier node still has one successor on q,
     the new operation node has one predecessor and one successor on q,
     and the output node still has one predecessor and no successor.

     Wires not used by the operation are unchanged.
  *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

assumes linear_before:
  "all_wires_linear circuit"

shows
  "all_wires_linear
           (fst (insert_operation circuit frontier op))"

  unfolding all_wires_linear_def

proof -
  let ?updated_circuit = "fst (insert_operation circuit frontier op)"
    (* The circuit returned after inserting the new operation. *)

  show "\<forall>q. qubit_in_circuit ?updated_circuit q
        \<longrightarrow> wire_is_linear ?updated_circuit q"

  proof (intro allI impI)
    fix q
      (* Choose an arbitrary wire q. We must prove that it remains linear
       whenever it is valid in the updated circuit. *)

    assume q_is_valid_after_insertion:
      "qubit_in_circuit ?updated_circuit q"

    have q_is_valid_before_insertion:
      "qubit_in_circuit circuit q"
      using
        qubit_in_circuit_def
        q_is_valid_after_insertion
      by simp

    have q_is_linear_before_insertion:
      "wire_is_linear circuit q"
      using linear_before q_is_valid_before_insertion
      unfolding all_wires_linear_def
      by simp

    show "wire_is_linear ?updated_circuit q"
    proof (cases "q \<in> set (op_qargs op)")
      case True

      have distinct_operation_wires:
        "distinct (op_qargs op)"
        using operation_valid
        unfolding 
          operation_in_circuit_def
          is_valid_operation_def
        by simp

      have q_wire_relation_after:
        "wire_edge_relation ?updated_circuit q
       =
       insert
         (next_id circuit, get_output_node_id q)
         (insert
           (frontier q, next_id circuit)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

      proof -
        let ?new_node_id = "next_id circuit"

        let ?circuit_with_node =
          "insert_node
           ?new_node_id
           (OperationNode op)
           circuit"

        let ?spliced_result =
          "splice_wires
           ?circuit_with_node
           frontier
           (op_qargs op)
           ?new_node_id"

        obtain spliced_circuit updated_frontier where
          spliced_result:
          "?spliced_result =
           (spliced_circuit, updated_frontier)"
          by (cases ?spliced_result)

        have relation_after_splicing:
          "wire_edge_relation spliced_circuit q
         =
         insert
           (?new_node_id, get_output_node_id q)
           (insert
             (frontier q, ?new_node_id)
             (wire_edge_relation ?circuit_with_node q -
                {(frontier q, get_output_node_id q)}))"
          using
            distinct_operation_wires
            True
            spliced_result
            splice_wires_updates_affected_wire_relation[
              of "op_qargs op" q
              ?circuit_with_node frontier ?new_node_id]
          by simp

        have node_insertion_preserves_relation:
          "wire_edge_relation ?circuit_with_node q =
         wire_edge_relation circuit q"
          unfolding
            wire_edge_relation_def
            insert_node_def
          by simp

        show ?thesis
          using
            spliced_result
            relation_after_splicing
            node_insertion_preserves_relation
          unfolding insert_operation_def Let_def
          by simp

      qed

      have valid_frontier_before:
        (* Extract the original frontier invariant from the valid
         construction-state assumption. *)
        "is_valid_frontier circuit frontier"
        using valid_state
        unfolding is_valid_construction_state_def
        by simp

      have new_node_unused_before:
        (* The node ID used for insertion was unused in the original
         circuit. *)
        "nodes circuit (next_id circuit) = None"
        using valid_state
        unfolding
          is_valid_construction_state_def
          next_id_is_unused_def
        by simp

      have output_node_exists_before:
        "nodes circuit (get_output_node_id q)
     = Some (OutputNode q)"
      proof -
        have "is_well_formed_circuit circuit"
          using
            is_valid_construction_state_def
            valid_state
          by simp
        then show ?thesis
          using
            are_well_formed_boundary_nodes_def
            get_qubit_index.elims
            insert_operation_num_qubits
            is_well_formed_circuit_def
            q_is_valid_after_insertion
            qubit_in_circuit_def
          by moura
      qed


      have new_node_not_output:
        "next_id circuit \<noteq> get_output_node_id q"
      proof
        assume same_id:
          "next_id circuit = get_output_node_id q"

        from new_node_unused_before have
          "nodes circuit (get_output_node_id q) = None"
          using same_id
          by simp

        with output_node_exists_before show False
          by simp
      qed

      have new_node_exists_after:
        (* The returned circuit stores the inserted operation node at the
         old next_id. *)
        "nodes ?updated_circuit (next_id circuit) =
       Some (OperationNode op)"
        using insert_operation_new_node
        by simp

      have new_node_uses_q:
        (* Since q occurs in the operation's qubit arguments, the inserted
         operation node uses q. *)
        "node_uses_qubit (OperationNode op) q"
        using True
        by simp

      have old_nodes_unchanged:
        (* Every node-table entry other than the newly allocated ID is
         unchanged by insert_operation. *)
        "node_id \<noteq> next_id circuit
       \<Longrightarrow> nodes ?updated_circuit node_id =
           nodes circuit node_id"
        for node_id
        using insert_operation_preserves_other_nodes
        by simp

      have comparable_after:
        "nodes_comparable_on_wire ?updated_circuit q"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          new_node_exists_after
          new_node_uses_q
          old_nodes_unchanged
          q_wire_relation_after
          subdividing_final_edge_preserves_wire_comparability
          wire_is_linear_def
          is_valid_construction_state_def valid_state
        by blast

      have input_node_exists_before:
        "nodes circuit (get_input_node_id q) =
   Some (InputNode q)"
        using
          valid_state
          q_is_valid_before_insertion
        unfolding
          is_valid_construction_state_def
          is_well_formed_circuit_def
          are_well_formed_boundary_nodes_def
          qubit_in_circuit_def
        by (metis get_qubit_index.elims)

      have new_node_not_input:
        "next_id circuit \<noteq> get_input_node_id q"
      proof
        assume same_id:
          "next_id circuit = get_input_node_id q"

        from new_node_unused_before same_id have
          "nodes circuit (get_input_node_id q) = None"
          by simp

        with input_node_exists_before show False
          by simp
      qed

      have input_boundary_after:
        "(\<nexists>predecessor_id.
          (predecessor_id, get_input_node_id q)
            \<in> wire_edge_relation ?updated_circuit q)
       \<and> has_unique_wire_successor
           ?updated_circuit q (get_input_node_id q)"

        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          q_wire_relation_after
          new_node_not_input
        using subdividing_final_edge_preserves_input_boundary
        by simp

      have output_predecessor_after:
        "has_unique_wire_predecessor
     ?updated_circuit q (get_output_node_id q)"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          q_wire_relation_after
          new_node_not_output
        by (simp add: subdividing_final_edge_preserves_output_predecessor)

      have output_no_successor_after:
        "\<nexists>successor_id.
     (get_output_node_id q, successor_id)
       \<in> wire_edge_relation ?updated_circuit q"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_not_output
          q_wire_relation_after
        by (rule subdividing_final_edge_preserves_output_no_successor)


      have operation_nodes_after:
        "\<forall>node_id stored_op.
         nodes ?updated_circuit node_id =
           Some (OperationNode stored_op)
         \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
         \<longrightarrow> has_unique_wire_predecessor
               ?updated_circuit q node_id
           \<and> has_unique_wire_successor
               ?updated_circuit q node_id"
        using
          q_is_linear_before_insertion
          valid_frontier_before
          q_is_valid_before_insertion
          new_node_unused_before
          new_node_exists_after
          new_node_uses_q
          old_nodes_unchanged
          q_wire_relation_after
          is_valid_construction_state_def
          subdividing_final_edge_preserves_operation_node_degrees
          valid_state
        by simp

      show ?thesis
        using
          comparable_after
          input_boundary_after
          output_predecessor_after
          output_no_successor_after
          operation_nodes_after
        unfolding wire_is_linear_def
        by simp

    next
      case False

      have q_wire_relation_unchanged:
        "wire_edge_relation ?updated_circuit q = wire_edge_relation circuit q"

      proof -
        let ?new_node_id = "next_id circuit"

        let ?circuit_with_node =
          "insert_node
           ?new_node_id
           (OperationNode op)
           circuit"

        let ?spliced_result =
          "splice_wires
           ?circuit_with_node
           frontier
           (op_qargs op)
           ?new_node_id"

        obtain spliced_circuit updated_frontier where
          spliced_result:
          "?spliced_result =
           (spliced_circuit, updated_frontier)"
          by (cases ?spliced_result)

        have relation_after_splicing:
          "wire_edge_relation spliced_circuit q =
         wire_edge_relation ?circuit_with_node q"
          using
            False
            spliced_result
            splice_wires_preserves_unaffected_wire_relation[
              of q "op_qargs op"
              ?circuit_with_node frontier ?new_node_id]
          by simp

        have inserting_node_preserves_relation:
          "wire_edge_relation ?circuit_with_node q =
         wire_edge_relation circuit q"
          unfolding
            wire_edge_relation_def
            insert_node_def
          by simp

        show ?thesis
          using
            spliced_result
            relation_after_splicing
            inserting_node_preserves_relation
          unfolding
            insert_operation_def
            Let_def
          by simp
      qed

      have old_node_lookup_unchanged:
        (* Inserting the operation changes the nodes field only at the old
         next_id. Every other node-table entry remains unchanged. *)
        "node_id \<noteq> next_id circuit
       \<Longrightarrow> nodes ?updated_circuit node_id =
           nodes circuit node_id"
        for node_id

        unfolding
          insert_operation_def
          Let_def
        by simp

      have q_wire_reaches_unchanged:
        (* Since the immediate q-labelled edge relation is unchanged,
           its transitive closure, and therefore reachability on q, is
           unchanged as well. *)
        "wire_reaches ?updated_circuit q node_a node_b
         \<longleftrightarrow> wire_reaches circuit q node_a node_b"

        unfolding wire_reaches_def
        using q_wire_relation_unchanged
        by simp

      have q_nodes_comparable_after:
        "nodes_comparable_on_wire ?updated_circuit q"
        unfolding nodes_comparable_on_wire_def
      proof (intro allI impI)
        fix node_a node_b node_a_value node_b_value

        assume node_a_lookup_after:
          "nodes ?updated_circuit node_a = Some node_a_value"

        assume node_b_lookup_after:
          "nodes ?updated_circuit node_b = Some node_b_value"

        assume node_a_uses_q:
          "node_uses_qubit node_a_value q"

        assume node_b_uses_q:
          "node_uses_qubit node_b_value q"

        have node_a_not_new:
          "node_a \<noteq> next_id circuit"
        proof
          assume node_a_is_new:
            "node_a = next_id circuit"

          have new_node_lookup:
            "nodes ?updated_circuit (next_id circuit) =
           Some (OperationNode op)"
            using insert_operation_new_node
            by simp

          from
            node_a_lookup_after
            new_node_lookup
            node_a_is_new
          have node_a_value_eq:
            "node_a_value = OperationNode op"
            by simp

          from node_a_uses_q node_a_value_eq have
            "q \<in> set (op_qargs op)"
            by simp

          with False show False
            by contradiction
        qed

        have node_b_not_new:
          "node_b \<noteq> next_id circuit"
        proof
          assume node_b_is_new:
            "node_b = next_id circuit"

          have new_node_lookup:
            "nodes ?updated_circuit (next_id circuit) =
           Some (OperationNode op)"
            using insert_operation_new_node
            by simp

          from node_b_lookup_after new_node_lookup node_b_is_new
          have node_b_value_eq:
            "node_b_value = OperationNode op"
            by simp

          from node_b_uses_q node_b_value_eq have
            "q \<in> set (op_qargs op)"
            by simp

          with False show False
            by contradiction
        qed

        have node_a_lookup_before:
          "nodes circuit node_a = Some node_a_value"
          using
            node_a_lookup_after
            old_node_lookup_unchanged[OF node_a_not_new]
          by simp

        have node_b_lookup_before:
          "nodes circuit node_b = Some node_b_value"
          using
            node_b_lookup_after
            old_node_lookup_unchanged[OF node_b_not_new]
          by simp

        from q_is_linear_before_insertion have comparable_before:
          "nodes_comparable_on_wire circuit q"
          unfolding wire_is_linear_def
          by simp

        from comparable_before
          node_a_lookup_before
          node_b_lookup_before
          node_a_uses_q
          node_b_uses_q
        have
          "node_a = node_b
         \<or> wire_reaches circuit q node_a node_b
         \<or> wire_reaches circuit q node_b node_a"
          unfolding nodes_comparable_on_wire_def
          by blast

        then show
          "node_a = node_b
         \<or> wire_reaches ?updated_circuit q node_a node_b
         \<or> wire_reaches ?updated_circuit q node_b node_a"
          using
            q_wire_reaches_unchanged
            q_wire_relation_unchanged
            wire_reaches_def
          by simp
      qed

      have operation_nodes_linear_after:
        "\<forall>node_id stored_op.
         nodes ?updated_circuit node_id =
           Some (OperationNode stored_op)
         \<longrightarrow> node_uses_qubit (OperationNode stored_op) q
         \<longrightarrow> has_unique_wire_predecessor
               ?updated_circuit q node_id
           \<and> has_unique_wire_successor
               ?updated_circuit q node_id"
      proof (intro allI impI)
        fix node_id stored_op

        assume operation_lookup_after:
          "nodes ?updated_circuit node_id =
         Some (OperationNode stored_op)"

        assume stored_op_uses_q:
          "node_uses_qubit (OperationNode stored_op) q"

        have node_id_not_new:
          "node_id \<noteq> next_id circuit"
        proof
          assume node_id_is_new:
            "node_id = next_id circuit"

          have new_node_lookup:
            "nodes ?updated_circuit (next_id circuit) = Some (OperationNode op)"
            using insert_operation_new_node
            by simp

          from operation_lookup_after
            new_node_lookup
            node_id_is_new
          have "stored_op = op"
            by simp

          with stored_op_uses_q have
            "q \<in> set (op_qargs op)"
            by simp

          with False show False
            by contradiction
        qed

        have operation_lookup_before:
          "nodes circuit node_id = Some (OperationNode stored_op)"
          using
            operation_lookup_after
            old_node_lookup_unchanged[OF node_id_not_new]
          by simp

        from q_is_linear_before_insertion
          operation_lookup_before
          stored_op_uses_q
        have old_degrees:
          "has_unique_wire_predecessor circuit q node_id
         \<and> has_unique_wire_successor circuit q node_id"
          unfolding wire_is_linear_def
          by blast

        show
          "has_unique_wire_predecessor
           ?updated_circuit q node_id
         \<and> has_unique_wire_successor
           ?updated_circuit q node_id"
          using old_degrees q_wire_relation_unchanged
          unfolding
            has_unique_wire_predecessor_def
            has_unique_wire_successor_def
          by simp
      qed

      show ?thesis
        using
          q_is_linear_before_insertion
          q_nodes_comparable_after
          operation_nodes_linear_after
          q_wire_relation_unchanged
        unfolding
          wire_is_linear_def
          has_unique_wire_predecessor_def
          has_unique_wire_successor_def
        by simp

    qed
  qed
qed

lemma insert_operation_preserves_acyclicity:
  (* Inserting a valid operation at the current construction frontier
     preserves global graph acyclicity.

     On every affected wire, insertion removes the final edge

         frontier(q) \<rightarrow> output(q)

     and replaces it with

         frontier(q) \<rightarrow> new_node
         new_node \<rightarrow> output(q).

     The new operation node was previously unused, so no path can
     already pass through it. The new node is inserted strictly after
     each affected frontier node and strictly before the corresponding
     output node. Therefore, the new edges cannot introduce a directed
     cycle.
  *)
  assumes valid_state:
    "is_valid_construction_state circuit frontier"
    and operation_valid:
    "operation_in_circuit circuit op"
    and acyclic:
    "is_acyclic_circuit circuit"
    and linear_before:
    "all_wires_linear circuit"
  shows
    "is_acyclic_circuit
       (fst (insert_operation circuit frontier op))"

proof -
  let ?new_node_id = "next_id circuit"

  let ?updated_circuit = "fst (insert_operation circuit frontier op)"

  let ?old_relation = "edge_relation circuit"

  let ?updated_relation = "edge_relation ?updated_circuit"

  have old_relation_acyclic:
    "acyclic ?old_relation" (* Previous edge relations are acyclic *)
    using acyclic
    unfolding is_acyclic_circuit_def
    by simp

  have circuit_well_formed:
    "is_well_formed_circuit circuit" (* Previous circuit is well-formed *)
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have new_node_unused:
    "nodes circuit ?new_node_id = None" (* New node was unused before insertion *)
    using valid_state
    unfolding
      is_valid_construction_state_def
      next_id_is_unused_def
    by simp

  have new_node_not_old_source:
    "\<And>target_id.
       (?new_node_id, target_id) \<notin> ?old_relation" (* New node did not occur in any old edge *)
  proof -
    fix target_id
    show
      "(?new_node_id, target_id) \<notin> ?old_relation"

    proof
      assume relation_edge:
        "(?new_node_id, target_id) \<in> ?old_relation"

      then obtain e where
        edge_in:
        "e \<in> edges circuit"
        and source_eq:
        "edge_source e = ?new_node_id"
        unfolding edge_relation_def
        by blast

      have edge_well_formed:
        "is_well_formed_edge circuit e"
        using circuit_well_formed edge_in
        unfolding
          is_well_formed_circuit_def
          are_well_formed_edges_def
        by simp

      have source_exists:
        "node_exists circuit ?new_node_id"
        using edge_well_formed source_eq
        unfolding is_well_formed_edge_def
        by simp

      then show False
        using new_node_unused
        unfolding node_exists_def
        by simp
    qed
  qed

  have new_node_not_old_target:
    "\<And>source_id.
       (source_id, ?new_node_id) \<notin> ?old_relation"
  proof -
    fix source_id

    show
      "(source_id, ?new_node_id) \<notin> ?old_relation"
    proof
      assume relation_edge:
        "(source_id, ?new_node_id) \<in> ?old_relation"

      then obtain e where
        edge_in:
        "e \<in> edges circuit"
        and target_eq:
        "edge_target e = ?new_node_id"
        unfolding edge_relation_def
        by auto

      have edge_well_formed:
        "is_well_formed_edge circuit e"
        using circuit_well_formed edge_in
        unfolding is_well_formed_circuit_def
          are_well_formed_edges_def
        by blast

      have target_exists:
        "node_exists circuit ?new_node_id"
        using edge_well_formed target_eq
        unfolding is_well_formed_edge_def
        by simp

      then show False
        using new_node_unused
        unfolding node_exists_def
        by simp
    qed
  qed

(* ---------- Establish well-formedness and linearity after insertion proofs begin --------- *)

  have updated_state_valid:
    "is_valid_construction_state
       ?updated_circuit
       (snd (insert_operation circuit frontier op))"
    using valid_state operation_valid
    by (simp add: insert_operation_preserves_valid_construction_state)

  have updated_well_formed:
    "is_well_formed_circuit ?updated_circuit"
    using updated_state_valid
    unfolding is_valid_construction_state_def
    by simp

  have updated_linear:
    "all_wires_linear ?updated_circuit"
    using valid_state operation_valid linear_before
    by (simp add: insert_operation_preserves_wire_linearity)

(* ---------- Establish well-formedness and linearity after insertion proofs end --------- *)

  have updated_output_is_sink:
    "\<And>q target_id.
       qubit_in_circuit ?updated_circuit q
       \<Longrightarrow>
       (get_output_node_id q, target_id)
         \<notin> ?updated_relation"
  proof -
    fix q target_id

    assume valid_q:
      "qubit_in_circuit ?updated_circuit q"

    show
      "(get_output_node_id q, target_id)
         \<notin> ?updated_relation"
    proof
      assume relation_edge:
        "(get_output_node_id q, target_id)
           \<in> ?updated_relation"

      then obtain e where
        edge_in:
        "e \<in> edges ?updated_circuit"
        and source_eq:
        "edge_source e = get_output_node_id q"
        and  target_eq:
        "edge_target e = target_id"
        unfolding edge_relation_def
        by auto

      have edge_well_formed:
        "is_well_formed_edge ?updated_circuit e"
        using
          updated_well_formed
          edge_in
        unfolding
          is_well_formed_circuit_def
          are_well_formed_edges_def
        by simp

      have output_node_value:
        "nodes ?updated_circuit (get_output_node_id q)
           = Some (OutputNode q)"
        using updated_well_formed valid_q
        unfolding is_well_formed_circuit_def
          are_well_formed_boundary_nodes_def
          qubit_in_circuit_def
        by (cases q; simp)

      have edge_wire_is_q:
        "edge_wire e = q"
        using edge_well_formed source_eq output_node_value
        unfolding is_well_formed_edge_def
        by (cases "nodes ?updated_circuit (edge_source e)") auto

      have wire_linear_q:
        "wire_is_linear ?updated_circuit q"
        using updated_linear valid_q
        unfolding all_wires_linear_def
        by simp

      have no_output_successor:
        "\<nexists>successor_id.
           (get_output_node_id q, successor_id)
             \<in> wire_edge_relation ?updated_circuit q"
        using wire_linear_q
        unfolding wire_is_linear_def
        by simp

      have output_wire_edge:
        "(get_output_node_id q, target_id)
          \<in> wire_edge_relation ?updated_circuit q"
      proof -
        have edge_eq:
          "e =
             make_edge
               (get_output_node_id q)
               target_id
               q"
          using source_eq edge_wire_is_q target_eq
          by (cases e) (simp add: make_edge_def)

        show ?thesis
          unfolding wire_edge_relation_def
          using edge_in edge_eq
          by simp
      qed

      then show False
        using no_output_successor
        by simp
    qed
  qed

  have updated_cycle_implies_old_cycle:
    "\<And>node_id.
       (node_id, node_id) \<in> ?updated_relation\<^sup>+
       \<Longrightarrow>
       (node_id, node_id) \<in> ?old_relation\<^sup>+"

  proof -
    fix node_id
    assume updated_cycle:
      "(node_id, node_id) \<in> ?updated_relation\<^sup>+"

    have updated_edge_is_old_or_new:
      "\<And>u v.
         (u,v) \<in> ?updated_relation
        \<Longrightarrow>
         (u,v) \<in> ?old_relation
         \<or> u = ?new_node_id
         \<or> v = ?new_node_id"
    proof -
      fix u v
      assume updated_edge:
        "(u,v) \<in> ?updated_relation" 
      obtain e where
        edge_in:
        "e \<in> edges ?updated_circuit"
        and source:
        "edge_source e = u"
        and target:
        "edge_target e = v"

        using updated_edge
        unfolding edge_relation_def
        by auto

      have splice_wires_edge_cases:
        "\<And>base_circuit base_frontier qs e.
           e \<in> edges
             (fst
               (splice_wires
                 base_circuit
                 base_frontier
                 qs
                 ?new_node_id))
          \<Longrightarrow>
           e \<in> edges base_circuit
           \<or> edge_source e = ?new_node_id
           \<or> edge_target e = ?new_node_id"
      proof -
        fix base_circuit base_frontier qs e

        show
          "e \<in> edges
       (fst
         (splice_wires
           base_circuit
           base_frontier
           qs
           ?new_node_id))
     \<Longrightarrow>
       e \<in> edges base_circuit
       \<or> edge_source e = ?new_node_id
       \<or> edge_target e = ?new_node_id"
        proof (induction qs arbitrary: base_circuit base_frontier)
          case Nil

          then show ?case
            by simp

        next
          case (Cons q qs)

          obtain first_circuit first_frontier where first_splice:
            "splice_wire
               base_circuit
               base_frontier
               q
               ?new_node_id
             =
             (first_circuit, first_frontier)"
            by (cases
                "splice_wire
                   base_circuit
                   base_frontier
                   q
                   ?new_node_id")

          have after_remaining:
            "e \<in> edges first_circuit
           \<or> edge_source e = ?new_node_id
           \<or> edge_target e = ?new_node_id"
            using Cons.prems
              Cons.IH[of first_circuit first_frontier]
              first_splice
            by simp

          then show ?case
            using first_splice
            unfolding
              splice_wire_def
              splice_wire_without_updating_frontier_def
              insert_edge_def
              delete_edge_def
              make_edge_def
              Let_def
            by auto
        qed
      qed

      have edge_cases:
        "e \<in> edges circuit
       \<or> edge_source e = ?new_node_id
       \<or> edge_target e = ?new_node_id"
      proof -
        have spliced_edge_cases:
          "e \<in> edges (insert_node ?new_node_id (OperationNode op) circuit)
         \<or> edge_source e = ?new_node_id
         \<or> edge_target e = ?new_node_id"
          using
            edge_in
            splice_wires_edge_cases[
              where
                base_circuit =
                "insert_node
               ?new_node_id
               (OperationNode op)
               circuit"
                and base_frontier = frontier
                and qs = "op_qargs op"
                and e = e
                ]
          unfolding
            insert_operation_def
            Let_def
          by simp

        then show ?thesis
          unfolding insert_node_def
          by simp
      qed

      from edge_cases
      consider
        (old) "e \<in> edges circuit"
        | (src) "edge_source e = ?new_node_id"
        | (tgt) "edge_target e = ?new_node_id"
        by auto

      show
        "(u,v) \<in> ?old_relation
         \<or> u = ?new_node_id
         \<or> v = ?new_node_id"

        using edge_cases source target
        unfolding edge_relation_def
        by auto
    qed

    have updated_path_old_or_through_new:
      "\<And>u v.
     (u, v) \<in> ?updated_relation\<^sup>+
     \<Longrightarrow>
       (u, v) \<in> ?old_relation\<^sup>+
       \<or>
       ((u, ?new_node_id) \<in> ?updated_relation\<^sup>*
        \<and>
        (?new_node_id, v) \<in> ?updated_relation\<^sup>*)"
    proof -
      fix u v

      assume updated_path:
        "(u, v) \<in> ?updated_relation\<^sup>+"

      show
        "(u, v) \<in> ?old_relation\<^sup>+
     \<or>
     ((u, ?new_node_id) \<in> ?updated_relation\<^sup>*
      \<and>
      (?new_node_id, v) \<in> ?updated_relation\<^sup>*)"
        using updated_path
      proof (induction rule: trancl_induct)
        case (base v)

        have edge_cases:
          "(u, v) \<in> ?old_relation
       \<or> u = ?new_node_id
       \<or> v = ?new_node_id"
          using updated_edge_is_old_or_new[OF base]
          .

        then show ?case
        proof
          assume old_edge:
            "(u, v) \<in> ?old_relation"

          then have
            "(u, v) \<in> ?old_relation\<^sup>+"
            by (rule r_into_trancl)

          then show ?case
            by simp

        next
          assume new_endpoint:
            "u = ?new_node_id \<or> v = ?new_node_id"

          then show ?case
          proof
            assume source_new:
              "u = ?new_node_id"

            have start_refl:
              "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
              using source_new
              by simp

            have remaining_edge:
              "(?new_node_id, v) \<in> ?updated_relation\<^sup>*"
              using base source_new
              by auto

            show ?case
              using start_refl remaining_edge
              by blast

          next
            assume target_new:
              "v = ?new_node_id"

            have first_edge:
              "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
              using base target_new
              by auto

            have end_refl:
              "(?new_node_id, v) \<in> ?updated_relation\<^sup>*"
              using target_new
              by simp

            show ?case
              using first_edge end_refl
              by simp
          qed
        qed

      next
        case (step v w)

        have final_edge_cases:
          "(v, w) \<in> ?old_relation
         \<or> v = ?new_node_id
         \<or> w = ?new_node_id"
          using updated_edge_is_old_or_new[OF step.hyps(2)]
          .

        have induction_hypothesis:
          "(u, v) \<in> ?old_relation\<^sup>+
       \<or>
       ((u, ?new_node_id) \<in> ?updated_relation\<^sup>* \<and> (?new_node_id, v) \<in> ?updated_relation\<^sup>*)"
          by (simp add: step.IH)

        from induction_hypothesis
        show ?case
        proof
          assume old_path:
            "(u, v) \<in> ?old_relation\<^sup>+"

          from final_edge_cases
          show ?thesis
          proof
            assume old_edge:
              "(v, w) \<in> ?old_relation"

            have old_extended:
              "(u, w) \<in> ?old_relation\<^sup>+"
              using old_path old_edge
              by (rule trancl_into_trancl)

            then show ?thesis
              by blast

          next
            assume new_endpoint:
              "v = ?new_node_id \<or> w = ?new_node_id"

            then show ?thesis
            proof
              assume source_is_new:
                "v = ?new_node_id"

              have path_to_new:
                "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
                using step.hyps(1) source_is_new
                by (simp add: trancl_into_rtrancl)

              have path_from_new:
                "(?new_node_id, w) \<in> ?updated_relation\<^sup>*"
                using step.hyps(2) source_is_new
                by auto

              show ?thesis
                using path_to_new path_from_new
                by blast

            next
              assume target_is_new:
                "w = ?new_node_id"

              have updated_extended:
                "(u, w) \<in> ?updated_relation\<^sup>+"
                using step.hyps(1) step.hyps(2)
                by (rule trancl_into_trancl)

              have path_to_new:
                "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
                using updated_extended target_is_new
                by (simp add: trancl_into_rtrancl)

              have path_from_new:
                "(?new_node_id, w) \<in> ?updated_relation\<^sup>*"
                using target_is_new
                by simp

              show ?thesis
                using path_to_new path_from_new
                by blast
            qed
          qed

        next
          assume through_new:
            "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*
          \<and>
         (?new_node_id, v) \<in> ?updated_relation\<^sup>*"


          have path_to_new:
            "(u, ?new_node_id) \<in> ?updated_relation\<^sup>*"
            using through_new
            by blast

          have path_from_new:
            "(?new_node_id, v) \<in> ?updated_relation\<^sup>*"
            using through_new
            by blast

          have extended_from_new:
            "(?new_node_id, w) \<in> ?updated_relation\<^sup>*"
            using path_from_new step.hyps(2)
            by (rule rtrancl_into_rtrancl)

          show ?thesis
            using path_to_new extended_from_new
            by blast

        qed
      qed
    qed


    have updated_cycle_old_or_contains_new:
      "\<And>x.
         (x, x) \<in> ?updated_relation\<^sup>+
         \<Longrightarrow>
         (x, x) \<in> ?old_relation\<^sup>+
       \<or> (?new_node_id, ?new_node_id) \<in> ?updated_relation\<^sup>+"
      by (metis
          rtrancl_eq_or_trancl
          trancl_rtrancl_trancl
          updated_path_old_or_through_new)


    have splice_wires_new_source_cases:
      "\<And>base_circuit base_frontier qs e.
     distinct qs
     \<Longrightarrow>
     (\<forall>q \<in> set qs.
        base_frontier q \<noteq> ?new_node_id)
     \<Longrightarrow>
     e \<in> edges
       (fst
         (splice_wires
           base_circuit
           base_frontier
           qs
           ?new_node_id))
     \<Longrightarrow>
     edge_source e = ?new_node_id
     \<Longrightarrow>
       (e \<in> edges base_circuit
        \<and> edge_source e = ?new_node_id)
       \<or>
       (\<exists>q \<in> set qs.
          e =
            make_edge
              ?new_node_id
              (get_output_node_id q)
              q)"
    proof -
      fix base_circuit :: quantum_circuit
        and base_frontier :: "qubit \<Rightarrow> node_id"
        and qs :: "qubit list"
        and e :: edge

      assume distinct_qs:
        "distinct qs"

      assume frontier_not_new:
        "\<forall>q \<in> set qs.
         base_frontier q \<noteq> ?new_node_id"

      assume edge_in:
        "e \<in> edges
       (fst
         (splice_wires
           base_circuit
           base_frontier
           qs
           ?new_node_id))"

      assume source_is_new:
        "edge_source e = ?new_node_id"

      show
        "(e \<in> edges base_circuit
      \<and> edge_source e = ?new_node_id)
     \<or>
     (\<exists>q \<in> set qs.
        e =
          make_edge
            ?new_node_id
            (get_output_node_id q)
            q)"
        using edge_in source_is_new distinct_qs frontier_not_new
      proof (induction qs arbitrary: base_circuit base_frontier)
        case Nil

        then show ?case
          by simp

      next
        case (Cons q qs)

        have q_not_in_remaining:
          "q \<notin> set qs"

          using Cons.prems(3)
          by simp

        have current_frontier_not_new:
          "base_frontier q \<noteq> ?new_node_id"
          using Cons.prems(4)
          by simp

        obtain first_circuit first_frontier where first_splice:
          "splice_wire
         base_circuit
         base_frontier
         q
         ?new_node_id
       =
       (first_circuit, first_frontier)"
          by (cases
              "splice_wire
             base_circuit
             base_frontier
             q
             ?new_node_id")

        have remaining_edge:
          "e \<in> edges
     (fst
       (splice_wires
         first_circuit
         first_frontier
         qs
         ?new_node_id))"
          using Cons.prems(1) first_splice
          by simp

        have remaining_source:
          "edge_source e = ?new_node_id"
          using Cons.prems(2)
          .

        have remaining_distinct:
          "distinct qs"
          using Cons.prems(3)
          by simp

        have remaining_frontier_not_new:
          "\<forall>r \<in> set qs.
     first_frontier r \<noteq> ?new_node_id"
          by (metis
              Cons.prems(4)
              first_splice list.set_intros(2)
              q_not_in_remaining
              snd_eqD
              splice_wire_def
              update_frontier_other)

        have after_remaining:
          "(e \<in> edges first_circuit
        \<and> edge_source e = ?new_node_id)
       \<or>
       (\<exists>r \<in> set qs.
          e =
            make_edge
              ?new_node_id
              (get_output_node_id r)
              r)"
          using
            Cons.IH[
              OF
              remaining_edge
              remaining_source
              remaining_distinct
              remaining_frontier_not_new] .

        then show ?case
          using 
            first_splice
            Cons.prems(4)
            edges_splice_wire_without_updating_frontier
          unfolding
            splice_wire_def
            splice_wire_without_updating_frontier_def
            insert_edge_def
            delete_edge_def
            make_edge_def
            Let_def
          by auto
      qed
    qed
    have new_node_successor_is_output:
      "\<And>target_id.
     (?new_node_id, target_id) \<in> ?updated_relation
     \<Longrightarrow>
     \<exists>q.
       qubit_in_circuit ?updated_circuit q
       \<and> target_id = get_output_node_id q"
    proof -
      fix target_id

      assume relation_edge:
        "(?new_node_id, target_id) \<in> ?updated_relation"

      obtain e where
        edge_in:
        "e \<in> edges ?updated_circuit"
        and source_eq:
        "edge_source e = ?new_node_id"
        and target_eq:
        "edge_target e = target_id"
        using relation_edge
        unfolding edge_relation_def
        by auto

      have distinct_qargs:
        "distinct (op_qargs op)"
        using operation_valid
        unfolding operation_in_circuit_def
        by (simp add: is_valid_operation_def)

      have frontier_not_new_on_qargs:
        "\<forall>q \<in> set (op_qargs op).
     frontier q \<noteq> ?new_node_id"
      proof (intro ballI)
        fix q
        assume q_in_args:
          "q \<in> set (op_qargs op)"

        have valid_q:
          "qubit_in_circuit circuit q"
          using operation_valid q_in_args
          unfolding operation_in_circuit_def
          by simp

        have frontier_exists:
          "node_exists circuit (frontier q)"

          using
            valid_state
            valid_q
            is_valid_frontier_def
            node_exists_def
            is_valid_construction_state_def

          by auto

        show "frontier q \<noteq> ?new_node_id"
        proof
          assume frontier_eq:
            "frontier q = ?new_node_id"

          have new_node_exists:
            "node_exists circuit ?new_node_id"
            using frontier_exists frontier_eq
            by simp

          show False
            using new_node_exists new_node_unused
            unfolding node_exists_def
            by simp
        qed
      qed

      have outgoing_cases:
        "(e \<in>
        edges
          (insert_node
            ?new_node_id
            (OperationNode op)
            circuit)
      \<and> edge_source e = ?new_node_id)
     \<or>
     (\<exists>q \<in> set (op_qargs op).
        e =
          make_edge
            ?new_node_id
            (get_output_node_id q)
            q)"
        using
          edge_in
          source_eq
          splice_wires_new_source_cases[
            where
              base_circuit =
              "insert_node
               ?new_node_id
               (OperationNode op)
               circuit"
              and base_frontier = frontier
              and qs = "op_qargs op"
              and e = e]
        unfolding insert_operation_def Let_def
        by (simp add:
            distinct_qargs
            frontier_not_new_on_qargs)


      have inserted_case_impossible:
        "\<not>
      (e \<in>
         edges
           (insert_node
             ?new_node_id
             (OperationNode op)
             circuit)
       \<and> edge_source e = ?new_node_id)"
      proof
        assume inserted_old:
          "e \<in>
         edges
           (insert_node
             ?new_node_id
             (OperationNode op)
             circuit)
       \<and> edge_source e = ?new_node_id"

        then have old_edge:
          "e \<in> edges circuit"
          unfolding insert_node_def
          by simp

        have old_relation_edge:
          "(?new_node_id, edge_target e) \<in> ?old_relation"
          using old_edge source_eq
          unfolding edge_relation_def
          by blast

        show False
          using
            new_node_not_old_source[of "edge_target e"]
            old_relation_edge
          by contradiction
      qed

      then obtain q where
        q_in_args:
        "q \<in> set (op_qargs op)"
        and edge_eq:
        "e =
        make_edge
          ?new_node_id
          (get_output_node_id q)
          q"
        using outgoing_cases
        by blast

      have valid_q_old:
        "qubit_in_circuit circuit q"
        using operation_valid q_in_args
        unfolding operation_in_circuit_def
        by blast

      have valid_q_updated:
        "qubit_in_circuit ?updated_circuit q"
        using
          qubit_in_circuit_def
          valid_q_old
        by auto

      have target_is_output:
        "target_id = get_output_node_id q"
        using target_eq edge_eq
        unfolding make_edge_def
        by simp

      show
        "\<exists>q.
       qubit_in_circuit ?updated_circuit q
       \<and> target_id = get_output_node_id q"
        using valid_q_updated target_is_output
        by blast
    qed

    have new_node_not_on_updated_cycle:
      "(?new_node_id, ?new_node_id) \<notin> ?updated_relation\<^sup>+"
      by (metis
          new_node_successor_is_output
          rtrancl_trancl_trancl
          tranclD updated_output_is_sink)

    show "(node_id, node_id) \<in> ?old_relation\<^sup>+"
      using
        updated_cycle
        updated_cycle_old_or_contains_new
        new_node_not_on_updated_cycle
      by simp
  qed

  have updated_relation_acyclic:
    "acyclic ?updated_relation"

  proof -
    show ?thesis
      unfolding acyclic_def
    proof
      fix node_id

      show
        "(node_id, node_id) \<notin> ?updated_relation\<^sup>+"
      proof
        assume updated_cycle:
          "(node_id, node_id) \<in> ?updated_relation\<^sup>+"

        have old_cycle:
          "(node_id, node_id) \<in> ?old_relation\<^sup>+"
          using updated_cycle_implies_old_cycle[OF updated_cycle]
          by simp

        have no_old_cycle:
          "(node_id, node_id) \<notin> ?old_relation\<^sup>+"
          using old_relation_acyclic
          unfolding acyclic_def
          by simp

        show False
          using old_cycle no_old_cycle
          by simp
      qed
    qed
  qed

  show ?thesis
    using updated_relation_acyclic
    unfolding is_acyclic_circuit_def
    by simp
qed

lemma insert_operation_preserves_valid_quantum_circuit:
  (* Inserting a valid operation into a valid construction state
     preserves the complete structural validity of the quantum circuit.

     Before insertion:

       1. the circuit is well formed;
       2. the graph is acyclic;
       3. all nodes on each valid wire are comparable; and
       4. every valid wire satisfies the stronger linear-chain
          invariant required by the insertion proofs.

     The previously proved insertion theorems establish that the updated
     circuit remains well formed, acyclic, and wire-linear. Since wire
     linearity implies wire-node comparability, the updated circuit
     satisfies every component of is_valid_circuit.
  *)
  assumes valid_circuit:
    "is_valid_circuit circuit"

assumes valid_state:
  "is_valid_construction_state circuit frontier"

assumes operation_valid:
  "operation_in_circuit circuit op"

shows
  "is_valid_circuit
       (fst (insert_operation circuit frontier op))"
  using
    insert_operation_preserves_acyclicity
    insert_operation_preserves_well_formed_circuit
    insert_operation_preserves_wire_linearity
    is_valid_construction_state_def
    is_valid_circuit_def
    operation_valid valid_circuit
    valid_state
  by simp

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

end
