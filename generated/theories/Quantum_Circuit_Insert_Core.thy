theory Quantum_Circuit_Insert_Core
  imports Quantum_Circuit_Wire_Splice

begin

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

lemma splice_wires_preserves_unaffected_wire_relation:
  (* Recursively splicing a node into the wires listed in qs does not
     change the edge relation of a wire q that does not occur in qs.

     Each individual splice deletes and inserts only edges whose wire
     label is the wire currently being processed. Therefore, no edge
     labelled q is changed when q is absent from qs.
  *)
  assumes unaffected_wire:
    "q \<notin> set qs"

shows
  "wire_edge_relation
       (fst (splice_wires circuit frontier qs new_node_id))
       q
     =
     wire_edge_relation circuit q"

  using unaffected_wire

proof (induction qs arbitrary: circuit frontier)
  case Nil
  then show ?case
    by simp

next
  case (Cons current_wire remaining_wires)

  have different_wire:
    "q \<noteq> current_wire"
    using Cons.prems
    by simp


  have unaffected_remaining:
    "q \<notin> set remaining_wires"
    using Cons.prems
    by simp

  obtain updated_circuit updated_frontier where
    first_splice:
    "splice_wire
         circuit
         frontier
         current_wire
         new_node_id
       =
       (updated_circuit, updated_frontier)"
    by (cases
        "splice_wire
             circuit
             frontier
             current_wire
             new_node_id")

  have first_splice_preserves_q:
    "wire_edge_relation updated_circuit q = wire_edge_relation circuit q"
    using
      first_splice
      different_wire
      splice_wire_preserves_other_wire_relation[
        of q current_wire circuit frontier new_node_id]
    by simp

  have remaining_splices_preserve_q:
    "wire_edge_relation
       (fst
         (splice_wires
           updated_circuit
           updated_frontier
           remaining_wires
           new_node_id))
       q
     =
     wire_edge_relation updated_circuit q"
    by (simp add: Cons.IH unaffected_remaining)

  show ?case
    using
      first_splice
      first_splice_preserves_q
      remaining_splices_preserve_q
    by simp
qed

lemma splice_wires_updates_affected_wire_relation:
  (* When q occurs exactly once in the list qs, splice_wires replaces
     the current frontier-to-output edge on q by two edges passing
     through new_node_id.

     Splices performed on the other wires in qs do not affect the
     q-labelled edge relation.
  *)
  assumes distinct_wires:
    "distinct qs"

assumes affected_wire:
  "q \<in> set qs"

shows
  "wire_edge_relation
         (fst (splice_wires circuit frontier qs new_node_id))
         q
       =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
          (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"

  using distinct_wires affected_wire
proof (induction qs arbitrary: circuit frontier)
  case Nil

  then show ?case
    by simp

next
  case (Cons current_wire remaining_wires)

  obtain updated_circuit updated_frontier where
    first_splice:
    "splice_wire
         circuit
         frontier
         current_wire
         new_node_id
       =
       (updated_circuit, updated_frontier)"
    by (cases
        "splice_wire
             circuit
             frontier
             current_wire
             new_node_id")

  show ?case
  proof (cases "current_wire = q")
    case True

    have q_not_in_remaining:
      "q \<notin> set remaining_wires"
      using Cons.prems True
      by simp

    have first_splice_updates_q:
      "wire_edge_relation updated_circuit q
       =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (frontier q, new_node_id)
           (wire_edge_relation circuit q -
              {(frontier q, get_output_node_id q)}))"
      using first_splice True
      unfolding
        splice_wire_def
        splice_wire_without_updating_frontier_def
        wire_edge_relation_def
        insert_edge_def
        delete_edge_def
        make_edge_def
        Let_def
      by auto

    have remaining_splices_preserve_q:
      "wire_edge_relation
         (fst
           (splice_wires
             updated_circuit
             updated_frontier
             remaining_wires
             new_node_id))
         q
       =
       wire_edge_relation updated_circuit q"
      using
        splice_wires_preserves_unaffected_wire_relation[
          OF q_not_in_remaining,
          of updated_circuit updated_frontier new_node_id]
      .

    show ?thesis
      using
        first_splice
        first_splice_updates_q
        remaining_splices_preserve_q
        True
      by simp

  next
    case False

    have remaining_distinct:
      "distinct remaining_wires"
      using Cons.prems
      by simp

    have q_in_remaining:
      "q \<in> set remaining_wires"
      using Cons.prems False
      by simp

    have first_splice_preserves_q:
      "wire_edge_relation updated_circuit q =
       wire_edge_relation circuit q"
      using
        first_splice
        False
        splice_wire_preserves_other_wire_relation[
          of q current_wire circuit frontier new_node_id]
      by simp

    have updated_frontier_preserves_q:
      "updated_frontier q = frontier q"
      using first_splice False
      unfolding
        splice_wire_def
        update_frontier_def
      by auto

    have remaining_splices_update_q:
      "wire_edge_relation
         (fst
           (splice_wires
             updated_circuit
             updated_frontier
             remaining_wires
             new_node_id))
         q
       =
       insert
         (new_node_id, get_output_node_id q)
         (insert
           (updated_frontier q, new_node_id)
           (wire_edge_relation updated_circuit q -
              {(updated_frontier q, get_output_node_id q)}))"
      using
        Cons.IH[
          of updated_circuit updated_frontier
          ]
        remaining_distinct
        q_in_remaining
      by simp

    show ?thesis
      using
        first_splice
        remaining_splices_update_q
        first_splice_preserves_q
        updated_frontier_preserves_q
      by simp
  qed
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

assumes distinct_wires:
  (* Each wire is spliced at most once. *)
  "distinct qs"

assumes new_node_not_frontiers:
  (* The inserted node is different from the existing frontier node on
         every wire that will be spliced. *)
  "\<forall>q \<in> set qs. new_node_id \<noteq> frontier q"

assumes new_node_has_no_other_successors:
  (* Before splicing starts, the inserted node has no conflicting
         successor on any affected wire. *)
  "\<forall>q \<in> set qs.
         (\<forall>successor_id.
            (new_node_id, successor_id)
              \<in> wire_edge_relation circuit q
            \<longrightarrow> successor_id = get_output_node_id q)"

shows
  "is_valid_frontier \<comment>\<open>The final frontier correctly describes the final circuit\<close>
         (fst (splice_wires circuit frontier qs new_node_id))
         (snd (splice_wires circuit frontier qs new_node_id))"

  using
    valid_frontier
    new_node_exists
    new_node_uses_all_wires
    distinct_wires
    new_node_not_frontiers
    new_node_has_no_other_successors \<comment>\<open>Passes assumptions to the induction proof\<close>

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

  have new_node_not_first_frontier:
    "new_node_id \<noteq> frontier q"
    using Cons.prems(5)
    by simp

  have new_node_has_no_other_successor_on_first_wire:
    "\<And>successor_id.
       (new_node_id, successor_id)
         \<in> wire_edge_relation circuit q
       \<Longrightarrow> successor_id = get_output_node_id q"
    using Cons.prems(6)
    by simp

  have first_splice_preserves_frontier:
    (* Splicing the first wire produces a circuit and frontier that still satisfy the valid-frontier invariant. *)
    "is_valid_frontier updated_circuit updated_frontier"

  proof -
    have
      "is_valid_frontier
         (fst (splice_wire circuit frontier q new_node_id))
         (snd (splice_wire circuit frontier q new_node_id))"
      using
        splice_wire_preserves_valid_frontier[
          OF
          Cons.prems(1)
          Cons.prems(2)
          new_node_uses_first_wire
          new_node_not_first_frontier
          new_node_has_no_other_successor_on_first_wire
          ]
      .

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

  have remaining_wires_distinct:
    (* Since q # qs is distinct, the tail qs is also distinct. *)
    "distinct qs"
    using Cons.prems(4)
    by simp

  have new_node_not_remaining_frontiers:
    (* The first splice updates only the frontier entry for q.

       Every wire in qs is different from q because the original wire
       list is distinct. Therefore, the frontier entries for all
       remaining wires are unchanged, and the inserted node is still
       different from those frontier nodes.
    *)
    "\<forall>wire \<in> set qs.
       new_node_id \<noteq> updated_frontier wire"
  proof (intro ballI)
    fix wire

    assume wire_in_remaining:
      "wire \<in> set qs"

    have wire_not_first:
      "wire \<noteq> q"
      using Cons.prems(4) wire_in_remaining
      by auto

    have remaining_frontier_unchanged:
      "updated_frontier wire = frontier wire"
      using splice_result wire_not_first
      by (simp add: splice_wire_def split_pairs)

    have new_node_not_remaining_frontiers:
      (* The first splice updates only the frontier entry for q.

       Every wire in qs is different from q because the original wire
       list is distinct. Therefore, the frontier entries for all
       remaining wires are unchanged, and the inserted node is still
       different from those frontier nodes.
    *)
      "\<forall>wire \<in> set qs.
       new_node_id \<noteq> updated_frontier wire"
    proof (intro ballI)
      fix wire

      assume wire_in_remaining:
        "wire \<in> set qs"

      have wire_not_first:
        "wire \<noteq> q"
        using Cons.prems(4) wire_in_remaining
        by auto

      have remaining_frontier_unchanged:
        "updated_frontier wire = frontier wire"
        using splice_result wire_not_first
        by (simp add: splice_wire_def split_pairs)

      have new_node_not_old_frontier:
        "new_node_id \<noteq> frontier wire"
        using Cons.prems(5) wire_in_remaining
        by simp

      show
        "new_node_id \<noteq> updated_frontier wire"
        using
          remaining_frontier_unchanged
          new_node_not_old_frontier
        by simp
    qed

    have new_node_not_old_frontier:
      "new_node_id \<noteq> frontier wire"
      using Cons.prems(5) wire_in_remaining
      by simp

    show
      "new_node_id \<noteq> updated_frontier wire"
      using
        remaining_frontier_unchanged
        new_node_not_old_frontier
      by simp
  qed

  have new_node_has_no_other_successors_remaining:
    (* The first splice changes only the q-labelled wire relation.

       Since every remaining wire differs from q, its wire relation is
       unchanged. Therefore, the original no-conflicting-successor
       property transfers to updated_circuit for every remaining wire.
    *)
    "\<forall>wire \<in> set qs.
       (\<forall>successor_id.
          (new_node_id, successor_id)
            \<in> wire_edge_relation updated_circuit wire
          \<longrightarrow> successor_id = get_output_node_id wire)"
  proof (intro ballI allI impI)
    fix wire successor_id

    assume wire_in_remaining:
      "wire \<in> set qs"

    assume successor_edge_after:
      "(new_node_id, successor_id)
         \<in> wire_edge_relation updated_circuit wire"

    have wire_not_first:
      "wire \<noteq> q"
      using Cons.prems(4) wire_in_remaining
      by auto

    have remaining_wire_relation_unchanged:
      "wire_edge_relation updated_circuit wire =
       wire_edge_relation circuit wire"
      using
        splice_result
        wire_not_first
        splice_wire_preserves_other_wire_relation[
          of wire q circuit frontier new_node_id]
      by simp

    have successor_edge_before:
      "(new_node_id, successor_id)
         \<in> wire_edge_relation circuit wire"
      using
        successor_edge_after
        remaining_wire_relation_unchanged
      by simp

    show
      "successor_id = get_output_node_id wire"
      using
        Cons.prems(6)
        wire_in_remaining
        successor_edge_before
      by simp
  qed

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
        OF
        first_splice_preserves_frontier
        new_node_still_exists
        new_node_uses_remaining_wires
        remaining_wires_distinct
        new_node_not_remaining_frontiers
        new_node_has_no_other_successors_remaining
        ] .

  show ?case
    using splice_result remaining_splices_preserve_frontier
    by simp
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
  assumes valid_state:
    "is_valid_construction_state circuit frontier"

assumes operation_valid_for_circuit:
  "operation_in_circuit circuit op"

shows "is_valid_frontier
    (fst (insert_operation circuit frontier op))
    (snd (insert_operation circuit frontier op))"

proof -
  let ?circuit1 = "insert_node (next_id circuit) (OperationNode op) circuit"
  let ?splice_result = "splice_wires ?circuit1 frontier (op_qargs op) (next_id circuit)"

  let ?circuit2 = "fst ?splice_result"
  let ?frontier2 = "snd ?splice_result"

  let ?final_circuit = "?circuit2 \<lparr> next_id := increment_node_id (next_id circuit) \<rparr>"

  have valid_frontier:
    "is_valid_frontier circuit frontier"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have next_id_unused:
    "next_id_is_unused circuit"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have circuit_well_formed:
    "is_well_formed_circuit circuit"
    using valid_state
    unfolding is_valid_construction_state_def
    by simp

  have valid_operation:
    "is_valid_operation op"
    using operation_valid_for_circuit
    unfolding operation_in_circuit_def
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

  have operation_wires_distinct:
    (* A valid operation does not list the same qubit more than once. *)
    "distinct (op_qargs op)"
    using valid_operation
    unfolding is_valid_operation_def
    by simp

  have new_node_not_existing_frontiers:
    (* Every frontier ID already stores a node. Since next_id is unused,
       it cannot equal the frontier ID of any affected wire. *)
    "\<forall>q \<in> set (op_qargs op).
       next_id circuit \<noteq> frontier q"
  proof (intro ballI)
    fix q

    assume q_in_operation:
      "q \<in> set (op_qargs op)"

    have q_valid:
      "qubit_in_circuit circuit q"
      using
        operation_valid_for_circuit
        q_in_operation
      unfolding operation_in_circuit_def
      by simp

    from valid_frontier q_valid
    obtain frontier_node where frontier_exists:
      "nodes circuit (frontier q) = Some frontier_node"
      unfolding is_valid_frontier_def
      by blast

    show
      "next_id circuit \<noteq> frontier q"
    proof
      assume same_id:
        "next_id circuit = frontier q"

      from next_node_id_unused same_id have
        "nodes circuit (frontier q) = None"
        by simp

      with frontier_exists show False
        by simp
    qed
  qed

  have new_node_has_no_conflicting_successors:
    (* The old next_id was unused. Since every old edge is well formed,
       no old edge can use next_id as its source. Inserting the node does
       not alter the edge set, so the freshly inserted node initially has
       no outgoing edge on any affected wire. *)
    "\<forall>q \<in> set (op_qargs op).
       (\<forall>successor_id.
          ((next_id circuit), successor_id)
            \<in> wire_edge_relation ?circuit1 q
          \<longrightarrow> successor_id = get_output_node_id q)"
  proof (intro ballI allI impI)
    fix q successor_id

    assume successor_edge:
      "(next_id circuit, successor_id)
        \<in> wire_edge_relation ?circuit1 q"

    have old_edge:
      "make_edge (next_id circuit) successor_id q
        \<in> edges circuit"
      using successor_edge
      unfolding
        wire_edge_relation_def
        insert_node_def
      by simp

    have well_formed_edges:
      "are_well_formed_edges circuit"
      using circuit_well_formed
      unfolding is_well_formed_circuit_def
      by simp

    from well_formed_edges old_edge have source_exists:
      "node_exists circuit (next_id circuit)"
      unfolding
        are_well_formed_edges_def
        is_well_formed_edge_def
        make_edge_def
      by auto

    have False
      using
        source_exists
        next_node_id_unused
      unfolding node_exists_def
      by simp

    then show
      "successor_id = get_output_node_id q"
      by simp
  qed

  have frontier_after_splice:
    (* Splicing the newly inserted operation node into all of its qubit
       wires preserves the strengthened frontier invariant. *)
    "is_valid_frontier ?circuit2 ?frontier2"
    using
      frontier_after_insert_is_valid
      operation_node_exists
      operation_node_uses_all_qubits
      operation_wires_distinct
      new_node_not_existing_frontiers
      new_node_has_no_conflicting_successors
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

lemma insert_operation_preserves_other_nodes:
  (* Inserting an operation changes the nodes field only at the node ID
     that was next_id in the original circuit.

     Therefore, looking up any different node ID in the returned circuit
     gives exactly the same result as looking it up in the original
     circuit.
  *)
  assumes different_node_id:
    "other_node_id \<noteq> next_id circuit"

shows
  "nodes
       (fst (insert_operation circuit frontier op))
       other_node_id
     =
     nodes circuit other_node_id"
proof -
  show ?thesis
    using different_node_id
    unfolding
      insert_operation_def
      Let_def
      insert_node_def
      increment_node_id_def
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

end
