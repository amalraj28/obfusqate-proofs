# Graph-library survey (Stage 1)

Survey date: 2026-08-05.  The local installation is Isabelle2025-2 at
`C:\Users\AMAL\Desktop\Isabelle2025-2`.  No AFP checkout/component was found
there, so entries marked **web-only** are not currently importable in this
workspace.  This report is a survey only; it makes no source changes.

## Project representation relevant to the comparison

The revalidated working skeleton represents a circuit's unlabelled graph as a
binary relation `edge_relation :: quantum_circuit => (node_id * node_id) set`
(lines 203--208) and a per-wire graph as `wire_edge_relation ::
quantum_circuit => qubit => (node_id * node_id) set` (lines 213--216).
`wire_reaches` is exactly membership in `(^+)` (lines 218--227), while
`is_acyclic_circuit` is exactly `acyclic (edge_relation circuit)` (lines
210--211).  The project retains the wire label in its `edge` record and
projects labels away for relation reasoning.

`insert_edge` and `delete_edge` are record updates around set `insert` and
difference (lines 487--494).  `delete_operation` is not mere vertex removal:
it reconnects each used wire and then updates the node map to `None` (lines
1429 onward).  Replacement also maps renamed subcircuit endpoints while
preserving wire labels.  The skeleton contains no requested topological-order
definition or graph-isomorphism definition.

This means the standard binary-relation libraries are a direct fit for generic
reachability and DAG arguments; any full graph framework must be bridged from
labelled circuit edges and record updates.

## Locally verified Isabelle/HOL candidates

### `HOL.Transitive_Closure` — direct core fit

- **Availability:** local and verified.
- **Theory/import:** `Transitive_Closure`, importing `Finite_Set`; source
  `C:\Users\AMAL\Desktop\Isabelle2025-2\src\HOL\Transitive_Closure.thy`.
  It is normally available through `Main`.
- **Representation:** binary relation as `('a * 'a) set`, exactly the type of
  `edge_relation` and each `wire_edge_relation circuit q`.
- **Verified material:** `rtrancl`/`(^*)` (line 29), `trancl`/`(^+)` (line 35),
  `rtrancl_mono` (187), `trancl_mono_subset` (441), `tranclD` (624),
  `rtrancl_eq_or_trancl` (706), `trancl_insert` (718), `rtrancl_insert` (735),
  `acyclic` (1502), `acyclicI` (1511), `acyclic_insert` (1524),
  `acyclic_converse` (1527), and `acyclic_subset` (1543).
- **Usefulness:** reachability/path closure, adding an edge without a cycle,
  deletion via subset/monotonicity, and predecessor reasoning by converse.
- **Fit/confidence:** direct / high.

### `HOL.Wellfounded` — finite-DAG bridge

- **Availability:** local and verified.
- **Theory/import:** `Wellfounded`; source
  `C:\Users\AMAL\Desktop\Isabelle2025-2\src\HOL\Wellfounded.thy` (the
  theory imports the relation/closure infrastructure).
- **Representation:** binary relations, matching the project after projecting
  labelled edges to endpoint pairs.
- **Verified material:** `wf_insert` (561), `wf_acyclic` (893),
  `finite_acyclic_wf` (901), `finite_acyclic_wf_converse` (910), and
  `wf_iff_acyclic_if_finite` (931).
- **Usefulness:** derive a well-founded order from a finite acyclic circuit,
  which is the standard route to topological/minimal-node arguments.
- **Fit/confidence:** direct for relation-level DAG reasoning; bridge needed
  for circuit finiteness / high.

### `HOL.Hoare.SchorrWaite` — reachability-set patterns only

- **Availability:** local and verified.
- **Theory/import:** `Hoare.SchorrWaite`; source
  `C:\Users\AMAL\Desktop\Isabelle2025-2\src\HOL\Hoare\SchorrWaite.thy`.
- **Verified material:** `self_reachable` (35), `oneStep_reachable` (39),
  `still_reachable` (43), `still_reachable_eq` (53), and
  `reachable_union_sym` (71).  These use `r^* `` A`.
- **Usefulness:** illustrative lemmas for source-set reachability under
  relation changes; not a reusable, generic graph API.
- **Fit/confidence:** partial / medium.

## AFP candidates (web-only; not locally installed)

### `Graph_Theory` — broad directed-graph framework

- **Availability:** web-only.  The AFP entry reports session `Graph_Theory`;
  theories include `Rtrancl_On`, `Digraph`, `Arc_Walk`, `Pair_Digraph`,
  `Vertex_Walk`, `Digraph_Isomorphism`, and `Subdivision`.
- **Source:** [AFP Graph Theory entry](https://devel.isa-afp.org/entries/Graph_Theory.html).
- **Representation:** directed graphs support labelled multi-edges and
  infinite graphs; pairs may be used as edge values.
- **Verified scope:** walks, connectedness, subgraphs, and basic graph
  isomorphism, as documented by the entry.
- **Fit/confidence:** strong for future labelled-edge/isomorphism work, but a
  representation bridge is required and importing it adds an AFP dependency /
  high that the entry exists, medium for direct lemma reuse.

### `Graph_Algorithms` — pair-set digraphs and walks

- **Availability:** web-only.  Session `Graph_Algorithms`; relevant theories
  `Pair_Graph`, `Vwalk`, `Pair_Graph_Specs`, `DFS`, and `BFS_2`.
- **Source:** [AFP Graph Algorithms entry](https://devel.isa-afp.org/entries/Graph_Algorithms.html),
  [current proof document](https://www.isa-afp.org/browser_info/current/AFP/Graph_Algorithms/document.pdf).
- **Imports/definitions verified in the current document:** `Pair_Graph`
  imports `Main` and `Graph-Theory.Rtrancl-On`; it declares
  `type_synonym 'v dgraph = ('v * 'v) set` and `dVs`.  `Vwalk` imports
  `Pair_Graph` and declares `vwalk`.  `Pair_Graph_Specs` includes executable
  adjacency-map abstraction, with `digraph_abs_delete` proving deletion maps
  to pair-set difference.
- **Fit/confidence:** relation-level representation is close, but the circuit's
  labels, nodes map, and splice operations still need a bridge / medium.

### `Prpu_Maxflow.Graph_Topological_Ordering` — topological-list predicate

- **Availability:** web-only.  AFP session `Prpu_Maxflow`, theory
  `Graph_Topological_Ordering`.
- **Source:** [AFP Push-Relabel entry](https://www.isa-afp.org/entries/Prpu_Maxflow.html),
  [current proof document](https://www.isa-afp.org/browser_info/current/AFP/Prpu_Maxflow/document.pdf).
- **Imports verified:** `Refine_Imperative_HOL.Sepref_Misc` and
  `List_Index.List_Index`.
- **Verified material:** `is_top_sorted R l` is defined as
  `list_before_rel l ∩ (R^*)^-1 = {}`; the document lists
  `is_top_sorted_alt`, `is_top_sorted_distinct`,
  `is_top_sorted_remove_elem`, `is_top_sorted_antimono`, and
  `is_top_sorted_isolated_constraint`.
- **Fit/confidence:** the revalidated skeleton has no topological-order
  requirement.  Keep this only as a future reference; avoid importing its
  substantial refinement dependencies / medium for existence, low for current
  relevance.

### `Graph_Saturation.GraphRewriting` — domain-specific rewriting

- **Availability:** web-only.  AFP session `Graph_Saturation`, theory
  `GraphRewriting` (also `LabeledGraphs`, `RulesAndChains`).
- **Source:** [AFP Graph Saturation entry](https://isa-afp.org/entries/Graph_Saturation.html).
- **Scope:** labelled graph saturation/rule application; the entry documents
  graph-rewriting and logical saturation rather than mutable circuit graphs.
- **Fit/confidence:** conceptually adjacent to replacement/splicing but not a
  direct model of node deletion, edge rewiring, or renaming / low.

### `Relational_Paths` — algebraic paths and a topological-sort algorithm

- **Availability:** web-only.  Session `Relational_Paths`; theories
  `More_Relation_Algebra`, `Paths`, `Rooted_Paths`, and `Path_Algorithms`.
- **Source:** [AFP Relational Paths entry](https://devel.isa-afp.org/entries/Relational_Paths.html),
  [proof outline](https://www.isa-afp.org/browser_info/current/AFP/Relational_Paths/outline.pdf).
- **Imports verified:** `Path_Algorithms` imports `HOL-Hoare.Hoare_Logic` and
  `Rooted_Paths`; `More_Relation_Algebra` imports Relation Algebra theories.
  The outline contains `topological_sort_total` and path predicates such as
  `terminating_path`.
- **Fit/confidence:** rich but algebraically abstract and dependency-heavy;
  unsuitable as a first replacement target for the current set-of-pairs
  development / low-to-medium.

## Recommendation

Keep the project representation.  Stage 7 should first inspect custom proofs
against the local `Transitive_Closure` and `Wellfounded` facts, especially
`trancl_insert`, `acyclic_insert`, `acyclic_subset`, and converse/closure
lemmas.  These apply to the skeleton's projected relations, including its
edge-splice and reachability proofs.  Do not add an AFP dependency unless a
later approved replacement needs graph isomorphism, explicit walks, or
explicit topological lists; none of the web-only entries is a drop-in
replacement for labelled circuit-node records or their splice/delete
operations.
