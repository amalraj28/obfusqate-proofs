# Sprint status

## Sprint 1: DAG architecture and initial graph implementation

### Task 1: Review and architectural decision

**Status: complete**

- The new branch is independent of the list-based circuit representation.
- The model follows Qiskit's wire-oriented `DAGCircuit`.
- `DAGDependency` was considered but not selected because its edges represent non-commutation rather than concrete qubit wires.
- The design is documented in `README.md`.

### Task 2: Core DAG datatype and invariants

**Status: initial implementation complete**

Implemented in `src/DAG/QuantumCircuitDAG.thy`:

- input, output, and operation node types;
- qubit-labelled edges;
- finite-support node map;
- canonical boundary identifiers;
- graph queries;
- structural validity predicates;
- empty DAG constructor;
- basic node insertion and deletion operations.

Remaining proof work:

- prove `valid_dag (empty_dag n)`;
- derive per-wire path properties from local degree constraints and acyclicity;
- prove preservation of selected invariants under primitive graph updates.

### Task 3: Sub-DAG insertion and replacement design

**Status: initial implementation complete**

Implemented in:

- `src/DAG/DAGFragments.thy`
- `src/DAG/DAGTransformations.thy`

Included:

- open operation-only graph fragments;
- fragment entry and exit ports;
- identity and singleton fragments;
- fresh node renaming;
- graph-native insertion at selected wire cuts;
- operation replacement by a fragment;
- an exact structural theorem showing that inserting an empty identity fragment leaves the host circuit unchanged.

Remaining proof work:

- prove valid insertion preserves `valid_dag` under `valid_cuts` and `valid_fragment`;
- prove valid replacement preserves `valid_dag` under `replacement_applicable`;
- implement graph-native serial and parallel fragment composition;
- prove fragment composition validity.

### Task 4: Examples

**Status: initial implementation complete**

`examples/DAGExamples.thy` constructs a two-qubit graph, inserts `H`, and then inserts `CNOT`, producing the structural prefix of a Bell-state circuit.

## Next task

The next implementation step is to complete the structural proof obligations before introducing matrix semantics:

1. prove `empty_dag` is valid;
2. prove the fragment constructors are valid under appropriate arity assumptions;
3. prove insertion preserves graph validity;
4. prove replacement preserves graph validity.

After those the project can begin the semantic sprint: placement of local gates, topological evaluation, and topological-order independence.
