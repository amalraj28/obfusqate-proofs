# ObfusQate DAG Formalisation

This branch develops a new Isabelle/HOL model of quantum circuits as directed acyclic graphs. It is intentionally independent of the earlier list-based circuit representation.

The immediate objective is to build a graph-native foundation for a certified implementation of the circuit-level transformations in ObfusQate:

- inverse-gate insertion,
- composite identity insertion,
- cloaked-gate replacement,
- delayed-gate replacement,
- later, basis transformations and hybrid control-flow constructions.

## Design basis

The model follows the wire-oriented structure of Qiskit's `DAGCircuit` rather than Qiskit's separate `DAGDependency` representation.

In a wire-oriented circuit DAG:

- nodes are input nodes, output nodes, or operation nodes;
- an edge is labelled by a qubit;
- an edge from `u` to `v` on qubit `q` means that the state of `q` passes from the output of `u` to the input of `v`;
- every qubit forms a directed chain from its unique input node to its unique output node;
- a multi-qubit operation lies on several qubit chains simultaneously.

This matches Qiskit's description of `DAGCircuit`, where input/output and operation nodes are connected by qubit or bit edges. QuantumFlow uses the same three-node structure and qubit-keyed edges. Qiskit's `DAGDependency` is useful for comparison, but its edges encode non-commutation rather than physical circuit wires. The wire-oriented model is preferable here because obfuscation rewrites must splice concrete subcircuits into selected qubit wires.

Primary references:

- Qiskit `DAGCircuit` source documentation: <https://github.com/Qiskit/qiskit/blob/main/qiskit/dagcircuit/dagcircuit.py>
- Qiskit `DAGDependency` source documentation: <https://github.com/Qiskit/qiskit/blob/main/qiskit/dagcircuit/dagdependency.py>
- QuantumFlow DAG circuit documentation: <https://quantumflow.readthedocs.io/en/latest/circuits.html>

## Repository layout

```text
.
├── README.md
├── ROOT
├── docs/
│   └── SPRINT_STATUS.md
├── examples/
│   └── DAGExamples.thy
└── src/
    └── DAG/
        ├── QuantumCircuitDAG.thy
        ├── DAGFragments.thy
        └── DAGTransformations.thy
```

## Core model

### Node identifiers

Every node has a natural-number identifier. Boundary identifiers are deterministic:

```text
input(q)  = 2 * q
output(q) = 2 * q + 1
```

Operation identifiers start at `2 * num_qubits`. Each circuit stores `dag_next_id`, the first identifier available for a fresh operation node.

### Node types

```isabelle
datatype 'gate dag_node =
    InputNode qubit
  | OutputNode qubit
  | OperationNode 'gate "qubit list"
```

An operation node stores:

- a gate payload of generic type `'gate`;
- an ordered list of qubit arguments.

The qubit list is ordered because control and target positions are semantically different for gates such as CNOT. Using a list inside an operation node does not make the circuit list-based. The circuit topology and execution order are represented exclusively by the graph.

### Edges

```isabelle
record dag_edge =
  edge_source :: node_id
  edge_target :: node_id
  edge_qubit  :: qubit
```

The edge label identifies the wire carried by the edge. A two-qubit operation therefore has incoming and outgoing edges on both of its qubits.

### Circuit record

```isabelle
record 'gate quantum_circuit_dag =
  dag_num_qubits :: nat
  dag_nodes      :: "node_id ⇒ 'gate dag_node option"
  dag_edges      :: "dag_edge set"
  dag_next_id    :: node_id
```

`dag_nodes` is a finite-support partial map represented as a total function returning `None` for unused identifiers. This representation supports executable lookup and Isabelle function update.

## Required invariants

`valid_dag G` combines the following properties:

1. `dag_nodes` has finite support and `dag_edges` is finite.
2. Every edge endpoint exists.
3. Every edge label is a valid qubit index.
4. Both endpoint nodes use the edge's qubit.
5. Every qubit has exactly one canonical input and output node.
6. Operation qubit arguments are non-empty, distinct, and in range.
7. Each input node has no predecessor and one successor on its wire.
8. Each output node has one predecessor and no successor on its wire.
9. Each operation has exactly one predecessor and successor on every qubit it uses.
10. The unlabelled edge relation is acyclic.
11. All used node identifiers are smaller than `dag_next_id`.

These local wire-degree constraints, together with finiteness and acyclicity, make every qubit a chain from its input node to its output node.

## Empty circuits

`empty_dag n` creates:

- one input and one output node for every qubit `q < n`;
- a direct edge `InputNode q → OutputNode q` on each wire;
- no operation nodes;
- `dag_next_id = 2 * n`.

This is the graph-level identity circuit on `n` qubits.

## Graph fragments

A replacement or insertion is represented by a `dag_fragment`. A fragment contains operation nodes only. It has no circuit-level input or output nodes because its boundary is supplied by the host circuit during splicing.

```isabelle
record 'gate dag_fragment =
  fragment_num_wires :: nat
  fragment_nodes     :: "node_id ⇒ 'gate dag_node option"
  fragment_edges     :: "dag_edge set"
  fragment_entry     :: "qubit ⇒ node_id option"
  fragment_exit      :: "qubit ⇒ node_id option"
  fragment_next_id   :: node_id
```

For each local wire:

- `fragment_entry q` identifies the first operation using that wire;
- `fragment_exit q` identifies the last operation using that wire;
- both are `None` when the fragment is the identity on that wire.

The initial implementation provides:

- `identity_fragment k`, with no operation nodes;
- `singleton_fragment gate k`, containing one `k`-qubit operation.

Later sprints will add graph-native serial and parallel fragment composition.

## Insertion

`insert_fragment_at_cuts G F cuts` inserts fragment `F` into circuit `G`.

`cuts i` identifies the host edge to cut for local fragment wire `i`. The host edge's qubit label determines the mapping from local wire `i` to the global qubit.

Insertion performs these graph edits:

1. allocate fresh node identifiers for all fragment nodes using `dag_next_id G` as an offset;
2. remove each selected host edge;
3. copy and rename the fragment's internal nodes and edges;
4. if a fragment wire has operations, connect the old predecessor to the fragment entry and the fragment exit to the old successor;
5. if a fragment wire is empty, restore the original host edge;
6. advance `dag_next_id`.

No linear position or global instruction index is used.

## Replacement

`replace_operation_with_fragment G v F` replaces operation node `v` by fragment `F`.

For every qubit argument of `v`, replacement:

1. finds the unique predecessor and successor of `v` on that qubit;
2. deletes `v` and all incident edges;
3. constructs a cut from that predecessor directly to that successor;
4. inserts `F` into those cuts.

The local fragment wire order is mapped to the target operation's ordered qubit arguments. For example, local wires `0` and `1` of a CNOT replacement map respectively to the original control and target qubits.

This operation is the formal counterpart of Qiskit's node-to-sub-DAG substitution.

## Semantic plan

The current files establish the structural graph layer. The next implementation step is semantic evaluation.

A DAG will be evaluated by a topological order of operation nodes. Each local gate will be embedded into the full Hilbert space according to its ordered qubit arguments. The main semantic obligations will be:

- independent topological orders produce the same matrix;
- inserting an identity fragment preserves evaluation;
- replacing a node with an equivalent fragment preserves evaluation.

Only after these generic theorems are established will the individual ObfusQate transformations be implemented.

## Build

From an Isabelle installation:

```bash
isabelle build -D . ObfusQate_DAG
```

The theories in this first implementation import only `Main`. Matrix semantics will be added in a later theory so that the graph core remains independent and easy to compile.
