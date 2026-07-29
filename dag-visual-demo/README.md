# Qiskit ↔ Isabelle DAG Laboratory

An offline visual aid for explaining the Qiskit DAGCircuit operations alongside
the formal model in `QuantumCircuit.thy`.

## Present

Open `index.html` in a modern browser. No server, installation, account, or
internet connection is required. Use a curated example or initialize a circuit,
choose Qiskit or Isabelle, choose a gate and ordered qubits, and press **Next
step** for each individual graph mutation. There is deliberately no autoplay.
The focused explainer contains its own controls, and every DAG flows from input
nodes at the top to output nodes at the bottom.

While a transformation is in progress, graph nodes cannot be selected and the
delete/replace controls are unavailable. Continue one step at a time or use
**Cancel operation** to restore the complete pre-operation state.

Insertion is always presented in four stages:

1. add the new node and node-table row beside the intended wire;
2. cut the old edge and connect the predecessor;
3. connect the successor;
4. show the completed DAG with temporary construction emphasis removed.

Whenever rows are added, removed, or updated, the node table shows a labelled
Before → After comparison. Only row insertion and deletion use table motion.

For CNOT, enter the **control first and target second**. For example, `0, 1`
means control `q0`, target `q1`. For CCNOT, enter two controls followed by the
target.

Click an operation node to enable deletion and replacement. Keyboard shortcuts:

- Left/Right: previous/next step

## Verify

With Node.js installed:

```powershell
node tests.js
```

The test suite uses only Node's standard library.

## Qiskit fidelity fixtures

The browser model is pinned to the documented behavior of Qiskit 2.4.1. The
optional `tools/export_qiskit_fixtures.py` script shows how maintainers can
regenerate compact structural traces from a real Qiskit installation. Qiskit is
not needed to run or present the website.

## Scope

This demonstrates symbolic DAG transformations, not quantum-state simulation.
The Qiskit wire end-point table is a labelled teaching view derived from graph
edges; it is not a public Qiskit `frontier` object.
