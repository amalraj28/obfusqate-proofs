# Consolidated QuantumCircuit architecture

## Result

The development is organized around feature ownership instead of proof phase.
There is one theory each for insertion, deletion, and replacement; supporting
data, graph, and construction-state logic is shared rather than duplicated.
The public `QuantumCircuit` theory contains the three existing full
valid-circuit preservation results and no low-level definitions or examples.

## Dependency design

`Quantum_Circuit_Data` defines the circuit representation and initial circuit.
`Quantum_Circuit_Graph` adds graph invariants and generic navigation.
`Quantum_Circuit_State` owns the frontier, allocation invariants, and primitive
node/edge updates used by multiple transformations.

Insertion, deletion, and replacement import State independently. This removes
the previous accidental source-order dependency in which deletion imported
insertion and replacement imported deletion. `QuantumCircuit` explicitly
imports all three feature theories and proves their public preservation
contracts. `Quantum_Circuit_Examples` imports `QuantumCircuit`, making examples
consumers of the public API rather than prerequisites of it.

## Public proof entry point

`generated/theories/QuantumCircuit.thy` owns exactly these authoritative
commands and proofs:

- `insert_operation_preserves_valid_quantum_circuit` (command 129)
- `delete_operation_preserves_valid_circuit` (command 195)
- `replacement_preserves_valid_circuit` (command 214)

The corresponding skeleton theory has the same three statements with `sorry`
proof bodies. Subcircuit replacement remains in the Replacement theory with
its existing well-formedness and acyclicity theorems; no full valid-circuit
preservation claim was added.

## Preservation and generation

All 317 content commands are assigned exactly once. Proved commands are copied
from the immutable authoritative theory using `manifests/source_map.json`.
Skeleton statements come from the validated working skeleton, with every
proof-bearing command—including both interpretations—normalized to `sorry`.
Theory headers, imports, `begin`, and `end` are synthetic structural metadata.

The old Core/Validity, Wire Splice, Construction, Navigation, Operation Replace,
and multi-file Subcircuit theory names were removed. A repository-wide scan
found no imports of those generated names outside the generated output trees,
so compatibility shims are unnecessary.
