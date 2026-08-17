# Stage 4 validation

- Skeleton SHA-256: passed (`19be416dd8983c90ec7c968f392f3d491c301f7fe0481b7afb8fc57d47dd017b`).
- Source-map SHA-256: passed (`e3299be7c87c0fab7f9ae0dcf9a89af909448da423a89463063945daaf0809d2`).
- Source map: passed; 321 mappings; ordinal kind/name bijection passed.
- Partition ownership: commands 1..321 assigned exactly once; generated content owns 4..320 exactly once (317 commands).
- Import DAG: passed; 17 edges; acyclic.
- Structural source commands 1, 2, 3, and 321 are metadata only; headers/wrappers are synthesized.
- Proof-bearing command inventory includes 2 interpretation commands (278, 288); their proof bodies are `sorry`, and no proof command token is present.
- No generated/theories compatibility wrapper was created in Stage 4.

## Generated files

- `generated/skeleton/Quantum_Circuit_Model.thy`
- `generated/skeleton/Quantum_Circuit_Graph.thy`
- `generated/skeleton/Quantum_Circuit_Construction.thy`
- `generated/skeleton/Quantum_Circuit_Wire_Splice.thy`
- `generated/skeleton/Quantum_Circuit_Insert_Core.thy`
- `generated/skeleton/Quantum_Circuit_Insert_Validity.thy`
- `generated/skeleton/Quantum_Circuit_Navigation.thy`
- `generated/skeleton/Quantum_Circuit_Delete_Core.thy`
- `generated/skeleton/Quantum_Circuit_Delete_Validity.thy`
- `generated/skeleton/Quantum_Circuit_Operation_Replace.thy`
- `generated/skeleton/Quantum_Circuit_Subcircuit_Model.thy`
- `generated/skeleton/Quantum_Circuit_Subcircuit_Edit.thy`
- `generated/skeleton/Quantum_Circuit_Subcircuit_Connect.thy`
- `generated/skeleton/Quantum_Circuit_Subcircuit_Replace_Core.thy`
- `generated/skeleton/Quantum_Circuit_Subcircuit_Replace_Acyclicity.thy`
- `generated/skeleton/Quantum_Circuit_Examples.thy`
- `generated/skeleton/QuantumCircuit_Skeleton.thy`
