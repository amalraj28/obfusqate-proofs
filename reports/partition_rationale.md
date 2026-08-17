# Stage 3 partition rationale

## Result

The 321-command monolith can be split into sixteen content theories plus a
compatibility wrapper without changing any definition, theorem statement,
name, assumption, attribute, or within-group order. The proposed import graph
is intentionally a source-order chain. That is the safest architecture for
mechanical proof restoration because every declaration and side effect visible
at a command in the monolith remains visible at its new location.

Stage 4 is approved to generate skeleton-only content theories. The
authoritative root `QuantumCircuit.thy` remains immutable.

## Partition boundaries

| Output theory | Commands | Authoritative lines | Purpose |
|---|---:|---:|---|
| `Quantum_Circuit_Model` | 4–30 | 6–210 | Datatypes, records, identifiers, initial circuit |
| `Quantum_Circuit_Graph` | 31–60 | 217–1264 | Graph relations, validity, wire linearity, initial proofs |
| `Quantum_Circuit_Construction` | 61–85 | 1272–1725 | Allocation, frontier, primitive edits, construction state |
| `Quantum_Circuit_Wire_Splice` | 86–104 | 1729–2506 | Single-wire splice and reachability preservation |
| `Quantum_Circuit_Insert_Core` | 105–119 | 2508–4807 | Multi-wire splice, insertion, construction invariants |
| `Quantum_Circuit_Insert_Validity` | 120–130 | 4809–8283 | Insertion linearity, acyclicity, and full validity |
| `Quantum_Circuit_Navigation` | 131–140 | 8289–8688 | Edge lookup and predecessor/successor operations |
| `Quantum_Circuit_Delete_Core` | 141–171 | 8694–11915 | Reconnection, deletion effects, well-formedness |
| `Quantum_Circuit_Delete_Validity` | 172–195 | 11917–15377 | Deletion reachability, degrees, acyclicity, linearity, validity |
| `Quantum_Circuit_Operation_Replace` | 196–214 | 15381–16744 | Same-node operation replacement |
| `Quantum_Circuit_Subcircuit_Model` | 215–244 | 16748–17282 | Subcircuit interfaces, validity, renaming |
| `Quantum_Circuit_Subcircuit_Edit` | 245–270 | 17284–17816 | Node removal and renamed node/internal-edge insertion |
| `Quantum_Circuit_Subcircuit_Connect` | 271–294 | 17818–18707 | Interface connection, fold interpretations, frontier update |
| `Quantum_Circuit_Subcircuit_Replace_Core` | 295–312 | 18709–22704 | Replacement construction and structural/well-formedness proofs |
| `Quantum_Circuit_Subcircuit_Replace_Acyclicity` | 313–318 | 22707–24101 | Cycle reflection/classification and acyclicity |
| `Quantum_Circuit_Examples` | 319–320 | 24107–24114 | Example values |
| `QuantumCircuit_Skeleton` | 1–3, 321 | 1–4, 24116 | Original header/footer represented as wrapper metadata |

The split points are all existing top-level command boundaries. No logical
group is internally reordered. Large proof regions are separated only where a
stable public result closes one concern and the next command begins another:
for example, insertion construction-state preservation ends at command 119,
while the reachability/linearity/acyclicity argument starts at command 120.

## Dependency and scope safety

Each content theory imports its immediate predecessor. Although some imports
could later be weakened, doing that during mechanical restructuring would add
risk without changing the result. The chain preserves source-order visibility
of declarations, simp attributes, named theorem collections, and global
interpretations.

There are no `locale`, `context`, or `sublocale` commands in the skeleton. The
two interpretation commands require special care:

- command 278, `interpretation connect_subcircuit_input`, stays beside its
  commutativity lemma (277) and its consumers (279–280);
- command 288, `interpretation connect_subcircuit_output`, stays beside its
  commutativity lemma (287) and consumer (289).

All are kept in `Quantum_Circuit_Subcircuit_Connect`, so no interpretation
proof or generated fold fact crosses a file boundary. The sole `section`
command, command 215, remains the first command of the subcircuit model.

## Comments and source text

The current skeleton contains no Isabelle block comments and no `text`
commands. Blank-line trivia should follow the command it precedes, with final
trivia attached to command 321. Commands themselves—including whitespace and
the statements ending in `sorry`—should be copied verbatim during Stage 4.
Only theory headers, imports, `begin`, and `end` are synthesized for the new
files.

The original four structural commands are represented once as metadata. They
are not copied verbatim: every generated theory header, import, `begin`, and
`end` is synthesized. `Complex_Main` becomes the direct import of the first
content theory. Stage 5 will generate the proved compatibility wrapper at
`generated/theories/QuantumCircuit.thy`, importing the final generated content
theory; it does not alter the authoritative root `QuantumCircuit.thy`.

## Mechanical proof-restoration implications

Every content partition is a contiguous interval of source-map command IDs.
Stage 4 can therefore extract skeleton text in ordinal order, and Stage 5 can
restore every proof-bearing outer command by the same IDs without theorem-name
guessing, including `interpretation` commands as well as lemma/theorem-like
commands. File boundaries do not split a theorem, definition, interpretation
proof, or logical command. No future stage may claim full valid-circuit
preservation for subcircuit replacement unless the source inventory contains
the corresponding theorem.

The authoritative line ranges in the manifest are informational guards, not
instructions to edit `QuantumCircuit.thy`. The input hashes pin this plan to the
validated skeleton and source map at Git commit `cf1a3859fc8f04cbf197807f75442691302e9067`.

## Inventory validation

The manifest owns commands through inclusive intervals. Expanding those
intervals yields 321 assignments and 321 unique command IDs. The sorted IDs are
exactly `1..321`; there are no gaps, duplicates, out-of-range IDs, or endpoint
mismatches against `manifests/source_map.json`.

Stage 4 must re-run the declared validation before writing generated theories
and must stop if either input hash or any command endpoint differs.
