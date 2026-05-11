theory ExecutableCloakedGates
  imports ExecutableGateNames CloakedGates
begin

text ‹
  Executable cloaked-gate entry point.
  Use cloak_seq_id at code level, then use the bridge lemmas in
  ExecutableGateNames to relate the generated gate-name sequences to cloak_seq.
›

export_code cloak_seq_id
  in OCaml
  module_name ExecutableCloakedGates
  file "executable_cloaked_gates.ml"

end
