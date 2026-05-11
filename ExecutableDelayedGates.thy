theory ExecutableDelayedGates
  imports ExecutableGateNames DelayedGates
begin

text ‹
  Executable delayed-gate entry point.
  Use delayed_seq_id at code level, then use the bridge lemmas in
  ExecutableGateNames to relate the generated gate-name sequences to delayed_seq.
›

export_code delayed_seq_id
  in OCaml
  module_name ExecutableDelayedGates
  file "executable_delayed_gates.ml"

end
