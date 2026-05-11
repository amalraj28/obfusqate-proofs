theory ExecutableObfusQate
  imports ExecutableInverseGates ExecutableCloakedGates ExecutableDelayedGates
begin

text ‹Combined executable entry point for the current phase-1 gate-sequence layer.›

export_code
  inverses_id cloak_seq_id delayed_seq_id
  insert_seq_id replace_gate_id
  replace_by_cloak_id replace_by_delayed_id insert_inverse_id
  in OCaml
  module_name ExecutableObfusQate
  file "executable_obfusqate.ml"

end
