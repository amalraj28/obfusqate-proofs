theory ExecutableInverseGates
  imports ExecutableGateNames InverseGates
begin

text ‹
  Executable inverse-gate entry point.
  The exported value is syntactic, while denote_inverses_id connects it to the
  existing matrix-table inverses used by inverseGates.
›

export_code inverses_id
  in OCaml
  module_name ExecutableInverseGates
  file "executable_inverse_gates.ml"

end
