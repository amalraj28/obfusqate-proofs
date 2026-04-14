theory Executable1
  imports Circuit

begin

context gate
begin

abbreviation exec_qc:: "complex mat list" where
  "exec_qc \<equiv> [X,X]"

value "X"

value "Y"

value "Z"

value "S"

value "Sdg"

value "Id"

value "H"

value "T"

value "Tdg"

value "compose exec_qc 2"

value "take 0 exec_qc @ [X,Y,Z] @ drop 0 exec_qc"

value "take 0 exec_qc @ [Z,Z,Z] @ drop (Suc 0) exec_qc"
(* Just testing replacement. Not checking whether gate at index 0 is equivalent to ZZZ or not*)

end
end