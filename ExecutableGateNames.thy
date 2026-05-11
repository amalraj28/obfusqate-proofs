theory ExecutableGateNames
  imports Circuit
begin

text ‹
  Executable syntax layer for gate sequences.

  The existing proof layer remains unchanged: all correctness lemmas still talk
  about complex matrices such as X, H, T, Sdg, etc. This file only introduces
  a first-order datatype that can be exported as code, together with a denotation
  function back into the existing matrix proof world.
›

datatype gate_id =
    GX
  | GY
  | GZ
  | GH
  | GS
  | GSdg
  | GT
  | GTdg
  | GCNOT

subsection ‹Executable inverse-pair table›

definition inverses_id :: "gate_id list list" where
  "inverses_id = [
     [GX, GX],
     [GY, GY],
     [GZ, GZ],
     [GH, GH],
     [GT, GTdg],
     [GTdg, GT],
     [GS, GSdg],
     [GSdg, GS],
     [GCNOT, GCNOT]
   ]"

subsection ‹Executable cloaked-gate table›

fun cloak_seq_id :: "gate_id ⇒ gate_id list list" where
  "cloak_seq_id GX = [
      [GH, GZ, GH],
      [GS, GY, GS, GZ],
      [GZ, GSdg, GY, GSdg],
      [GH, GY, GZ, GH, GY],
      [GY, GH, GZ, GY, GH],
      [GH, GY, GH, GY, GSdg, GY, GS],
      [GSdg, GY, GS, GH, GY, GH, GY],
      [GS, GY, GSdg]
    ]"
| "cloak_seq_id GY = [
      [GSdg, GX, GS],
      [GSdg, GX, GZ, GSdg],
      [GS, GZ, GX, GS]
    ]"
| "cloak_seq_id GZ = [
      [GH, GX, GH],
      [GX, GS, GY, GS],
      [GSdg, GY, GSdg, GX],
      [GY, GH, GX, GY, GH],
      [GH, GY, GX, GH, GY],
      [GS, GS],
      [GT, GT, GT, GT]
    ]"
| "cloak_seq_id GS = [
      [GT, GT],
      [GZ, GT, GZ, GT],
      [GTdg, GTdg, GZ]
    ]"
| "cloak_seq_id _ = []"

subsection ‹Executable delayed-gate table›

fun delayed_seq_id :: "gate_id ⇒ gate_id list list" where
  "delayed_seq_id GX = [
      [GH, GZ, GX, GH, GZ],
      [GH, GY, GH, GY, GZ, GX, GZ],
      [GH, GY, GH, GX, GY],
      [GY, GX, GH, GY, GH],
      [GZ, GH, GX, GZ, GH],
      [GZ, GX, GZ, GY, GH, GY, GH]
    ]"
| "delayed_seq_id GY = [
      [GX, GH, GY, GH, GX]
    ]"
| "delayed_seq_id GZ = [
      [GH, GY, GH, GZ, GY],
      [GY, GZ, GH, GY, GH],
      [GH, GY, GH, GY, GX, GZ, GX],
      [GX, GZ, GX, GY, GH, GY, GH],
      [GX, GH, GZ, GX, GH],
      [GH, GX, GZ, GH, GX],
      [GSdg, GZ, GS],
      [GS, GZ, GSdg]
    ]"
| "delayed_seq_id GH = [
      [GX, GZ, GH, GX, GZ],
      [GZ, GX, GH, GZ, GX]
    ]"
| "delayed_seq_id GS = [
      [GZ, GT, GS, GTdg, GZ],
      [GZ, GTdg, GS, GT, GZ],
      [GH, GY, GH, GS, GX]
    ]"
| "delayed_seq_id GT = [
      [GZ, GSdg, GT, GS, GZ],
      [GZ, GS, GT, GSdg, GZ]
    ]"
| "delayed_seq_id _ = []"

subsection ‹Denotation into the existing proof layer›

context gate
begin

fun denote_gate_id :: "gate_id ⇒ complex mat" where
  "denote_gate_id GX = X"
| "denote_gate_id GY = Y"
| "denote_gate_id GZ = Z"
| "denote_gate_id GH = H"
| "denote_gate_id GS = S"
| "denote_gate_id GSdg = Sdg"
| "denote_gate_id GT = T"
| "denote_gate_id GTdg = Tdg"
| "denote_gate_id GCNOT = CNOT"

definition denote_gate_seq :: "gate_id list ⇒ complex mat list" where
  "denote_gate_seq xs = map denote_gate_id xs"

definition denote_gate_seqs :: "gate_id list list ⇒ complex mat list list" where
  "denote_gate_seqs xss = map denote_gate_seq xss"

lemma denote_gate_seq_simps[simp]:
  "denote_gate_seq [] = []"
  "denote_gate_seq (x # xs) = denote_gate_id x # denote_gate_seq xs"
  by (simp_all add: denote_gate_seq_def)

lemma denote_gate_seqs_simps[simp]:
  "denote_gate_seqs [] = []"
  "denote_gate_seqs (xs # xss) = denote_gate_seq xs # denote_gate_seqs xss"
  by (simp_all add: denote_gate_seqs_def)

subsection ‹Bridge lemmas for inverse pairs›

lemma denote_inverses_id:
  "denote_gate_seqs inverses_id = inverses"
  by (simp add: denote_gate_seqs_def denote_gate_seq_def inverses_id_def inverses_def)

subsection ‹Bridge lemmas for cloaked gates›

lemma denote_cloak_seq_id_GX:
  "denote_gate_seqs (cloak_seq_id GX) = cloak_seq X"
  by (simp add: denote_gate_seqs_def denote_gate_seq_def cloak_seq_def)

lemma denote_cloak_seq_id_GY:
  "denote_gate_seqs (cloak_seq_id GY) = cloak_seq Y"
  apply (simp add: denote_gate_seqs_def denote_gate_seq_def cloak_seq_def X_def Y_def)
  using X_def X_neq_Y Y_def by presburger

lemma denote_cloak_seq_id_GZ:
  "denote_gate_seqs (cloak_seq_id GZ) = cloak_seq Z"
  using X_neq_Z Y_neq_Z cloak_seq_def cloak_seq_id.simps(3) denote_gate_id.simps(1,2,4,5,6,7) denote_gate_seq_simps(1,2)
    denote_gate_seqs_simps(1,2) by presburger

lemma denote_cloak_seq_id_GS:
  "denote_gate_seqs (cloak_seq_id GS) = cloak_seq S"
  apply (simp add: denote_gate_seqs_def denote_gate_seq_def cloak_seq_def X_def Y_def Z_def S_def)
  using S_def X_def X_neq_S Y_def Y_neq_S Z_def Z_neq_S by presburger

subsection ‹Bridge lemmas for delayed gates›

lemma denote_delayed_seq_id_GX:
  "denote_gate_seqs (delayed_seq_id GX) = delayed_seq X"
  by (simp add: denote_gate_seqs_def denote_gate_seq_def delayed_seq_def)

lemma denote_delayed_seq_id_GY:
  "denote_gate_seqs (delayed_seq_id GY) = delayed_seq Y"
  apply (simp add: denote_gate_seqs_def denote_gate_seq_def delayed_seq_def X_def Y_def)
  using X_def X_neq_Y Y_def by presburger

lemma denote_delayed_seq_id_GZ:
  "denote_gate_seqs (delayed_seq_id GZ) = delayed_seq Z"
  apply (simp add: denote_gate_seqs_def denote_gate_seq_def delayed_seq_def X_def Y_def Z_def)
  using X_def X_neq_Z Y_def Y_neq_Z Z_def by presburger

lemma denote_delayed_seq_id_GH:
  "denote_gate_seqs (delayed_seq_id GH) = delayed_seq H"
  apply (simp add: denote_gate_seqs_def denote_gate_seq_def delayed_seq_def X_def Y_def Z_def H_def)
  using H_def X_def Y_def Z_def by force

lemma denote_delayed_seq_id_GS:
  "denote_gate_seqs (delayed_seq_id GS) = delayed_seq S"
  apply (simp add: denote_gate_seqs_def denote_gate_seq_def delayed_seq_def X_def Y_def Z_def H_def S_def)
  by (metis (no_types, lifting) H_def H_neq_S S_def X_def X_neq_S Y_def Y_neq_S Z_def Z_neq_S of_real_1
      of_real_divide)

lemma denote_delayed_seq_id_GT:
  "denote_gate_seqs (delayed_seq_id GT) = delayed_seq T"
  by (metis (mono_tags, lifting) H_neq_T T_neq_S T_neq_X T_neq_Y T_neq_Z Z_is_gate delayed_seq_id.simps(6)
      denote_gate_id.simps(3,5,6,7) denote_gate_seq_simps(1) denote_gate_seqs_simps(1) gate.delayed_seq_def
      gate.denote_gate_seq_simps(2) gate.denote_gate_seqs_simps(2))
end


type_synonym circuit_id = "gate_id list"

definition insert_seq_id :: "circuit_id ⇒ nat ⇒ gate_id list ⇒ circuit_id" where
  "insert_seq_id qc pos seq = take pos qc @ seq @ drop pos qc"

definition replace_gate_id :: "circuit_id ⇒ nat ⇒ gate_id list ⇒ circuit_id" where
  "replace_gate_id qc pos seq = take pos qc @ seq @ drop (Suc pos) qc"

definition replace_by_cloak_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id" where
  "replace_by_cloak_id qc pos alt =
     replace_gate_id qc pos ((cloak_seq_id (qc ! pos)) ! alt)"

definition replace_by_delayed_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id" where
  "replace_by_delayed_id qc pos alt =
     replace_gate_id qc pos ((delayed_seq_id (qc ! pos)) ! alt)"

definition insert_inverse_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id" where
  "insert_inverse_id qc pos alt =
     insert_seq_id qc pos (inverses_id ! alt)"

context gate
begin

lemma denote_insert_seq_id:
  "denote_gate_seq (insert_seq_id qc pos seq) =
   insert_seq (denote_gate_seq qc) pos (denote_gate_seq seq)"
  by (simp add: insert_seq_id_def insert_seq_def denote_gate_seq_def drop_map take_map)

lemma denote_replace_gate_id:
  "denote_gate_seq (replace_gate_id qc pos seq) =
   replace_gate (denote_gate_seq qc) pos (denote_gate_seq seq)"
  by (simp add: denote_gate_seq_def drop_map replace_gate_def
      replace_gate_id_def take_map)
end

subsection ‹Code generation entry points›

value "cloak_seq_id GX"

value "insert_seq_id [GX, GH, GT] 1 [GT, GTdg]"
value "replace_gate_id [GX, GH, GT] 1 [GH, GZ, GH]"
value "replace_gate_id [GX, GH, GT] 0 ((cloak_seq_id GX) ! 1)"
value "cloak_seq_id GX"
value "delayed_seq_id GH"
value "inverses_id"
value "replace_by_cloak_id [GX, GH, GT] 0 0"
value "replace_by_cloak_id [GX, GH, GT] 0 1"
value "replace_by_delayed_id [GX, GH, GT] 1 0"
value "insert_inverse_id [GX, GH, GT] 1 5"

export_code
  inverses_id cloak_seq_id delayed_seq_id
  insert_seq_id replace_gate_id
  replace_by_cloak_id replace_by_delayed_id insert_inverse_id
  in OCaml
  module_name ExecutableGateNames
  file "executable_gate_names.ml"

end
