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

fun gate_id_arity :: "gate_id ⇒ nat" where
  "gate_id_arity GX = 1"
| "gate_id_arity GY = 1"
| "gate_id_arity GZ = 1"
| "gate_id_arity GH = 1"
| "gate_id_arity GS = 1"
| "gate_id_arity GSdg = 1"
| "gate_id_arity GT = 1"
| "gate_id_arity GTdg = 1"
| "gate_id_arity GCNOT = 2"

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
| "cloak_seq_id G = [[G]]"

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
| "delayed_seq_id G = [[G]]"


subsection ‹Executable basis-transformation table›

fun basis_transform_seq_id :: "gate_id ⇒ gate_id list list" where
  (*
    """
      Defines the executable symbolic basis-transformation table.

      The table stores basis transformations as lists of symbolic gate names,
      keeping the executable circuit representation code-generation friendly.
      The initial table is conservative: X, Y, and Z receive nontrivial
      basis-style replacements, while all other gates fall back to the singleton
      sequence containing the original gate.

      args:
        g:
          The symbolic gate name to transform.

      returns:
        A list of symbolic replacement alternatives for the supplied gate.
    """
  *)
  "basis_transform_seq_id GX = [
      [GH, GZ, GH]
    ]"
| "basis_transform_seq_id GY = [
      [GSdg, GX, GS]
    ]"
| "basis_transform_seq_id GZ = [
      [GH, GX, GH]
    ]"
| "basis_transform_seq_id G = [[G]]"


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


lemma dim_row_denote_gate_id[simp]:
  "dim_row (denote_gate_id g) = 2 ^ gate_id_arity g"
  by (cases g) simp_all


lemma dim_col_denote_gate_id[simp]:
  "dim_col (denote_gate_id g) = 2 ^ gate_id_arity g"
  by (cases g) simp_all


lemma denote_gate_id_carrier:
  "denote_gate_id g ∈ carrier_mat
     (2 ^ gate_id_arity g)
     (2 ^ gate_id_arity g)"
  by auto


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


lemma selected_denoted_inverse_in_inverses:
  (*
    """
      Shows that any valid executable inverse-pair choice denotes one of the
      known matrix-level inverse-pair sequences.

      The executable inverse table stores inverse-pair alternatives using symbolic gate names.
      This lemma states that the selected executable alternative, after conversion into matrix gates,
      is a member of the existing matrix-level inverse table.

      args:
        choice:
          The selected executable inverse-pair alternative.

      assumptions:
        The selected choice is within the range of the executable inverse table.

      conclusion:
        The selected executable inverse-pair alternative, after conversion into
        matrix gates, belongs to the known matrix-level inverse-pair table.
    """
  *)
  assumes choice_lt: "choice < length inverses_id"
  shows "denote_gate_seq (inverses_id ! choice) \<in> set inverses"
  using choice_lt
  by (metis denote_gate_seqs_def denote_inverses_id length_map nth_map
      nth_mem)


lemma inverse_seq_id_selected_correct:
  (*
    """
      Proves that any selected executable inverse-pair alternative is correct
      after conversion into the matrix proof layer.

      The proof first shows that the selected executable sequence denotes one of
      the known matrix-level inverse-pair sequences. It then reuses the existing
      matrix-level inverse-pair correctness theorem.

      args:
        choice:
          The index of the selected executable inverse-pair alternative.

      assumptions:
        The selected choice is within the range of the executable inverse table.

      conclusion:
        The selected executable inverse-pair alternative, after conversion into
        matrix gates, composes to the identity matrix for the dimension of the
        selected inverse pair.
    """
  *)
  assumes choice_lt: "choice < length inverses_id"
  shows
    "compose (denote_gate_seq (inverses_id ! choice))
       (dim_row ((denote_gate_seq (inverses_id ! choice)) ! 0))
     =
     1\<^sub>m (dim_row ((denote_gate_seq (inverses_id ! choice)) ! 0))"
proof -
  have seq_in:
    "denote_gate_seq (inverses_id ! choice) ∈ set inverses"
    using choice_lt
    by (rule selected_denoted_inverse_in_inverses)

  show ?thesis
    using inverse_pair_identity[OF seq_in]
    by simp
qed


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


lemma length_denote_gate_seqs_eq:
  (*
    """
      Shows that denoting an executable sequence table does not change the
      number of available alternatives.

      The executable sequence table stores alternatives using symbolic gate
      names. Denoting the table only converts the gates inside each alternative
      into matrix gates. It does not add or remove alternatives.

      args:
        xs:
          The executable sequence table.

        ys:
          The matrix sequence table that corresponds to the executable table.

      assumptions:
        Denoting the executable sequence table gives the matrix sequence table.

      conclusion:
        The executable sequence table and the matrix sequence table contain the
        same number of alternatives.
    """
  *)
  assumes table_eq: "denote_gate_seqs xs = ys"
  shows "length xs = length ys"
proof -
  have "length (denote_gate_seqs xs) = length ys"
    using table_eq
    by simp
  then show ?thesis
    by (simp add: denote_gate_seqs_def)
qed


lemma nth_denote_gate_seqs_eq:
  (*
    """
      Shows that selecting an executable alternative and then denoting it gives
      the same matrix sequence as selecting the corresponding matrix-level
      alternative.

      The executable table and the matrix table have matching alternatives.
      This lemma is used when a particular alternative has been selected by
      index.

      args:
        xs:
          The executable sequence table.

        ys:
          The matrix sequence table that corresponds to the executable table.

        i:
          The selected alternative index.

      assumptions:
        Denoting the executable sequence table gives the matrix sequence table.

        The selected index is valid for the executable sequence table.

      conclusion:
        The selected executable alternative, after denotation, is the same as
        the corresponding selected matrix-level alternative.
    """
  *)
  assumes table_eq: "denote_gate_seqs xs = ys"
  assumes i_lt: "i < length xs"
  shows "denote_gate_seq (xs ! i) = ys ! i"
proof -
  have "denote_gate_seq (xs ! i) = denote_gate_seqs xs ! i"
    using i_lt
    by (simp add: denote_gate_seqs_def)
  also have "... = ys ! i"
    using table_eq
    by simp
  finally show ?thesis .
qed


lemma cloak_seq_id_correct:
  (*
    """
      Proves that every executable cloak sequence is correct after conversion
      into the matrix proof layer.

      The executable cloak table stores alternatives using symbolic gate names.
      This lemma shows that when a valid cloak alternative is selected, converting
      that symbolic sequence into matrix gates gives a sequence whose composition
      is equal to the matrix represented by the original symbolic gate.

      This lemma reuses the existing cloak sequence correctness theorem from
      the sequence proof layer and lifts it to the executable gate-name layer.

      args:
        g:
          The executable gate for which cloak alternatives are generated.

        choice:
          The index of the selected cloak alternative.

      assumptions:
        The selected choice is within the range of available executable cloak
        alternatives for the given gate.

      conclusion:
        The selected executable cloak alternative, after conversion into matrix
        gates, composes back to the matrix represented by the original executable
        gate.
    """
  *)
  assumes choice_lt: "choice < length (cloak_seq_id g)"
  shows
    "compose (denote_gate_seq ((cloak_seq_id g) ! choice))
       (dim_row (denote_gate_id g))
     =
     denote_gate_id g"
proof (cases g)
  case GX

  have bridge:
    "denote_gate_seqs (cloak_seq_id GX) = cloak_seq X"
    by (rule denote_cloak_seq_id_GX)

  have len_eq:
    "length (cloak_seq_id GX) = length (cloak_seq X)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (cloak_seq X)"
    using choice_lt GX len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((cloak_seq_id GX) ! choice) =
     (cloak_seq X) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GX
    by simp

  show ?thesis
    using GX choice_lt_matrix seq_eq by auto    

next
  case GY

  have bridge:
    "denote_gate_seqs (cloak_seq_id GY) = cloak_seq Y"
    by (rule denote_cloak_seq_id_GY)

  have len_eq:
    "length (cloak_seq_id GY) = length (cloak_seq Y)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (cloak_seq Y)"
    using choice_lt GY len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((cloak_seq_id GY) ! choice) =
     (cloak_seq Y) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GY
    by simp

  show ?thesis
    using GY choice_lt len_eq seq_eq by auto

next
  case GZ

  have bridge:
    "denote_gate_seqs (cloak_seq_id GZ) = cloak_seq Z"
    by (rule denote_cloak_seq_id_GZ)

  have len_eq:
    "length (cloak_seq_id GZ) = length (cloak_seq Z)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (cloak_seq Z)"
    using choice_lt GZ len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((cloak_seq_id GZ) ! choice) =
     (cloak_seq Z) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GZ
    by simp

  show ?thesis
    using GZ choice_lt len_eq seq_eq by auto

next
  case GH

  have only_choice:
    "choice = 0"
    using choice_lt GH
    by simp

  show ?thesis
    using GH only_choice
    by (simp add: denote_gate_seq_def)

next
  case GS

  have bridge:
    "denote_gate_seqs (cloak_seq_id GS) = cloak_seq S"
    by (rule denote_cloak_seq_id_GS)

  have len_eq:
    "length (cloak_seq_id GS) = length (cloak_seq S)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (cloak_seq S)"
    using choice_lt GS len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((cloak_seq_id GS) ! choice) =
     (cloak_seq S) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GS
    by simp

  show ?thesis
    using GS choice_lt len_eq seq_eq by auto

next
  case GSdg

  have only_choice:
    "choice = 0"
    using choice_lt GSdg
    by simp

  show ?thesis
    using GSdg only_choice
    by (simp add: denote_gate_seq_def)

next
  case GT

  have only_choice:
    "choice = 0"
    using choice_lt GT
    by simp

  show ?thesis
    using GT only_choice
    by (simp add: denote_gate_seq_def)

next
  case GTdg

  have only_choice:
    "choice = 0"
    using choice_lt GTdg
    by simp

  show ?thesis
    using GTdg only_choice
    by (simp add: denote_gate_seq_def)

next
  case GCNOT

  have only_choice:
    "choice = 0"
    using choice_lt GCNOT
    by simp

  show ?thesis
    using GCNOT only_choice
    by (simp add: denote_gate_seq_def)
qed


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


lemma delayed_seq_id_correct:
  (*
    """
      Proves that every executable delayed sequence is correct after conversion
      into the matrix proof layer.

      The executable delayed table stores alternatives using symbolic gate names.
      This lemma shows that when a valid delayed alternative is selected, converting
      that symbolic sequence into matrix gates gives a sequence whose composition
      is equal to the matrix represented by the original symbolic gate.

      This lemma reuses the existing delayed sequence correctness theorem from
      the sequence proof layer and lifts it to the executable gate-name layer.

      args:
        g:
          The executable gate for which delayed alternatives are generated.

        choice:
          The index of the selected delayed alternative.

      assumptions:
        The selected choice is within the range of available executable delayed
        alternatives for the given gate.

      conclusion:
        The selected executable delayed alternative, after conversion into matrix
        gates, composes back to the matrix represented by the original executable
        gate.
    """
  *)
  assumes choice_lt: "choice < length (delayed_seq_id g)"
  shows
    "compose (denote_gate_seq ((delayed_seq_id g) ! choice))
       (dim_row (denote_gate_id g))
     =
     denote_gate_id g"
proof (cases g)
  case GX

  have bridge:
    "denote_gate_seqs (delayed_seq_id GX) = delayed_seq X"
    by (rule denote_delayed_seq_id_GX)

  have len_eq:
    "length (delayed_seq_id GX) = length (delayed_seq X)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (delayed_seq X)"
    using choice_lt GX len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((delayed_seq_id GX) ! choice) =
     (delayed_seq X) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GX
    by simp

  show ?thesis
    using GX choice_lt_matrix seq_eq by auto    

next
  case GY

  have bridge:
    "denote_gate_seqs (delayed_seq_id GY) = delayed_seq Y"
    by (rule denote_delayed_seq_id_GY)

  have len_eq:
    "length (delayed_seq_id GY) = length (delayed_seq Y)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (delayed_seq Y)"
    using choice_lt GY len_eq
    by auto

  have seq_eq:
    "denote_gate_seq ((delayed_seq_id GY) ! choice) =
     (delayed_seq Y) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GY
    by simp

  show ?thesis
    using GY choice_lt_matrix seq_eq by fastforce

next
  case GZ

  have bridge:
    "denote_gate_seqs (delayed_seq_id GZ) = delayed_seq Z"
    by (rule denote_delayed_seq_id_GZ)

  have len_eq:
    "length (delayed_seq_id GZ) = length (delayed_seq Z)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (delayed_seq Z)"
    using choice_lt GZ len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((delayed_seq_id GZ) ! choice) =
     (delayed_seq Z) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GZ
    by simp

  show ?thesis
    using GZ choice_lt len_eq seq_eq by auto

next
  case GH

  have bridge:
    "denote_gate_seqs (delayed_seq_id GH) = delayed_seq H"
    by (rule denote_delayed_seq_id_GH)

  have len_eq:
    "length (delayed_seq_id GH) = length (delayed_seq H)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (delayed_seq H)"
    using choice_lt GH len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((delayed_seq_id GH) ! choice) =
     (delayed_seq H) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GH
    by simp

  show ?thesis
    using GH choice_lt_matrix seq_eq by auto

next
  case GS

  have bridge:
    "denote_gate_seqs (delayed_seq_id GS) = delayed_seq S"
    by (rule denote_delayed_seq_id_GS)

  have len_eq:
    "length (delayed_seq_id GS) = length (delayed_seq S)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (delayed_seq S)"
    using choice_lt GS len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((delayed_seq_id GS) ! choice) =
     (delayed_seq S) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GS
    by simp

  show ?thesis
    using GS choice_lt len_eq seq_eq by auto

next
  case GSdg

  have only_choice:
    "choice = 0"
    using choice_lt GSdg
    by simp

  show ?thesis
    using GSdg only_choice
    by (simp add: denote_gate_seq_def)

next
  case GT

  have bridge:
    "denote_gate_seqs (delayed_seq_id GT) = delayed_seq T"
    by (rule denote_delayed_seq_id_GT)

  have len_eq:
    "length (delayed_seq_id GT) = length (delayed_seq T)"
    using bridge
    by (rule length_denote_gate_seqs_eq)

  have choice_lt_matrix:
    "choice < length (delayed_seq T)"
    using choice_lt GT len_eq
    by simp

  have seq_eq:
    "denote_gate_seq ((delayed_seq_id GT) ! choice) =
     (delayed_seq T) ! choice"
    using nth_denote_gate_seqs_eq[OF bridge] choice_lt GT
    by simp

  show ?thesis
    using GT choice_lt_matrix seq_eq by auto

next
  case GTdg

  have only_choice:
    "choice = 0"
    using choice_lt GTdg
    by simp

  show ?thesis
    using GTdg only_choice
    by (simp add: denote_gate_seq_def)

next
  case GCNOT

  have only_choice:
    "choice = 0"
    using choice_lt GCNOT
    by simp

  show ?thesis
    using GCNOT only_choice
    by (simp add: denote_gate_seq_def)
qed


subsection ‹Bridge lemmas for basis transformations›

lemma basis_transform_seq_id_correct:
  (*
    """
      Proves that every executable basis-transformation sequence is correct
      after conversion into the matrix proof layer.

      The executable basis table stores alternatives using symbolic gate names.
      This lemma shows that when a valid basis alternative is selected,
      converting that symbolic sequence into matrices gives a local matrix
      sequence that composes back to the matrix represented by the original
      symbolic gate.

      args:
        g:
          The symbolic gate being transformed.

        idx:
          The selected executable basis-transformation alternative.

      assumptions:
        The selected basis-transformation index is within the alternatives
        available for the symbolic gate.

      conclusion:
        The selected executable basis alternative, after conversion into matrix
        gates, composes back to the matrix represented by the original executable
        gate.
    """
  *)
  assumes idx_lt: "idx < length (basis_transform_seq_id g)"
  shows
    "compose (denote_gate_seq ((basis_transform_seq_id g) ! idx))
       (dim_row (denote_gate_id g))
     =
     denote_gate_id g"
proof (cases g)
  case GX
  then have idx_eq: "idx = 0"
    using idx_lt by simp
  have local_eq: "compose [H, Z, H] 2 = X"
    using cloak_seq_correct_idx
    by (simp add: cloak_seq_def)
  show ?thesis
    using GX idx_eq local_eq
    by (simp add: denote_gate_seq_def)
next
  case GY
  then have idx_eq: "idx = 0"
    using idx_lt by simp

  have local_eq: "compose [Sdg, X, S] 2 = Y"
    using SdgXS_is_Y
    by simp

  show ?thesis
    using GY idx_eq local_eq
    by (simp add: denote_gate_seq_def)
next
  case GZ
  then have idx_eq: "idx = 0"
    using idx_lt by simp
  have local_eq: "compose [H, X, H] 2 = Z"
    using cloak_seq_correct_idx
    by (simp add: cloak_seq_def)
  show ?thesis
    using GZ idx_eq local_eq
    by (simp add: denote_gate_seq_def)
next
  case GH
  then show ?thesis
    using idx_lt by (simp add: denote_gate_seq_def)
next
  case GS
  then show ?thesis
    using idx_lt by (simp add: denote_gate_seq_def)
next
  case GSdg
  then show ?thesis
    using idx_lt by (simp add: denote_gate_seq_def)
next
  case GT
  then show ?thesis
    using idx_lt by (simp add: denote_gate_seq_def)
next
  case GTdg
  then show ?thesis
    using idx_lt by (simp add: denote_gate_seq_def)
next
  case GCNOT
  then show ?thesis
    using idx_lt by (simp add: denote_gate_seq_def)
qed

end


type_synonym circuit_id = "gate_id list"

definition insert_seq_id :: "circuit_id ⇒ nat ⇒ gate_id list ⇒ circuit_id" where
  "insert_seq_id qc pos seq = take pos qc @ seq @ drop pos qc"

definition replace_gate_id :: "circuit_id ⇒ nat ⇒ gate_id list ⇒ circuit_id" where
  "replace_gate_id qc pos seq = take pos qc @ seq @ drop (Suc pos) qc"

definition replace_by_cloak_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id" where
  "replace_by_cloak_id qc pos idx =
     replace_gate_id qc pos ((cloak_seq_id (qc ! pos)) ! idx)"

definition replace_by_delayed_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id" where
  "replace_by_delayed_id qc pos idx =
     replace_gate_id qc pos ((delayed_seq_id (qc ! pos)) ! idx)"

definition insert_inverse_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id" where
  "insert_inverse_id qc pos idx =
     insert_seq_id qc pos (inverses_id ! idx)"


definition can_replace_by_cloak_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ bool"
where
  (*
    """
      Checks whether an executable cloak replacement request is safe.

      The check ensures that the requested gate position exists in the
      executable gate-name circuit and that the requested cloak alternative is
      available for the gate at that position.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position of the gate to be replaced.

        idx:
          The selected cloak alternative.

      returns:
        True when the cloak replacement request can be applied safely, and
        False otherwise.
    """
  *)
  "can_replace_by_cloak_id qc pos idx ⟷
     pos < length qc ∧ idx < length (cloak_seq_id (qc ! pos))"


definition can_replace_by_delayed_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ bool"
where
  (*
    """
      Checks whether an executable delayed replacement request is safe.

      The check ensures that the requested gate position exists in the
      executable gate-name circuit and that the requested delayed alternative is
      available for the gate at that position.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position of the gate to be replaced.

        idx:
          The selected delayed alternative.

      returns:
        True when the delayed replacement request can be applied safely, and
        False otherwise.
    """
  *)
  "can_replace_by_delayed_id qc pos idx ⟷
     pos < length qc ∧ idx < length (delayed_seq_id (qc ! pos))"


definition can_insert_inverse_id ::
  "circuit_id ⇒ nat ⇒ nat ⇒ bool"
where
  (*
    """
      Checks whether an executable inverse-pair insertion request is safe.

      The check ensures that the requested insertion position is valid for the
      executable gate-name circuit and that the selected inverse-pair alternative
      exists in the executable inverse table.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position where the inverse-pair sequence should be inserted.

        idx:
          The selected inverse-pair alternative.

      returns:
        True when the inverse-pair insertion request can be applied safely, and
        False otherwise.
    """
  *)
  "can_insert_inverse_id qc pos idx ⟷
     pos ≤ length qc ∧ idx < length inverses_id"


definition replace_by_cloak_id_or_self ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id"
where
  (*
    """
      Applies executable cloak replacement when the request is valid, and
      otherwise returns the original circuit unchanged.

      This wrapper is intended for safe executable use. It avoids invalid list
      indexing by checking the requested position and cloak alternative before
      applying the underlying replacement function.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position of the gate to be replaced.

        idx:
          The selected cloak alternative.

      returns:
        The cloak-transformed circuit when the request is valid, and the
        original circuit otherwise.
    """
  *)
  "replace_by_cloak_id_or_self qc pos idx =
     (if can_replace_by_cloak_id qc pos idx
      then replace_by_cloak_id qc pos idx
      else qc)"


definition replace_by_delayed_id_or_self ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id"
where
  (*
    """
      Applies executable delayed replacement when the request is valid, and
      otherwise returns the original circuit unchanged.

      This wrapper is intended for safe executable use. It avoids invalid list
      indexing by checking the requested position and delayed alternative before
      applying the underlying replacement function.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position of the gate to be replaced.

        idx:
          The selected delayed alternative.

      returns:
        The delayed-transformed circuit when the request is valid, and the
        original circuit otherwise.
    """
  *)
  "replace_by_delayed_id_or_self qc pos idx =
     (if can_replace_by_delayed_id qc pos idx
      then replace_by_delayed_id qc pos idx
      else qc)"


definition insert_inverse_id_or_self ::
  "circuit_id ⇒ nat ⇒ nat ⇒ circuit_id"
where
  (*
    """
      Applies executable inverse-pair insertion when the request is valid, and
      otherwise returns the original circuit unchanged.

      This wrapper is intended for safe executable use. It avoids invalid list
      indexing by checking the requested insertion position and inverse-pair
      alternative before applying the underlying insertion function.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position where the inverse-pair sequence should be inserted.

        idx:
          The selected inverse-pair alternative.

      returns:
        The circuit with the inverse-pair sequence inserted when the request is
        valid, and the original circuit otherwise.
    """
  *)
  "insert_inverse_id_or_self qc pos idx =
     (if can_insert_inverse_id qc pos idx
      then insert_inverse_id qc pos idx
      else qc)"


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


lemma denote_replace_by_cloak_id:
  (*
    """
      Shows that executable cloak replacement commutes with denotation.

      Replacing a symbolic gate by a selected symbolic cloak sequence and then
      converting the circuit into matrix gates gives the same matrix gate list
      as first converting the original symbolic circuit and then replacing the
      corresponding matrix gate by the denoted selected cloak sequence.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position of the gate to be replaced.

        idx:
          The selected cloak alternative.

      conclusion:
        Denotation commutes with executable cloak replacement.
    """
  *)
  shows
    "denote_gate_seq (replace_by_cloak_id qc pos idx) =
     replace_gate
       (denote_gate_seq qc)
       pos
       (denote_gate_seq ((cloak_seq_id (qc ! pos)) ! idx))"
  by (simp add:replace_by_cloak_id_def denote_replace_gate_id)


lemma denote_replace_by_delayed_id:
  (*
    """
      Shows that executable delayed replacement commutes with denotation.

      Replacing a symbolic gate by a selected symbolic delayed sequence and then
      converting the circuit into matrix gates gives the same matrix gate list
      as first converting the original symbolic circuit and then replacing the
      corresponding matrix gate by the denoted selected delayed sequence.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position of the gate to be replaced.

        idx:
          The selected delayed alternative.

      conclusion:
        Denotation commutes with executable delayed replacement.
    """
  *)
  shows
    "denote_gate_seq (replace_by_delayed_id qc pos idx) =
     replace_gate
       (denote_gate_seq qc)
       pos
       (denote_gate_seq ((delayed_seq_id (qc ! pos)) ! idx))"
  by (simp add:
      replace_by_delayed_id_def
      denote_replace_gate_id)


lemma denote_insert_inverse_id:
  (*
    """
      Shows that executable inverse-pair insertion commutes with denotation.

      Inserting a symbolic inverse-pair sequence and then converting the circuit
      into matrix gates gives the same matrix gate list as first converting the
      original symbolic circuit and then inserting the denoted inverse-pair
      sequence.

      args:
        qc:
          The executable gate-name circuit.

        pos:
          The position where the inverse-pair sequence is inserted.

        idx:
          The selected inverse-pair alternative.

      conclusion:
        Denotation commutes with executable inverse-pair insertion.
    """
  *)
  shows
    "denote_gate_seq (insert_inverse_id qc pos idx) =
     insert_seq
       (denote_gate_seq qc)
       pos
       (denote_gate_seq (inverses_id ! idx))"
  by (simp add:
      insert_inverse_id_def
      denote_insert_seq_id)

end

subsection ‹Code generation entry points›

value "cloak_seq_id GX"
value "basis_transform_seq_id GX"

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
  inverses_id cloak_seq_id delayed_seq_id basis_transform_seq_id
  insert_seq_id replace_gate_id
  replace_by_cloak_id replace_by_delayed_id insert_inverse_id
  can_replace_by_cloak_id can_replace_by_delayed_id can_insert_inverse_id
  replace_by_cloak_id_or_self
  replace_by_delayed_id_or_self
  insert_inverse_id_or_self
  in OCaml
  module_name ExecutableGateNames
  file "executable_gate_names.ml"

end
