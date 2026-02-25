theory ObfuscationProofs
  imports Main
begin

datatype gate = H | X | Y | Z | S | Sdg | T | Tdg

locale gate_semantics =
  fixes U :: "gate ⇒ 's ⇒ 's"
    and cloaked :: "gate ⇒ nat ⇒ gate list"
    and delayed :: "gate ⇒ nat ⇒ gate list"
  assumes H_H:  "U H (U H s) = s"
      and X_X:  "U X (U X s) = s"
      and Y_Y:  "U Y (U Y s) = s"
      and Z_Z:  "U Z (U Z s) = s"
      and S_Sdg:    "U Sdg (U S s) = s"  "U S (U Sdg s) = s"
      and T_Tdg:    "U Tdg (U T s) = s"  "U T (U Tdg s) = s"
      and cloaked_ok:
        "∀g v s. apply_seq (cloaked g v) s = U g s"
      and delayed_ok:
        "∀g v s. apply_seq (delayed g v) s = U g s"
begin

fun apply_seq :: "gate list ⇒ 's ⇒ 's" where
  "apply_seq [] s = s"
| "apply_seq (g # gs) s = apply_seq gs (U g s)"

fun inv_of :: "gate ⇒ gate" where
  "inv_of H = H"
| "inv_of X = X"
| "inv_of Y = Y"
| "inv_of Z = Z"
| "inv_of S = Sdg"
| "inv_of Sdg = S"
| "inv_of T = Tdg"
| "inv_of Tdg = T"

definition inv_seq :: "gate list ⇒ gate list" where
  "inv_seq xs = map inv_of (rev xs)"

definition aux_seq :: "gate list" where
  "aux_seq = [H, H, Z, X, Z, X]"

definition res_seq :: "gate list" where
  "res_seq = [X, Z, X, Z, H, H]"

definition aux_res_seq :: "gate list" where
  "aux_res_seq = aux_seq @ res_seq"

definition invpair :: "gate ⇒ gate list" where
  "invpair g = [g] @ inv_seq [g]"

fun insert_at :: "nat ⇒ gate list ⇒ gate list ⇒ gate list" where
  "insert_at 0 ins xs = ins @ xs"
| "insert_at (Suc n) ins [] = ins"          (* or ins @ [] depending on your choice *)
| "insert_at (Suc n) ins (x#xs) = x # insert_at n ins xs"

lemma apply_seq_append:
  "apply_seq (xs @ ys) s = apply_seq ys (apply_seq xs s)"
  by (induct xs arbitrary: s) auto

lemma inv_of_cancel: "U (inv_of g) (U g s) = s"
  by (cases g; simp add: H_H X_X Y_Y Z_Z S_Sdg T_Tdg)

lemma apply_seq_inv_seq:
  "apply_seq (xs @ inv_seq xs) s = s"
  unfolding inv_seq_def
  by (induct xs arbitrary: s) (auto simp: apply_seq_append inv_of_cancel)

lemma res_is_inverse_aux:
  "res_seq = inv_seq aux_seq"
  unfolding res_seq_def aux_seq_def inv_seq_def
  by simp

lemma aux_res_id:
  "∀s. apply_seq aux_res_seq s = s"
  by (intro allI) (simp add: aux_res_seq_def res_is_inverse_aux apply_seq_inv_seq)

  (* 
    proof
      fix s
      have "apply_seq aux_res_seq s = apply_seq (aux_seq @ res_seq) s"
        by (simp add: aux_res_seq_def)
      also have "... = apply_seq (aux_seq @ inv_seq aux_seq) s"
        by (simp add: res_is_inverse_aux)
      also have "... = s"
        by (simp add: apply_seq_inv_seq)
      finally show "apply_seq aux_res_seq s = s" .
    qed
  *)

lemma insert_identity_preserves:
  assumes "∀s. apply_seq ins s = s"  (* identity sequence *)
  shows   "apply_seq (insert_at k ins xs) s = apply_seq xs s"
  using assms
  by (induct k ins xs arbitrary: s rule: insert_at.induct)
     (auto simp: apply_seq_append)+

lemma invpair_id: "∀s. apply_seq (invpair g) s = s"
  unfolding invpair_def inv_seq_def
  by (intro allI) (simp add: inv_of_cancel)

fun replace_at :: "nat ⇒ gate ⇒ gate list ⇒ gate list ⇒ gate list" where
  "replace_at 0 g rep [] = []"
| "replace_at 0 g rep (x # xs) = (if x = g then rep @ xs else x # xs)"
| "replace_at (Suc n) g rep [] = []"
| "replace_at (Suc n) g rep (x # xs) = x # replace_at n g rep xs"


theorem insert_invpair_preserves:
  "apply_seq (insert_at k (invpair g) xs) s = apply_seq xs s"
  using insert_identity_preserves invpair_id
  by simp

lemma replace_semantics_preserves:
  assumes rep_ok: "∀s. apply_seq rep s = U g s"
  shows "apply_seq (replace_at k g rep xs) s = apply_seq xs s"
  using rep_ok
proof (induct k g rep xs arbitrary: s rule: replace_at.induct)
  case (1 g rep)
  then show ?case by simp
next
  case (2 g rep x xs)
  then show ?case
    by (simp add: apply_seq_append)
next
  case (3 n g rep)
  then show ?case by simp
next
  case (4 n g rep x xs)
  then show ?case by simp
qed


theorem replace_cloaked_preserves:
  "apply_seq (replace_at k g (cloaked g v) xs) s = apply_seq xs s"
  by (rule replace_semantics_preserves, simp add: cloaked_ok)

theorem replace_delayed_preserves:
  "apply_seq (replace_at k g (delayed g v) xs) s = apply_seq xs s"
  by (rule replace_semantics_preserves, simp add: delayed_ok)

end

end
