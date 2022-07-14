(** Coq coding by choukh, July 2022 **)

Require Import Equivalence.

Theorem Cantor's {A} (f : A → (A → Prop)) : ¬ ∀ p, ∃ x, f x ≡{_} p.
Proof.
  intros sur. pose (g x := ¬ (f x x)).
  destruct (sur g) as [a fa]. firstorder.
Qed.
