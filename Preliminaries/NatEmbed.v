(** Coq coding by choukh, July 2022 **)

Require Export Meta.
Require Import PeanoNat.

(* f(n) = n(n+1)/2 *)
Local Fixpoint f n : ℕ := match n with
  | O => O
  | S m => n + f m
end.

(* 从 ℕ×ℕ 到 ℕ 的双射 *)
Definition F '(x, y) : ℕ := y + f (y + x).

(* 从 ℕ 到 ℕ×ℕ 的双射 *)
Fixpoint G (n : ℕ) : ℕ * ℕ := match n with
  | O => (0, 0)
  | S m => let '(x, y) := G m in match x with
    | O => (S y, 0)
    | S x => (x, S y)
    end
  end.

Lemma GF {p: ℕ * ℕ} : G (F p) = p.
Proof.
  cut (∀ n, F p = n → G n = p); auto.
  intro n. revert p. induction n as [|n IH].
  - intros [[|] [|]]; intro H; inversion H; reflexivity.
  - intros [x [|y]].
    + destruct x as [|x]; intro H. inversion H.
      simpl. rewrite (IH (0, x)). reflexivity.
      inversion H. simpl. rewrite Nat.add_0_r. reflexivity.
    + intro H. simpl. rewrite (IH (S x, y)). reflexivity.
      inversion H. simpl. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma FG {n: ℕ} : F (G n) = n.
Proof.
  induction n as [|n IH]. reflexivity.
  simpl. revert IH. destruct (G n) as [x y].
  destruct x as [|x]; intro IH; rewrite <- IH; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - repeat rewrite Nat.add_succ_r. simpl.
    rewrite Nat.add_succ_r. reflexivity.
Qed.

Notation "'λ'' ⟨ x , y ⟩ , b" := (λ n, let (x, y) := G n in b)
  (format "'λ''  ⟨ x ,  y ⟩ ,  b", at level 30, b at next level).

Notation "⟨ x , y ⟩" := (F (x, y)) (format "⟨ x ,  y ⟩").
Notation "⎞ n ⎛" := (G n) (format "⎞ n ⎛").

Example test1 x y : ⎞⟨x, y⟩⎛ = (x, y).
Proof. now rewrite GF. Qed.

Example test2 n : ⟨fst ⎞n⎛, snd ⎞n⎛⟩ = n.
Proof. now rewrite <- surjective_pairing, FG. Qed.
