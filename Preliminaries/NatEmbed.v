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

Global Opaque F G.

Notation "'λ'' ⟨ x , y ⟩ , b" := (λ n, let (x, y) := G n in b)
  (format "'λ''  ⟨ x ,  y ⟩ ,  b", at level 190, b at next level).

Notation "⟨ x , y ⟩" := (F (x, y)) (format "⟨ x ,  y ⟩").
Notation "⎞ n ⎛" := (G n) (format "⎞ n ⎛").

Lemma F_to_G xy x y : xy = ⟨x, y⟩ → ⎞xy⎛ = (x, y).
Proof. intros. now rewrite H, GF. Qed.

Lemma G_to_F xy x y : ⎞xy⎛ = (x, y) → xy = ⟨x, y⟩.
Proof. intros. now rewrite <- FG, H. Qed.

Lemma F单射 x y a b : ⟨x, y⟩ = ⟨a, b⟩ → x = a ∧ y = b.
Proof.
  intros H1. assert (H2: ⎞⟨x, y⟩⎛ = ⎞⟨a, b⟩⎛) by auto.
  rewrite GF, GF in H2. now apply pair_equal_spec.
Qed.

Lemma G单射 xy ab : ⎞xy⎛ = ⎞ab⎛ → xy = ab.
Proof.
  intros.
  destruct ⎞xy⎛ as [x y] eqn:E1.
  destruct ⎞ab⎛ as [a b] eqn:E2.
  apply pair_equal_spec in H as []; subst.
  apply G_to_F in E1, E2. congruence.
Qed.

Example FG_test x y : ⎞⟨x, y⟩⎛ = (x, y).
Proof. now rewrite GF. Qed.

Example GF_test xy : let (x, y) := ⎞xy⎛ in ⟨x, y⟩ = xy.
Proof. destruct ⎞xy⎛ as [x y] eqn:E. apply G_to_F in E. congruence. Qed.
