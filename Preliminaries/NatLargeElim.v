(** Coq coding by choukh, July 2022 **)

Require Export Meta.
Require Import Lia Notions.

(* 满足 p 的不小于 n 的最小数 m *)
Definition 最小 p n m := p m ∧ n <= m ∧ ∀ k, n <= k → p k → m <= k.

Section 布尔值编码.

(* 自然数子集 *)
Variable f : ℕ → bool.

(* 计算语义版的 存在 n ≤ m 使得 f m = true *)
Inductive G (n : ℕ) : Prop :=
  | GI : (f n = false → G (S n)) → G n.

Lemma G_0 n : G n → G 0.
Proof.
  induction n as [|n IH].
  - easy.
  - intros GSn. apply IH. constructor. easy.
Qed.

(* 提取不小于n的最小元 *)
Lemma G_提取 n : G n → Σ m, 最小 (λ k, f k = true) n m.
Proof.
  intros Gn. induction Gn as [n _ IH].
  destruct (f n) eqn: fn.
  - exists n. easy.
  - destruct (IH eq_refl) as (m & pm & le & min).
    exists m. repeat split.
    + apply pm.
    + lia.
    + intros k Hk. inversion Hk.
      * congruence.
      * apply min. lia.
Qed.

(* 从非空子集中构造地提取最小元 *)
Lemma 非空提取 : (∃ n, f n = true) → Σ n, 最小 (λ k, f k = true) 0 n.
Proof.
  intros H. apply (G_提取 0).
  destruct H as [n H]. apply (G_0 n).
  constructor. rewrite H. discriminate.
Qed.

End 布尔值编码.

Theorem 自然数大消除 (p : ℕ → Prop) : 强逻辑可判定 p →
  (∃ n, p n) → Σ n, p n.
Proof.
  intros dec Hn.
  destruct (非空提取 (λ n, if dec n then true else false)) as [n H].
  - abstract (destruct Hn as [n H]; exists n; destruct dec; firstorder).
  - exists n. destruct H as [H _]. destruct (dec n). easy. congruence.
Defined.

Theorem 自然数大消除_最小性 p dec ex m : m < projT1 (自然数大消除 p dec ex) → ¬ p m.
Proof.
  intros lt. unfold 自然数大消除 in lt.
  destruct 非空提取 as [n (H1 & H2 & H3)]. simpl in lt.
  assert ((if dec m then true else false) = true → n <= m). apply H3. lia.
  intros npm. destruct (dec m). lia. easy.
Qed.
