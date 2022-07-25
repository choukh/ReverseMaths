(** Coq coding by choukh, July 2022 **)

Require Export Meta.
Require Import Lia Notions.

(* 满足 p 的不小于 n 的最小数 m *)
Definition 最小 p n m := p m ∧ n ≤ m ∧ ∀ k, n ≤ k → p k → m ≤ k.

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
Theorem 自然数布尔大消除 n : f n = true → Σ n, f n = true ∧ ∀ k, k < n → f k = false.
Proof.
  intros H. pose proof (G_提取 0) as [m [H1 [_ H2]]].
  - apply (G_0 n). constructor. rewrite H. discriminate.
  - exists m. split. apply H1. intros k fk.
    destruct (f k) eqn:E. 2:easy.
    enough (m ≤ k) by lia. apply H2. lia. apply E.
Qed.

End 布尔值编码.

Theorem 自然数命题大消除 (p : ℕ → Prop) : 逻辑可判定 p →
  ∀ n, p n → Σ n, p n ∧ ∀ k, k < n → ¬ p k.
Proof.
  intros dec n pn.
  pose proof (自然数布尔大消除 (λ n, if dec n then true else false) n) as [m [dm min]].
  - abstract (destruct (dec n); auto).
  - exists m. destruct (dec m) as [pm|npm]. 2:discriminate.
    split. apply pm. intros k km. pose proof (min k km).
    destruct (dec k) as [|npk]. discriminate. apply npk.
Qed.
