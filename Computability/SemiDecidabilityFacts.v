(** Coq coding by choukh, July 2022 **)

Require Import Notions NatEmbed PartialFunc.

Lemma 半可判定的偏函数表述 {M : 偏函数模型} {A} {p : A → Prop} :
  半可判定 p ↔ ∃ B (f : A ⇀ B), ∀ x, p x ↔ 有值 (f x).
Proof.
  split.
  - intros [f Hf].
    exists ℕ, (λ x, μ (f x)). intros x.
    rewrite (Hf x). split; intros [n H].
    + eapply μ有值. eauto.
    + eapply μ规则 in H as [H _]. eauto.
  - intros (B & f & Hf).
    exists (λ x n, if 求值 (f x) n is Some _ then true else false).
    intros x. rewrite Hf. split.
    + intros [y H]. apply 求值规则 in H as [n H].
      exists n. rewrite H. easy.
    + intros [n H]. destruct 求值 eqn:E.
      eexists. eapply 求值规则. eauto. discriminate.
Qed.
