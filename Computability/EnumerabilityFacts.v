(** Coq coding by choukh, July 2022 **)

Require Import Notions NatEmbed PartialFunc.

Lemma 可枚举的偏函数表述 {M : 偏函数模型} {A} (p : A → Prop) :
  可枚举 p ↔ ∃ f : ℕ ⇀ A, ∀ x, p x ↔ ∃ n, f n ?= x.
Proof.
  split.
  - intros [f Hf]. exists (λ n, if f n is Some x then 有 x else 无).
    intros x. rewrite (Hf x).
    split; intros [n H]; exists n; destruct (f n).
    + apply 有值解包. congruence.
    + congruence.
    + apply 有值解包 in H. congruence.
    + now apply 无规则 in H.
  - intros [f Hf]. exists (λ' ⟨n, m⟩, 求值 (f n) m).
    intros x. rewrite (Hf x). split.
    + intros [n H]. apply 求值规则 in H as [m H].
      exists ⟨n, m⟩. rewrite GF. easy.
    + intros [nm H]. destruct ⎞nm⎛ as [n m].
      eexists. eapply 求值规则. eauto.
Qed.
