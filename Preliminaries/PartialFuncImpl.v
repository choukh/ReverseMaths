(** Coq coding by choukh, July 2022 **)

Require Import Meta Notions.

Section 模型实装.

Record 偏 A := {
  求值 : ℕ → A?;
  求值安定 : 安定 求值
}.
Arguments 求值 {_} _ _.
Notation "x @ n" := (求值 x n) (at level 50).

Section 给定类型A.
Context {A : Type}.

Definition 解包关系 (x : 偏 A) (a : A) := ∃ n, x @ n = Some a.
Notation "x ?= a" := (解包关系 x a) (at level 70).

Lemma 解包关系单射 : ∀ (x : 偏 A) a b, x ?= a → x ?= b → a = b.
Proof.
  intros x a b [n Hn] [m Hm].
  eapply 安定平稳. apply 求值安定. eauto. eauto.
Qed.

End 给定类型A.
End 模型实装.

Require PartialFunc.

(* TODO *)
Global Instance 可选值序列 : PartialFunc.偏函数模型.
Proof.
  unshelve econstructor.
  - exact 偏.
  - exact @解包关系.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - exact @解包关系单射.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
