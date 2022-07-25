(** Coq coding by choukh, July 2022 **)

Require Export Utf8.

(* 让auto策略可使用typeclass实例 *)
Global Hint Extern 4 => exact _ : core.

Ltac inv H := inversion H; subst; try clear H.

Notation ℕ := nat.

Notation "A ?" := (option A) (format "A ?", at level 20).

Notation "P ⇔ Q" := (prod (P → Q) (Q → P)) (at level 95).

(* 存在量词式Σ类型记法 *)
Notation "'Σ' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
    format "'[' 'Σ'  '/ ' x .. y ,  '/ ' p ']'") : type_scope.

Notation "'if' x 'is' p 'then' a 'else' b" :=
  (match x with p => a | _ => b end) (at level 200, p pattern).

(* 反柯里化 *)
Notation "'uncurry' R" := (λ '(x, y), R x y) (only parsing, at level 10).
