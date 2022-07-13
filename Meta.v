(** Coq coding by choukh, July 2022 **)

Require Export Utf8_core.

Notation ℕ := nat.

Notation "A ?" := (option A) (format "A ?", at level 20).

(* 存在量词式Σ类型记法 *)
Notation "'Σ' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
    format "'[' 'Σ'  '/ ' x .. y ,  '/ ' p ']'") : type_scope.

Notation "'if' x 'is' p 'then' a 'else' b" :=
  (match x with p => a | _ => b end) (at level 200, p pattern).

Ltac inv H := inversion H; subst; try clear H.
