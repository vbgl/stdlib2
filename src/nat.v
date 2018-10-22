Require Import prelude.

Inductive nat :=
| O
| S `(nat).

Register nat as num.nat.type.
Register O as num.nat.O.
Register S as num.nat.S.

Declare Scope nat_scope.

Arguments S _%nat_scope.

Notation "0" := O : nat_scope.
Notation "1" := (S 0) : nat_scope.
Notation "2" := (S 1) : nat_scope.
