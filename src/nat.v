Require Import prelude.

Inductive nat :=
| O
| S `(nat).

Register nat as num.nat.type.
Register O as num.nat.O.
Register S as num.nat.S.
