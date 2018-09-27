(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import prelude ssreflect prop.

(** [eq x y], or simply [x=y] expresses the equality of [x] and
    [y]. Both [x] and [y] must belong to the same type [A].
    The definition is inductive and states the reflexivity of the equality.
    The others properties (symmetry, transitivity, replacement of
    equals by equals) are proved below. The type of [x] and [y] can be
    made explicit using the notation [x = y :> A]. This is Leibniz equality
    as it expresses that [x] and [y] are equal iff every property on
    [A] which is true of [x] is also true of [y] *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Inductive eq (A : Type) (x : A) : A -> Prop :=
  eq_refl : x = x :> A

where "x = y :> A" := (@eq A x y) : type_scope.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :> T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Arguments eq {A} x _.
Prenex Implicits eq_refl.
Arguments eq_refl {A x}, {A} x.

Arguments eq_ind [A] x P _ y _.
Arguments eq_rec [A] x P _ y _.
Arguments eq_rect [A] x P _ y _.

Section equality.

Context {A B : Type} (f : A -> B) {x y z : A}.

Lemma eq_sym : x = y -> y = x.
Proof. by case: _ /. Qed.

Lemma eq_trans : x = y -> y = z -> x = z.
Proof. by case: _ /. Qed.

Lemma eq_congr : x = y -> f x = f y.
Proof. by case: _ /. Qed.

End equality.

Register eq_sym as core.eq.sym.
Register eq_trans as core.eq.trans.
Register eq_congr as core.eq.congr.

Lemma neq_sym A (x y : A) : x <> y -> y <> x.
Proof. by move=> neq_xy /eq_sym. Qed.

(* A predicate for singleton types.                                           *)
Definition all_equal_to T (x0 : T) := forall x, unkeyed x = x0.

Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: eq_sym; trivial]
         | discriminate | contradiction | split]
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(* Quicker done tactic not including split, syntax: /0/ *)
Ltac ssrdone0 :=
  trivial; hnf; intros; solve
   [ do ![solve trivial
         | discriminate | contradiction ]
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].