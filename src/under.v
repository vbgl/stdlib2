(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import prelude ssreflect prop equality datatypes.

(*****************************************************************************)
(* Constants for under, to rewrite under binders using "Leibniz eta lemmas". *)

Module Type UNDER_EQ.
Parameter Under_eq :
  forall (R : Type), R -> R -> Prop.
Parameter Under_eq_from_eq :
  forall (T : Type) (x y : T), @Under_eq T x y -> x = y.

(** [Over_eq, over_eq, over_eq_done]: for "by rewrite over_eq" *)
Parameter Over_eq :
  forall (R : Type), R -> R -> Prop.
Parameter over_eq :
  forall (T : Type) (x : T) (y : T), @Under_eq T x y = @Over_eq T x y.
Parameter over_eq_done :
  forall (T : Type) (x : T), @Over_eq T x x.
(* We need both hints below, otherwise the test-suite does not pass *)
Hint Extern 0 (@Over_eq _ _ _) => solve [ apply over_eq_done ] : core.
(* => for [test-suite/ssr/under.v:test_big_patt1] *)
Hint Resolve over_eq_done : core.
(* => for [test-suite/ssr/over.v:test_over_1_1] *)

(** [under_eq_done]: for Ltac-style over *)
Parameter under_eq_done :
  forall (T : Type) (x : T), @Under_eq T x x.
Notation "''Under[' x ]" := (@Under_eq _ x _)
  (at level 8, format "''Under['  x  ]", only printing).
End UNDER_EQ.

Module Export Under_eq : UNDER_EQ.
Definition Under_eq := @eq.
Lemma Under_eq_from_eq (T : Type) (x y : T) :
  @Under_eq T x y -> x = y.
Proof. by []. Qed.
Definition Over_eq := Under_eq.
Lemma over_eq :
  forall (T : Type) (x : T) (y : T), @Under_eq T x y = @Over_eq T x y.
Proof. by []. Qed.
Lemma over_eq_done :
  forall (T : Type) (x : T), @Over_eq T x x.
Proof. by []. Qed.
Lemma under_eq_done :
  forall (T : Type) (x : T), @Under_eq T x x.
Proof. by []. Qed.
End Under_eq.

Register Under_eq as plugins.ssreflect.Under_eq.
Register Under_eq_from_eq as plugins.ssreflect.Under_eq_from_eq.

Module Type UNDER_IFF.
Parameter Under_iff : Prop -> Prop -> Prop.
Parameter Under_iff_from_iff : forall x y : Prop, @Under_iff x y -> x <-> y.

(** [Over_iff, over_iff, over_iff_done]: for "by rewrite over_iff" *)
Parameter Over_iff : Prop -> Prop -> Prop.
Parameter over_iff :
  forall (x : Prop) (y : Prop), @Under_iff x y = @Over_iff x y.
Parameter over_iff_done :
  forall (x : Prop), @Over_iff x x.
Hint Extern 0 (@Over_iff _ _) => solve [ apply over_iff_done ] : core.
Hint Resolve over_iff_done : core.

(** [under_iff_done]: for Ltac-style over *)
Parameter under_iff_done :
  forall (x : Prop), @Under_iff x x.
Notation "''Under[' x ]" := (@Under_iff x _)
  (at level 8, format "''Under['  x  ]", only printing).
End UNDER_IFF.

Module Export Under_iff : UNDER_IFF.
Definition Under_iff := iff.
Lemma Under_iff_from_iff (x y : Prop) :
  @Under_iff x y -> x <-> y.
Proof. by []. Qed.
Definition Over_iff := Under_iff.
Lemma over_iff :
  forall (x : Prop) (y : Prop), @Under_iff x y = @Over_iff x y.
Proof. by []. Qed.
Lemma over_iff_done :
  forall (x : Prop), @Over_iff x x.
Proof. by []. Qed.
Lemma under_iff_done :
  forall (x : Prop), @Under_iff x x.
Proof. by []. Qed.
End Under_iff.

Register Under_iff as plugins.ssreflect.Under_iff.
Register Under_iff_from_iff as plugins.ssreflect.Under_iff_from_iff.

Definition over := (over_eq, over_iff).

Ltac over :=
  by [ apply: Under_eq.under_eq_done
     | apply: Under_iff.under_iff_done
     | rewrite over
     ].
