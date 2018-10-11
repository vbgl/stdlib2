(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file contains basic propositional connectives *)

Require Import prelude ssreflect.

(** Notations for propositional connectives *)

Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "~ x" (at level 75, right associativity).

(** [True] is the always true proposition *)

Variant True : Prop :=
  I : True.

(** [False] is the always false proposition *)

Inductive False : Prop :=.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A : Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

(** Create the “core” hint database, and set its transparent state for
  variables and constants explicitely. *)
Create HintDb core.
Hint Variables Opaque : core.
Hint Constants Opaque : core.

Hint Unfold not: core.

(* The basic closing tactic "done".                                           *)
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve trivial
         | discriminate | contradiction | split]
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(* Quicker done tactic not including split, syntax: /0/ *)
Ltac ssrdone0 :=
  trivial; hnf; intros; solve
   [ do ![solve trivial
         | discriminate | contradiction ]
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(** [and A B], written [A /\ B], is the conjunction of [A] and [B]

    [and_intro p q] is a proof of [A /\ B] as soon as
    [p] is a proof of [A] and [q] a proof of [B]

    [and_fst] and [and_snd] are first and second projections of a conjunction *)

Record and (A B : Prop) : Prop :=
  and_intro { and_proj1 : A; and_proj2 : B }.

Reserved Notation "x /\ y" (at level 80, right associativity).
Notation "A /\ B" := (and A B) : type_scope.

Record iff (A B : Prop) : Prop :=
  iff_intro { iff_proj1 : A -> B; iff_proj2 : B -> A }.
Notation "A <-> B" := (iff A B) : type_scope.

(* View lemmas that don't use reflection.                                     *)

Section ApplyIff.

Variables P Q : Prop.
Hypothesis eqPQ : P <-> Q.

Lemma iffLR : P -> Q. Proof. by case: eqPQ. Qed.
Lemma iffRL : Q -> P. Proof. by case: eqPQ. Qed.

Lemma iffLRn : ~P -> ~Q. Proof. by move=> nP tQ; case: nP; case: eqPQ tQ. Qed.
Lemma iffRLn : ~Q -> ~P. Proof. by move=> nQ tP; case: nQ; case: eqPQ tP. Qed.

End ApplyIff.

Hint View for move/ iffLRn|2 iffRLn|2 iffLR|2 iffRL|2.
Hint View for apply/ iffRLn|2 iffLRn|2 iffRL|2 iffLR|2.
