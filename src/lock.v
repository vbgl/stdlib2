(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import prelude prop bool datatypes equality.

Lemma master_key : unit. Proof. exact tt. Qed.
Definition locked A := let: tt := master_key in fun x : A => x.

Lemma lock A x : x = locked x :> A. Proof. unlock; reflexivity. Qed.

(* Needed for locked predicates, in particular for eqType's.                  *)
Lemma not_locked_false_eq_true : locked false <> true.
Proof. unlock; discriminate. Qed.

(* To unlock opaque constants. *)
Structure unlockable T v := Unlockable {unlocked : T; _ : unlocked = v}.
Lemma unlock T x C : @unlocked T x C = x. Proof. by case: C. Qed.

Notation "[ 'unlockable' 'of' C ]" := (@Unlockable _ _ C (unlock _))
  (at level 0, format "[ 'unlockable'  'of'  C ]") : form_scope.

Notation "[ 'unlockable' 'fun' C ]" := (@Unlockable _ (fun _ => _) C (unlock _))
  (at level 0, format "[ 'unlockable'  'fun'  C ]") : form_scope.

(* Generic keyed constant locking. *)

(* The argument order ensures that k is always compared before T. *)
Definition locked_with k := let: tt := k in fun T x => x : T.

(* This can be used as a cheap alternative to cloning the unlockable instance *)
(* below, but with caution as unkeyed matching can be expensive.              *)
Lemma locked_withE T k x : unkeyed (locked_with k x) = x :> T.
Proof. by case: k. Qed.

(* Intensionaly, this instance will not apply to locked u. *)
Canonical locked_with_unlockable T k x :=
  @Unlockable T x (locked_with k x) (locked_withE k x).

(* More accurate variant of unlock, and safer alternative to locked_withE. *)
Lemma unlock_with T k x : unlocked (locked_with_unlockable k x) = x :> T.
Proof. exact: unlock. Qed.

(* The basic closing tactic "done".                                           *)
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(* Quicker done tactic not including split, syntax: /0/ *)
Ltac ssrdone0 :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction ]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].