(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import datatypes.

(** An interface for non-Prop types; used to avoid improper instantiation
    of polymorphic lemmas with on-demand implicits when they are used as views.
    For example: Some_inj {T} : forall x y : T, Some x = Some y -> x = y.
    Using move/Some_inj on a goal of the form Some n = Some 0 will fail:
    SSReflect will interpret the view as @Some_inj ?T _top_assumption_
    since this is the well-typed application of the view with the minimal
    number of inserted evars (taking ?T := Some n = Some 0), and then will
    later complain that it cannot erase _top_assumption_ after having
    abstracted the viewed assumption. Making x and y maximal implicits
    would avoid this and force the intended @Some_inj nat x y _top_assumption_
    interpretation, but is undesirable as it makes it harder to use Some_inj
    with the many SSReflect and MathComp lemmas that have an injectivity
    premise. Specifying {T : nonPropType} solves this more elegantly, as then
    (?T : Type) no longer unifies with (Some n = Some 0), which has sort Prop.
 **)

Module NonPropType.

(** Implementation notes:
 We rely on three interface Structures:
  - test_of r, the middle structure, performs the actual check: it has two
    canonical instances whose 'condition' projection are maybeProj (?P : Prop)
    and tt, and which set r := true and r := false, respectively. Unifying
    condition (?t : test_of ?r) with maybeProj T will thus set ?r to true if
    T is in Prop as the test_Prop T instance will apply, and otherwise simplify
    maybeProp T to tt and use the test_negative instance and set ?r to false.
  - call_of c r sets up a call to test_of on condition c with expected result r.
    It has a default instance for its 'callee' projection to Type, which
    sets c := maybeProj T and r := false when unifying with a type T.
  - type is a telescope on call_of c r, which checks that unifying test_of ?r1
    with c indeed sets ?r1 := r; the type structure bundles the 'test' instance
    and its 'result' value along with its call_of c r projection. The default
    instance essentially provides eta-expansion for 'type'. This is only
    essential for the first 'result' projection to bool; using the instance
    for other projection merely avoids spurious delta expansions that would
    spoil the notProp T notation.
 In detail, unifying T =~= ?S with ?S : nonPropType, i.e.,
  (1)  T =~= @callee (@condition (result ?S) (test ?S)) (result ?S) (frame ?S)
 first uses the default call instance with ?T := T to reduce (1) to
  (2a) @condition (result ?S) (test ?S) =~= maybeProp T
  (3)                         result ?S =~= false
  (4)                          frame ?S =~= call T
 along with some trivial universe-related checks which are irrelevant here.
   Then the unification tries to use the test_Prop instance to reduce (2a) to
  (6a)                        result ?S =~= true
  (7a)                               ?P =~= T with ?P : Prop
  (8a)                          test ?S =~= test_Prop ?P
 Now the default 'check' instance with ?result := true resolves (6a) as
  (9a)                               ?S := @check true ?test ?frame
 Then (7a) can be solved precisely if T has sort at most (hence exactly) Prop,
 and then (8a) is solved by the check instance, yielding ?test := test_Prop T,
 and completing the solution of (2a), and _committing_ to it. But now (3) is
 inconsistent with (9a), and this makes the entire problem (1) fails.
   If on the othe hand T does not have sort Prop then (7a) fails and the
 unification resorts to delta expanding (2a), which gives
  (2b) @condition (result ?S) (test ?S) =~= tt
 which is then reduced, using the test_negative instance, to
  (6b)                        result ?S =~= false
  (8b)                          test ?S =~= test_negative
 Both are solved using the check default instance, as in the (2a) branch, giving
  (9b)                               ?S := @check false test_negative ?frame
 Then (3) and (4) are similarly soved using check, giving the final assignment
  (9)                                ?S := notProp T
 Observe that we _must_ perform the actual test unification on the arguments
 of the initial canonical instance, and not on the instance itself as we do
 in mathcomp/matrix and mathcomp/vector, because we want the unification to
 fail when T has sort Prop. If both the test_of _and_ the result check
 unifications were done as part of the structure telescope then the latter
 would be a sub-problem of the former, and thus failing the check would merely
 make the test_of unification backtrack and delta-expand and we would not get
 failure.
 **)

Structure call_of (condition : unit) (result : bool) := Call {callee : Type}.
Definition maybeProp (T : Type) := tt.
Definition call T := Call (maybeProp T) false T.

Structure test_of (result : bool) := Test {condition :> unit}.
Definition test_Prop (P : Prop) := Test true (maybeProp P).
Definition test_negative := Test false tt.

Structure type :=
  Check {result : bool; test : test_of result; frame : call_of test result}.
Definition check result test frame := @Check result test frame.

Module Exports.
Canonical call.
Canonical test_Prop.
Canonical test_negative.
Canonical check.
Notation nonPropType := type.
Coercion callee : call_of >-> Sortclass.
Coercion frame : type >-> call_of.
Notation notProp T := (@check false test_negative (call T)).
End Exports.

End NonPropType.
Export NonPropType.Exports.
