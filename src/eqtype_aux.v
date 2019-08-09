(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Ltac2.

(** When [p] is a projector of some record type [r],
then [dual p] is a constructor of [r]. *)

Ltac2 dual p :=
  let rec find typ :=
      Message.print (Message.of_constr typ);
      let kind := Constr.Unsafe.kind typ in
      match kind with
      | Constr.Unsafe.Ind ι u =>
        let naked := Constr.Unsafe.constructor ι 0 in
        let k := Constr.Unsafe.make (Constr.Unsafe.Constructor naked u) in
        Message.print (Message.of_string "Fini: ");
        Message.print (Message.of_constr k);
        k
      | Constr.Unsafe.Prod _ a _ => find a
      | Constr.Unsafe.App f a =>
        let res := Constr.Unsafe.make (Constr.Unsafe.App (find f) a) in
        Message.print (Message.of_string "Reconstruit: ");
        Message.print (Message.of_constr res);
        res
      | _ =>
        Message.print (Message.of_string "fail");
        p
      end
  in find (Constr.type p).
