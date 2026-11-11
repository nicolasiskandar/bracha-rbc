(******************************************************************************)
(* Messages.v — Protocol message types                                       *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition ProcessId := nat.
Definition Value := nat.

(** The three protocol message types. *)
Inductive MessageKind : Type :=
  | INIT  : MessageKind
  | ECHO  : MessageKind
  | READY : MessageKind.

(** Decidable equality for MessageKind. *)
Lemma messagekind_eq_dec : forall (a b : MessageKind), {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** A protocol message. *)
Record Message : Type := mkMessage {
  msg_kind   : MessageKind;
  msg_value  : Value;
  msg_sender : ProcessId;
  msg_inst   : nat
}.
