(******************************************************************************)
(* State.v — Local process state for one broadcast instance                  *)
(*                                                                            *)
(* Mirrors the Rust ProcessState struct.                                      *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition ProcessId := nat.
Definition Value := nat.

(** The local state of one process for one broadcast instance.
    We use option for echo_sent/ready_sent/delivered (set-once semantics).
    Sender sets are lists of ProcessId (deduplicated by the transition). *)
Record ProcessState : Type := mkPS {
  echo_sent     : option Value;
  ready_sent    : option Value;
  delivered     : option Value;
  echo_senders  : Value -> list ProcessId;
  ready_senders : Value -> list ProcessId
}.

(** Counts. *)
Definition echo_count (s : ProcessState) (v : Value) : nat :=
  length (echo_senders s v).

Definition ready_count (s : ProcessState) (v : Value) : nat :=
  length (ready_senders s v).

(** Initial state. *)
Definition init_state : ProcessState := {|
  echo_sent     := None;
  ready_sent    := None;
  delivered     := None;
  echo_senders  := fun _ => nil;
  ready_senders := fun _ => nil
|}.

(** Global state: one ProcessState per process.
    Message history is tracked in Transitions.v which imports Messages.v. *)
Record GlobalState : Type := mkGS {
  local_state : ProcessId -> ProcessState
}.

(** Predicates on global state. *)
Definition EchoSent (gs : GlobalState) (p : ProcessId) (v : Value) : Prop :=
  echo_sent (local_state gs p) = Some v.

Definition ReadySent (gs : GlobalState) (p : ProcessId) (v : Value) : Prop :=
  ready_sent (local_state gs p) = Some v.

Definition Delivered (gs : GlobalState) (p : ProcessId) (v : Value) : Prop :=
  delivered (local_state gs p) = Some v.
