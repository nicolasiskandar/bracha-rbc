(******************************************************************************)
(* Transitions.v — Protocol transition relation                              *)
(*                                                                            *)
(* Small-step relation: step gs ev gs'                                        *)
(* Correct processes follow protocol rules.                                   *)
(* Byzantine processes can inject arbitrary messages under their own ID.      *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition ProcessId := nat.
Definition Value := nat.

Require Import State.

(** Protocol events. *)
Inductive Event : Type :=
  | Ev_recv_init  (receiver sender : ProcessId) (v : Value) (inst : nat)
  | Ev_recv_echo  (receiver sender : ProcessId) (v : Value) (inst : nat)
  | Ev_recv_ready (receiver sender : ProcessId) (v : Value) (inst : nat)
  | Ev_send_ready (p : ProcessId) (v : Value) (inst : nat)
  | Ev_deliver    (p : ProcessId) (v : Value) (inst : nat)
  | Ev_byzantine  (p : ProcessId) (m : Message).

(** Helper: add p to a list if not already present. *)
Definition add_sender (p : ProcessId) (senders : list ProcessId) : list ProcessId :=
  if existsb (Nat.eqb p) senders then senders else p :: senders.

(** Update local state of one process. *)
Definition update_local (gs : GlobalState) (p : ProcessId)
                        (new_ps : ProcessState) : GlobalState :=
  mkGS (fun q => if Nat.eqb q p then new_ps else local_state gs q)
       (history gs).

(** Parameters for transition rules. *)
Section Transitions.

Variable n f : nat.
Variable broadcaster : ProcessId.
Variable faulty : ProcessId -> Prop.
Definition correct (p : ProcessId) : Prop := ~ faulty p.
Definition q := n - f.

(** The transition relation. *)
Inductive step : GlobalState -> Event -> GlobalState -> Prop :=

  (** Rule 1: Receive INIT from broadcaster → send ECHO. *)
  | step_recv_init :
      forall gs receiver v inst,
        correct receiver ->
        echo_sent (local_state gs receiver) = None ->
        step gs
             (Ev_recv_init receiver broadcaster v inst)
             (update_local gs receiver
               (mkPS (Some v)
                     (ready_sent (local_state gs receiver))
                     (delivered (local_state gs receiver))
                     (fun w => if Nat.eqb w v
                               then add_sender receiver (echo_senders (local_state gs receiver) w)
                               else echo_senders (local_state gs receiver) w)
                     (ready_senders (local_state gs receiver))))

  (** Receive ECHO: record sender. *)
  | step_recv_echo :
      forall gs receiver sender v inst,
        correct receiver ->
        step gs
             (Ev_recv_echo receiver sender v inst)
             (update_local gs receiver
               (mkPS (echo_sent (local_state gs receiver))
                     (ready_sent (local_state gs receiver))
                     (delivered (local_state gs receiver))
                     (fun w => if Nat.eqb w v
                               then add_sender sender (echo_senders (local_state gs receiver) w)
                               else echo_senders (local_state gs receiver) w)
                     (ready_senders (local_state gs receiver))))

  (** Receive READY: record sender. *)
  | step_recv_ready :
      forall gs receiver sender v inst,
        correct receiver ->
        step gs
             (Ev_recv_ready receiver sender v inst)
             (update_local gs receiver
               (mkPS (echo_sent (local_state gs receiver))
                     (ready_sent (local_state gs receiver))
                     (delivered (local_state gs receiver))
                     (echo_senders (local_state gs receiver))
                     (fun w => if Nat.eqb w v
                               then add_sender sender (ready_senders (local_state gs receiver) w)
                               else ready_senders (local_state gs receiver) w)))

  (** Rule 2a: n-f ECHOs received → send READY. *)
  | step_send_ready_echo :
      forall gs p v inst,
        correct p ->
        ready_sent (local_state gs p) = None ->
        echo_count (local_state gs p) v >= q ->
        step gs
             (Ev_send_ready p v inst)
             (update_local gs p
               (mkPS (echo_sent (local_state gs p))
                     (Some v)
                     (delivered (local_state gs p))
                     (echo_senders (local_state gs p))
                     (fun w => if Nat.eqb w v
                               then add_sender p (ready_senders (local_state gs p) w)
                               else ready_senders (local_state gs p) w)))

  (** Rule 2b: f+1 READYs received → amplify READY. *)
  | step_send_ready_amplify :
      forall gs p v inst,
        correct p ->
        ready_sent (local_state gs p) = None ->
        ready_count (local_state gs p) v >= f + 1 ->
        step gs
             (Ev_send_ready p v inst)
             (update_local gs p
               (mkPS (echo_sent (local_state gs p))
                     (Some v)
                     (delivered (local_state gs p))
                     (echo_senders (local_state gs p))
                     (fun w => if Nat.eqb w v
                               then add_sender p (ready_senders (local_state gs p) w)
                               else ready_senders (local_state gs p) w)))

  (** Rule 3: n-f READYs received → deliver. *)
  | step_deliver :
      forall gs p v inst,
        correct p ->
        delivered (local_state gs p) = None ->
        ready_count (local_state gs p) v >= q ->
        step gs
             (Ev_deliver p v inst)
             (update_local gs p
               (mkPS (echo_sent (local_state gs p))
                     (ready_sent (local_state gs p))
                     (Some v)
                     (echo_senders (local_state gs p))
                     (ready_senders (local_state gs p))))

  (** Byzantine: inject arbitrary message under own identity. *)
  | step_byzantine :
      forall gs p m,
        faulty p ->
        msg_sender m = p ->
        step gs (Ev_byzantine p m) (mkGS (local_state gs) (m :: history gs)).

(** Reachable states. *)
Definition init_gs : GlobalState := mkGS (fun _ => init_state) nil.

Inductive reachable : GlobalState -> Prop :=
  | reach_init : reachable init_gs
  | reach_step : forall gs ev gs',
      reachable gs -> step gs ev gs' -> reachable gs'.

End Transitions.
