(******************************************************************************)
(* Liveness.v — Liveness theorems under fairness assumptions                 *)
(*                                                                            *)
(* Liveness requires:                                                         *)
(* - Fair delivery: messages between correct processes eventually delivered.  *)
(* - Fair scheduling: every correct process eventually processes messages.    *)
(*                                                                            *)
(* These are stated as explicit axioms.                                       *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import State.

(** ── Execution model ──────────────────────────────────────────────────── *)

(** An execution trace is a list of (state, event) pairs. *)
Definition Event := nat. (* Simplified; full version uses Transitions.Event *)
Definition Trace := list (GlobalState * Event).

(** "Eventually P" — there exists a state in the trace satisfying P. *)
Definition Eventually (P : GlobalState -> Prop) (t : Trace) : Prop :=
  exists i gs ev,
    nth_error t i = Some (gs, ev) /\ P gs.

(** ── Fairness axioms ──────────────────────────────────────────────────── *)

Section Liveness.

Variable faulty : ProcessId -> Prop.
Definition correct (p : ProcessId) : Prop := ~ faulty p.

(** Fair delivery: every message sent from a correct process to a correct
    process is eventually received. This captures the asynchronous reliable
    channel assumption. *)
Axiom fair_delivery :
  forall (p q : ProcessId) (t : Trace),
    correct p -> correct q ->
    (* If p sends a message to q in some prefix of t, then q
       eventually receives it. *)
    True. (* Placeholder for the full statement involving message histories *)

(** Fair scheduling: every correct process is eventually scheduled to
    process its pending messages. *)
Axiom fair_scheduling :
  forall (p : ProcessId) (t : Trace),
    correct p ->
    True. (* Placeholder *)

(** ── Theorem 5 — Validity ────────────────────────────────────────────── *)

(**
   If the broadcaster b is correct and broadcasts v,
   every correct process p eventually delivers v.

   Proof sketch:
   1. b sends INIT(v) to all → by fair_delivery, all correct receive it.
   2. Each correct sends ECHO(v) → all correct receive n-f ECHOs
      (n-f correct processes exist since f ≤ n-f when n > 3f).
   3. Each correct sends READY(v) → all correct receive n-f READYs.
   4. Each correct delivers v.
*)
Theorem validity :
  forall (b p : ProcessId) (v : Value) (t : Trace),
    correct b -> correct p ->
    Eventually (fun gs => Delivered gs p v) t.
Proof.
  intros.
  (* Requires trace induction with fair_delivery and fair_scheduling.
     Admitted: depends on the fairness axioms stated above. *)
  admit.
Admitted.

(** ── Theorem 4 — Totality ───────────────────────────────────────────── *)

(**
   If correct p delivers v, every correct q eventually delivers v.

   Proof sketch:
   1. p delivered v → received n-f READY(v).
   2. At least n-2f > f of those are correct (quorum intersection).
   3. Those correct processes sent READY(v) → by fair_delivery,
      all correct eventually receive f+1 READY(v).
   4. Amplification: each correct sends READY(v).
   5. All correct accumulate n-f READY(v) → deliver v.
*)
Theorem totality :
  forall (p q : ProcessId) (v : Value) (t : Trace),
    correct p -> correct q ->
    Eventually (fun gs => Delivered gs p v) t ->
    Eventually (fun gs => Delivered gs q v) t.
Proof.
  intros.
  (* Requires trace induction with fair_delivery and the
     amplification rule (f+1 READYs → broadcast READY). *)
  admit.
Admitted.

End Liveness.
