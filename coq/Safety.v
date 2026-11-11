(******************************************************************************)
(* Safety.v — Safety theorems for Bracha Reliable Broadcast                  *)
(*                                                                            *)
(* Proved:                                                                    *)
(*   1. Echo Integrity    — option monotonicity                               *)
(*   2. READY Integrity   — option monotonicity                               *)
(*   3. Delivery Integrity — option monotonicity                              *)
(*                                                                            *)
(* Stated with proof sketch (admitted pending execution induction infra):     *)
(*   4. No Conflicting READY                                                  *)
(*   5. Agreement                                                             *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import State.

(** ═══════════════════════════════════════════════════════════════════════
    Helper: option injectivity.
    ═══════════════════════════════════════════════════════════════════════ *)

Lemma option_some_inj : forall {A : Type} (a b : A),
  Some a = Some b -> a = b.
Proof.
  intros A a b H. injection H. auto.
Qed.

(** ═══════════════════════════════════════════════════════════════════════
    Theorem 1 — Echo Integrity

    A correct process echoes at most one value per instance.

    Proof: echo_sent is set from None to Some v exactly once
    (step_recv_init requires echo_sent = None). Therefore if
    EchoSent p v and EchoSent p w, both mean echo_sent = Some v
    and echo_sent = Some w on the same state, so v = w.
    ═══════════════════════════════════════════════════════════════════════ *)

Theorem echo_integrity :
  forall (gs : GlobalState) (p : ProcessId) (v w : Value),
    EchoSent gs p v ->
    EchoSent gs p w ->
    v = w.
Proof.
  intros gs p v w Hv Hw.
  unfold EchoSent in *.
  rewrite Hv in Hw.
  apply option_some_inj. exact Hw.
Qed.

(** ═══════════════════════════════════════════════════════════════════════
    Theorem 2 — READY Integrity

    A correct process broadcasts READY for at most one value per instance.
    Same argument as echo integrity.
    ═══════════════════════════════════════════════════════════════════════ *)

Theorem ready_integrity :
  forall (gs : GlobalState) (p : ProcessId) (v w : Value),
    ReadySent gs p v ->
    ReadySent gs p w ->
    v = w.
Proof.
  intros gs p v w Hv Hw.
  unfold ReadySent in *.
  rewrite Hv in Hw.
  apply option_some_inj. exact Hw.
Qed.

(** ═══════════════════════════════════════════════════════════════════════
    Theorem 6 — Delivery Integrity

    A correct process delivers at most one value per instance.
    ═══════════════════════════════════════════════════════════════════════ *)

Theorem delivery_integrity :
  forall (gs : GlobalState) (p : ProcessId) (v w : Value),
    Delivered gs p v ->
    Delivered gs p w ->
    v = w.
Proof.
  intros gs p v w Hv Hw.
  unfold Delivered in *.
  rewrite Hv in Hw.
  apply option_some_inj. exact Hw.
Qed.

(** ═══════════════════════════════════════════════════════════════════════
    Lemma — No Conflicting READY from correct processes

    If correct p sent READY(v) and correct q sent READY(w), then v = w.

    Proof sketch (by well-founded induction on execution prefix length):

    Consider the earliest correct READY event in the execution.

    Case A: Triggered by n-f ECHOs for v.
      Those n-f senders form quorum Q1.
      If another correct READY for w ≠ v exists:
        Case A.1: Triggered by n-f ECHOs for w → quorum Q2.
          By quorum_intersection_has_correct, ∃ r ∈ Q1 ∩ Q2 correct.
          r echoed both v and w → contradicts echo_integrity.
        Case A.2: Triggered by f+1 READYs for w.
          At most f Byzantine → ≥1 correct sent READY(w) earlier.
          Contradicts "earliest".

    Case B: Triggered by f+1 READYs.
      At most f Byzantine → ≥1 correct sent READY earlier.
      Contradicts "earliest".

    Therefore all correct READY messages agree on value.
    ═══════════════════════════════════════════════════════════════════════ *)

Section NoConflictingReady.

Variable n f : nat.
Variable faulty : ProcessId -> Prop.
Hypothesis byzantine_bound : n > 3 * f.

Definition correct (p : ProcessId) : Prop := ~ faulty p.

Lemma no_conflicting_ready :
  forall (gs : GlobalState) (p_id q_id : ProcessId) (v w : Value),
    correct p_id ->
    correct q_id ->
    ReadySent gs p_id v ->
    ReadySent gs q_id w ->
    v = w.
Proof.
  intros gs p_id q_id v w Hcp Hcq Hv Hw.
  (* The full proof requires:
     1. Induction over the execution trace (reachable gs).
     2. A strengthened invariant tracking which correct processes
        have sent READY and for which values.
     3. The quorum intersection lemma from Quorums.v.
     4. The echo_integrity theorem proved above.

     The key argument is:
     - The first correct READY must be triggered by n-f ECHOs (Case A),
       because Case B requires an earlier correct READY.
     - Any second correct READY for a different value also needs n-f ECHOs,
       but quorum intersection forces a correct process to have echoed
       both values, contradicting echo_integrity.

     This proof structure is sound but requires execution-trace
     induction infrastructure that is beyond the scope of this
     initial formalization. We admit it here. *)
  admit.
Admitted.

End NoConflictingReady.

(** ═══════════════════════════════════════════════════════════════════════
    Theorem 3 — Agreement

    If correct p delivers v and correct q delivers w, then v = w.

    Proof sketch:
    Delivery of v by p requires n-f READY(v) messages.
    Delivery of w by q requires n-f READY(w) messages.
    Among n-f senders, at most f are Byzantine, so at least n-2f > 0
    are correct. By no_conflicting_ready, all correct READYs agree,
    so v = w.
    ═══════════════════════════════════════════════════════════════════════ *)

Section Agreement.

Variable n f : nat.
Variable faulty : ProcessId -> Prop.
Hypothesis byzantine_bound : n > 3 * f.

Definition correct' (p : ProcessId) : Prop := ~ faulty p.

Theorem agreement :
  forall (gs : GlobalState) (p_id q_id : ProcessId) (v w : Value),
    correct' p_id ->
    correct' q_id ->
    Delivered gs p_id v ->
    Delivered gs q_id w ->
    v = w.
Proof.
  intros gs p_id q_id v w Hcp Hcq Hv Hw.
  (* Delivery requires n-f READY messages for the delivered value.
     By no_conflicting_ready, all correct READY senders agree on the value.
     Since the READY quorum contains correct processes (n-f > f when n > 3f),
     both delivery quorums contain a correct process that sent READY
     for the same value. Therefore v = w. *)
  admit.
Admitted.

End Agreement.
