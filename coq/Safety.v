(*******************************************************************************)
(* Safety.v — Safety theorems for Bracha Reliable Broadcast                  *)
(*                                                                             *)
(* FULLY PROVED — zero Admitted (Liveness.v still carries admitted liveness). *)
(*                                                                             *)
(* Proved without any Admitted:                                                *)
(*   1. Echo Integrity     — option monotonicity (snapshot)                   *)
(*   2. READY Integrity    — option monotonicity (snapshot)                   *)
(*   3. Delivery Integrity — option monotonicity (snapshot)                   *)
(*   4. No Conflicting READY                                                   *)
(*      Requires: echo-quorum witnesses, quorum intersection (Quorums.v),    *)
(*                echo_integrity (above).                                     *)
(*   5. Agreement                                                               *)
(*      Requires: READY-quorum witnesses, no_conflicting_ready (above).      *)
(*******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import State.
Require Import Quorums.

(** ═══════════════════════════════════════════════════════════════════════════
    Helper: option injectivity.
    ═══════════════════════════════════════════════════════════════════════════ *)

Lemma option_some_inj : forall {A : Type} (a b : A),
  Some a = Some b -> a = b.
Proof.
  intros A a b H. injection H. auto.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Theorem 1 — Echo Integrity

    A correct process echoes at most one value per instance.
    Proof: echo_sent is a set-once option field; two Some values must agree.
    ═══════════════════════════════════════════════════════════════════════════ *)

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

(** ═══════════════════════════════════════════════════════════════════════════
    Theorem 2 — READY Integrity

    A correct process broadcasts READY for at most one value per instance.
    ═══════════════════════════════════════════════════════════════════════════ *)

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

(** ═══════════════════════════════════════════════════════════════════════════
    Theorem 3 — Delivery Integrity

    A correct process delivers at most one value per instance.
    ═══════════════════════════════════════════════════════════════════════════ *)

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

(** ═══════════════════════════════════════════════════════════════════════════
    Section SafetyWithWitnesses

    Theorems 4 and 5 require reasoning about why ReadySent / Delivered came
    to hold — i.e., which processes triggered the state transitions.  We
    capture this via explicit witness hypotheses:

    echo_justified
      For every correct process p that sent READY for v there exists a list Q
      of >= n-f process IDs, all within the universe, all of which echoed v.
      (This is what Exec.echo_quorum_invariant proves for a concrete trace.)

    delivery_has_ready_quorum
      For every correct process p that delivered v there exists a list of
      >= n-f pids, all of whose correct members sent READY for v.

    These hypotheses are satisfiable by any reachable global state; they
    encode the connection between the snapshot model (GlobalState) and the
    operational transition model (Transitions.reachable).
    ═══════════════════════════════════════════════════════════════════════════ *)

Section SafetyWithWitnesses.

Variable n f : nat.
Hypothesis Hbound : n > 3 * f.

Variable gs : GlobalState.

Variable faulty_list : list ProcessId.
Variable universe    : list ProcessId.

Hypothesis universe_size       : length universe = n.
Hypothesis universe_NoDup      : NoDup universe.
Hypothesis faulty_NoDup        : NoDup faulty_list.
Hypothesis faulty_bound        : length faulty_list <= f.
Hypothesis faulty_in_universe  : forall p, In p faulty_list -> In p universe.

Definition correct_S (p : ProcessId) : Prop := ~ In p faulty_list.

(** echo_justified:
    For every correct process p with ReadySent gs p v, there is an echo
    quorum Q — a list of n-f pids, all in the universe, all of whose
    *correct* members have EchoSent gs q v.  Byzantine members need not
    have echoed anything. *)
Hypothesis echo_justified :
  forall (p : ProcessId) (v : Value),
    correct_S p ->
    ReadySent gs p v ->
    exists Q : list ProcessId,
      length Q >= n - f /\
      NoDup Q /\
      (forall q, In q Q -> In q universe) /\
      (forall q, In q Q -> correct_S q -> EchoSent gs q v).

(** delivery_has_ready_quorum:
    For every correct process p with Delivered gs p v, there exists a list R
    of n-f pids all of whose correct members sent READY for v. *)
Hypothesis delivery_has_ready_quorum :
  forall (p : ProcessId) (v : Value),
    correct_S p ->
    Delivered gs p v ->
    exists R : list ProcessId,
      length R >= n - f /\
      NoDup R /\
      (forall r, In r R -> correct_S r -> ReadySent gs r v).

(** ═══════════════════════════════════════════════════════════════════════════
    Theorem 4 — No Conflicting READY

    Two correct processes cannot send READY for different values.

    Proof:
      By echo_justified, each correct READY sender has an echo quorum.
      By quorum_intersection_has_correct, the two echo quorums share a
      correct process c.
      c echoed both v and w.
      By echo_integrity, v = w.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem no_conflicting_ready :
  forall (p_id q_id : ProcessId) (v w : Value),
    correct_S p_id ->
    correct_S q_id ->
    ReadySent gs p_id v ->
    ReadySent gs q_id w ->
    v = w.
Proof.
  intros p_id q_id v w Hcp Hcq Hv Hw.

  (* Obtain echo quorums for v and w *)
  destruct (echo_justified p_id v Hcp Hv) as [Qv [HlQv [HnQv [HuQv HeQv]]]].
  destruct (echo_justified q_id w Hcq Hw) as [Qw [HlQw [HnQw [HuQw HeQw]]]].

  (* Find a correct process c in the intersection of the two quorums *)
  destruct (quorum_intersection_has_correct n f Hbound
              universe Qv Qw faulty_list
              universe_NoDup HnQv HnQw faulty_NoDup
              universe_size HuQv HuQw faulty_in_universe
              HlQv HlQw faulty_bound)
    as [c [HcI Hc_correct]].

  (* c is in both Qv and Qw, so it echoed v and w *)
  apply in_list_inter in HcI. destruct HcI as [HcQv HcQw].

  (* By echo_integrity, v = w *)
  apply echo_integrity with (gs := gs) (p := c).
  - exact (HeQv c HcQv Hc_correct).
  - exact (HeQw c HcQw Hc_correct).
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Theorem 5 — Agreement

    If two correct processes deliver, they deliver the same value.

    Proof:
      Delivery of v requires n-f READYs.  Since n-f > f >= |faulty_list|,
      the delivery quorum contains at least one correct READY sender c1 for v.
      Similarly, q's delivery contains correct c2 that sent READY for w.
      By no_conflicting_ready, v = w.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem agreement :
  forall (p_id q_id : ProcessId) (v w : Value),
    correct_S p_id ->
    correct_S q_id ->
    Delivered gs p_id v ->
    Delivered gs q_id w ->
    v = w.
Proof.
  intros p_id q_id v w Hcp Hcq Hv Hw.

  (* Get delivery quorums *)
  destruct (delivery_has_ready_quorum p_id v Hcp Hv) as [R [HlR [HnR HrR]]].
  destruct (delivery_has_ready_quorum q_id w Hcq Hw) as [R' [HlR' [HnR' HrR']]].

  (* By pigeonhole: each delivery quorum contains a correct pid.
     |faulty_list| <= f < n-f <= |R| *)
  assert (Hlt1 : length faulty_list < length R) by lia.
  assert (Hlt2 : length faulty_list < length R') by lia.

  destruct (longer_NoDup_has_element_not_in R faulty_list HnR Hlt1)
    as [c1 [Hc1R Hc1_correct]].
  destruct (longer_NoDup_has_element_not_in R' faulty_list HnR' Hlt2)
    as [c2 [Hc2R' Hc2_correct]].

  (* c1 sent READY(v), c2 sent READY(w), both correct *)
  assert (Hc1v : ReadySent gs c1 v) by (exact (HrR c1 Hc1R Hc1_correct)).
  assert (Hc2w : ReadySent gs c2 w) by (exact (HrR' c2 Hc2R' Hc2_correct)).

  (* By no_conflicting_ready, v = w *)
  exact (no_conflicting_ready c1 c2 v w Hc1_correct Hc2_correct Hc1v Hc2w).
Qed.

End SafetyWithWitnesses.
