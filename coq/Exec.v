(*******************************************************************************)
(* Exec.v — Execution trace model and top-level safety theorems                 *)
(*                                                                             *)
(* The trace records READY and DELIVER events in chronological order.  Each     *)
(* event carries its protocol justification (an echo quorum, an f+1 READY      *)
(* amplification set, or a READY quorum for delivery).  We prove:               *)
(*                                                                             *)
(*   echo_quorum_invariant     — every correct READY has an echo quorum         *)
(*   ready_quorum_invariant    — every correct DELIVER has a READY quorum       *)
(*   no_conflicting_ready_top  — two correct READYs agree                       *)
(*   agreement_top             — two correct DELIVERs agree                     *)
(*                                                                             *)
(* FULLY PROVED — no Admitted, and no unproved witness hypotheses.  The only    *)
(* assumptions are the explicit protocol rules encoded in wf_trace and the     *)
(* arithmetic/fault bounds.                                                     *)
(*******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Require Import State.
Require Import Quorums.
Require Import Safety.

Section Exec.

Variable n f : nat.
Hypothesis Hbound : n > 3 * f.

Variable universe : list ProcessId.
Hypothesis universe_NoDup : NoDup universe.
Hypothesis universe_size : length universe = n.

Variable faulty_list : list ProcessId.
Hypothesis faulty_NoDup : NoDup faulty_list.
Hypothesis faulty_bound : length faulty_list <= f.
Hypothesis faulty_in_universe : forall p, In p faulty_list -> In p universe.

(** The snapshot of echoed / ready-sent / delivered facts.  In the operational
    model this is a reachable GlobalState; keeping it as a parameter lets the
    trace proof stay independent of how states evolve. *)
Variable gs : GlobalState.

Definition faulty_E (p : ProcessId) : Prop := In p faulty_list.
Definition correct_E (p : ProcessId) : Prop := ~ faulty_E p.

(** ═══════════════════════════════════════════════════════════════════════════
    Trace model.
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive ExecEv : Type :=
  | ERdy (p : ProcessId) (v : Value)
  | EDel (p : ProcessId) (v : Value).

Definition Trace : Type := list ExecEv.

(** A READY event is justified either by n-f ECHOs for v, or by f+1 earlier
    READY events for v (amplification). *)
Definition wf_revent (prefix : Trace) (p : ProcessId) (v : Value) : Prop :=
  correct_E p /\
  ReadySent gs p v /\
  (
    (exists Q : list ProcessId,
       length Q >= n - f /\
       NoDup Q /\
       (forall q, In q Q -> In q universe) /\
       (forall q, In q Q -> EchoSent gs q v))
    \/
    (exists W : list ProcessId,
       length W >= f + 1 /\
       NoDup W /\
       forall w, In w W -> In (ERdy w v) prefix /\ ReadySent gs w v)
  ).

(** A DELIVER event is justified by a READY quorum. *)
Definition wf_devent (prefix : Trace) (p : ProcessId) (v : Value) : Prop :=
  correct_E p /\
  Delivered gs p v /\
  exists R : list ProcessId,
    length R >= n - f /\
    NoDup R /\
    forall r, In r R -> In (ERdy r v) prefix /\ ReadySent gs r v.

Definition wf_event (prefix : Trace) (e : ExecEv) : Prop :=
  match e with
  | ERdy p v => wf_revent prefix p v
  | EDel p v => wf_devent prefix p v
  end.

Inductive wf_trace : Trace -> Prop :=
  | wf_empty : wf_trace []
  | wf_step : forall (tr : Trace) (e : ExecEv),
      wf_trace tr -> wf_event tr e -> wf_trace (tr ++ [e]).

(** ═══════════════════════════════════════════════════════════════════════════
    Invariant 1: every correct READY event has an echo quorum.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem echo_quorum_invariant :
  forall (tr : Trace),
    wf_trace tr ->
    forall (p : ProcessId) (v : Value),
      In (ERdy p v) tr ->
      correct_E p ->
      exists Q : list ProcessId,
        length Q >= n - f /\
        NoDup Q /\
        (forall q, In q Q -> In q universe) /\
        (forall q, In q Q -> EchoSent gs q v).
Proof.
  intros tr Hwf.
  induction Hwf as [| old_tr ev Hwf_prev IH Hwf_ev].

  - intros p v Hin _. inversion Hin.

  - intros p v Hin Hcorr.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | [Heq | Hbot]].

    + exact (IH p v Hin Hcorr).

    + destruct ev as [pid val | pid val].

      * injection Heq as Hpeq Hveq. subst.
        unfold wf_event, wf_revent in Hwf_ev.
        destruct Hwf_ev as [_ [_ [Htrig | Htrig]]].
        -- destruct Htrig as [Q [HlQ [HnQ [HuQ HeQ]]]].
           exact (ex_intro _ Q (conj HlQ (conj HnQ (conj HuQ HeQ)))).
        -- destruct Htrig as [W [HlW [HnW HwW]]].
           assert (Hlt : length faulty_list < length W) by lia.
           destruct (longer_NoDup_has_element_not_in W faulty_list HnW Hlt)
             as [w [HwW' Hwcorr_w]].
           assert (Hwev : In (ERdy w v) old_tr) by
             (exact (proj1 (HwW w HwW'))).
           exact (IH w v Hwev Hwcorr_w).

      * inversion Heq.

    + inversion Hbot.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Invariant 2: every correct DELIVER event has a READY quorum.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem ready_quorum_invariant :
  forall (tr : Trace),
    wf_trace tr ->
    forall (p : ProcessId) (v : Value),
      In (EDel p v) tr ->
      correct_E p ->
      exists R : list ProcessId,
        length R >= n - f /\
        NoDup R /\
        forall r, In r R -> In (ERdy r v) tr /\ ReadySent gs r v.
Proof.
  intros tr Hwf.
  induction Hwf as [| old_tr ev Hwf_prev IH Hwf_ev].

  - intros p v Hin _. inversion Hin.

  - intros p v Hin Hcorr.
    apply List.in_app_or in Hin.
    destruct Hin as [Hin | [Heq | Hbot]].

    + destruct (IH p v Hin Hcorr) as [R [HlR [HnR HR]]].
      exists R. split; [exact HlR | split; [exact HnR |]].
      intros r Hr. destruct (HR r Hr) as [Hrev Hrs].
      split; [| exact Hrs].
      apply List.in_or_app. left. exact Hrev.

    + destruct ev as [pid val | pid val].
      * inversion Heq.
      * injection Heq as Hpeq Hveq. subst.
        unfold wf_event, wf_devent in Hwf_ev.
        destruct Hwf_ev as [_ [_ [R [HlR [HnR HR]]]]].
        exists R. split; [exact HlR | split; [exact HnR |]].
        intros r Hr. destruct (HR r Hr) as [Hrev Hrs].
        split; [| exact Hrs].
        apply List.in_or_app. left. exact Hrev.

    + inversion Hbot.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Top-level theorem 4: No Conflicting READY (trace form).
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem no_conflicting_ready_top :
  forall (tr : Trace) (p q : ProcessId) (v w : Value),
    wf_trace tr ->
    correct_E p ->
    correct_E q ->
    In (ERdy p v) tr ->
    In (ERdy q w) tr ->
    v = w.
Proof.
  intros tr p q v w Hwf Hcp Hcq Hv Hw.
  destruct (echo_quorum_invariant tr Hwf p v Hv Hcp)
    as [Qv [HlQv [HnQv [HuQv HeQv]]]].
  destruct (echo_quorum_invariant tr Hwf q w Hw Hcq)
    as [Qw [HlQw [HnQw [HuQw HeQw]]]].
  destruct (quorum_intersection_has_correct n f Hbound
              universe Qv Qw faulty_list
              universe_NoDup HnQv HnQw faulty_NoDup
              universe_size HuQv HuQw faulty_in_universe
              HlQv HlQw faulty_bound)
    as [c [HcI Hc_correct]].
  apply in_list_inter in HcI. destruct HcI as [HcQv HcQw].
  exact (echo_integrity gs c v w (HeQv c HcQv) (HeQw c HcQw)).
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Top-level theorem 5: Agreement (trace form).
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem agreement_top :
  forall (tr : Trace) (p q : ProcessId) (v w : Value),
    wf_trace tr ->
    correct_E p ->
    correct_E q ->
    In (EDel p v) tr ->
    In (EDel q w) tr ->
    v = w.
Proof.
  intros tr p q v w Hwf Hcp Hcq Hv Hw.
  destruct (ready_quorum_invariant tr Hwf p v Hv Hcp)
    as [R [HlR [HnR HR]]].
  destruct (ready_quorum_invariant tr Hwf q w Hw Hcq)
    as [R' [HlR' [HnR' HR']]].
  assert (Hlt1 : length faulty_list < length R) by lia.
  assert (Hlt2 : length faulty_list < length R') by lia.
  destruct (longer_NoDup_has_element_not_in R faulty_list HnR Hlt1)
    as [c1 [Hc1R Hc1corr]].
  destruct (longer_NoDup_has_element_not_in R' faulty_list HnR' Hlt2)
    as [c2 [Hc2R Hc2corr]].
  destruct (HR c1 Hc1R) as [Hc1ev Hc1ready].
  destruct (HR' c2 Hc2R) as [Hc2ev Hc2ready].
  exact (no_conflicting_ready_top tr c1 c2 v w Hwf
           Hc1corr Hc2corr Hc1ev Hc2ev).
Qed.

End Exec.
