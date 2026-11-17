(*******************************************************************************)
(* Operational.v — Safety of the small-step model                              *)
(*                                                                             *)
(* Proves that every state reachable by Transitions.step satisfies the         *)
(* witness hypotheses of Safety.SafetyWithWitnesses, yielding end-to-end        *)
(* no_conflicting_ready and agreement over reachable global states.             *)
(*                                                                             *)
(* FULLY PROVED — zero Admitted.                                                *)
(*******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import State.
Require Import Quorums.
Require Import Transitions.
Require Import Safety.

Section Operational.

Variable n f : nat.
Hypothesis Hbound : n > 3 * f.
Variable broadcaster : ProcessId.

Variable universe : list ProcessId.
Hypothesis universe_NoDup : NoDup universe.
Hypothesis universe_size : length universe = n.

Variable faulty_list : list ProcessId.
Hypothesis faulty_NoDup : NoDup faulty_list.
Hypothesis faulty_bound : length faulty_list <= f.
Hypothesis faulty_in_universe : forall p, In p faulty_list -> In p universe.

(** Section parameters of Transitions.step / reachable, fixed here. *)
Local Notation step := (Transitions.step n f broadcaster universe faulty_list).
Local Notation reachable := (Transitions.reachable n f broadcaster universe faulty_list).

(** ═══════════════════════════════════════════════════════════════════════════
    Helper lemmas for update_local.
    ═══════════════════════════════════════════════════════════════════════════ *)

Lemma update_local_same : forall (gs : GlobalState) (p : ProcessId) (ps : ProcessState),
  local_state (update_local gs p ps) p = ps.
Proof.
  intros gs p ps. unfold update_local. simpl.
  destruct (Nat.eqb p p) eqn:E.
  - reflexivity.
  - rewrite Nat.eqb_refl in E. discriminate E.
Qed.

Lemma update_local_other : forall (gs : GlobalState) (p q : ProcessId) (ps : ProcessState),
  q <> p -> local_state (update_local gs p ps) q = local_state gs q.
Proof.
  intros gs p q ps Hne. unfold update_local. simpl.
  destruct (Nat.eqb q p) eqn:E.
  - exfalso. apply Hne. apply Nat.eqb_eq in E. exact E.
  - reflexivity.
Qed.

(** If an update preserves the echo_sent field, it preserves EchoSent facts. *)
Lemma echo_sent_preserved_update :
  forall (gs : GlobalState) (ps : ProcessState) (q : ProcessId)
         (p : ProcessId) (v : Value),
    echo_sent (local_state gs p) = Some v ->
    echo_sent ps = echo_sent (local_state gs q) ->
    echo_sent (if Nat.eqb p q then ps else local_state gs p) = Some v.
Proof.
  intros gs ps q p v Hsent Hfield.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p. rewrite Hfield. exact Hsent.
  - exact Hsent.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Stability of the set-once fields under one step.
    ═══════════════════════════════════════════════════════════════════════════ *)

Lemma echo_sent_step_stable :
  forall (gs : GlobalState) (ev : Transitions.Event) (gs' : GlobalState) (p : ProcessId) (v : Value),
    step gs ev gs' -> EchoSent gs p v -> EchoSent gs' p v.
Proof.
  intros gs ev gs' p v Hstep Hsent.
  inversion Hstep; subst; unfold EchoSent in *; simpl in *.

  - (* recv_init *)
    destruct (Nat.eqb p receiver) eqn:E.
    + apply Nat.eqb_eq in E. subst p. rewrite H1 in Hsent. discriminate.
    + exact Hsent.

  - refine (echo_sent_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_echo *)
  - refine (echo_sent_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_ready *)
  - refine (echo_sent_preserved_update gs _ p0 p v Hsent _). reflexivity.        (* send_ready_echo *)
  - refine (echo_sent_preserved_update gs _ p0 p v Hsent _). reflexivity.        (* send_ready_amplify *)
  - refine (echo_sent_preserved_update gs _ p0 p v Hsent _). reflexivity.        (* deliver *)
  - exact Hsent.                                                          (* byzantine *)
Qed.

(** Analogous preservation lemmas for ready_sent and delivered. *)
Lemma ready_sent_preserved_update :
  forall (gs : GlobalState) (ps : ProcessState) (q : ProcessId)
         (p : ProcessId) (v : Value),
    ready_sent (local_state gs p) = Some v ->
    ready_sent ps = ready_sent (local_state gs q) ->
    ready_sent (if Nat.eqb p q then ps else local_state gs p) = Some v.
Proof.
  intros gs ps q p v Hsent Hfield.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p. rewrite Hfield. exact Hsent.
  - exact Hsent.
Qed.

Lemma delivered_preserved_update :
  forall (gs : GlobalState) (ps : ProcessState) (q : ProcessId)
         (p : ProcessId) (v : Value),
    delivered (local_state gs p) = Some v ->
    delivered ps = delivered (local_state gs q) ->
    delivered (if Nat.eqb p q then ps else local_state gs p) = Some v.
Proof.
  intros gs ps q p v Hsent Hfield.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p. rewrite Hfield. exact Hsent.
  - exact Hsent.
Qed.

Lemma ready_sent_step_stable :
  forall (gs : GlobalState) (ev : Transitions.Event) (gs' : GlobalState) (p : ProcessId) (v : Value),
    step gs ev gs' -> ReadySent gs p v -> ReadySent gs' p v.
Proof.
  intros gs ev gs' p v Hstep Hsent.
  inversion Hstep; subst; unfold ReadySent in *; simpl in *.

  - refine (ready_sent_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_init *)
  - refine (ready_sent_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_echo *)
  - refine (ready_sent_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_ready *)

  - (* send_ready_echo *)
    destruct (Nat.eqb p p0) eqn:E.
    + apply Nat.eqb_eq in E. subst p. rewrite H1 in Hsent. discriminate.
    + exact Hsent.

  - (* send_ready_amplify *)
    destruct (Nat.eqb p p0) eqn:E.
    + apply Nat.eqb_eq in E. subst p. rewrite H1 in Hsent. discriminate.
    + exact Hsent.

  - refine (ready_sent_preserved_update gs _ p0 p v Hsent _). reflexivity.  (* deliver *)
  - exact Hsent.                                                          (* byzantine *)
Qed.

Lemma ready_senders_nodup_update :
  forall (gs : GlobalState) (q : ProcessId) (ps : ProcessState)
         (p : ProcessId) (v : Value),
    NoDup (ready_senders ps v) ->
    NoDup (ready_senders (local_state gs p) v) ->
    NoDup (ready_senders (local_state (update_local gs q ps) p) v).
Proof.
  intros gs q ps p v Hnew Hold.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p. rewrite update_local_same. exact Hnew.
  - rewrite update_local_other by (apply Nat.eqb_neq in E; exact E). exact Hold.
Qed.

(** Generic bridge through update_local for sender-list properties. *)
Lemma echo_senders_nodup_update :
  forall (gs : GlobalState) (q : ProcessId) (ps : ProcessState)
         (p : ProcessId) (v : Value),
    NoDup (echo_senders ps v) ->
    NoDup (echo_senders (local_state gs p) v) ->
    NoDup (echo_senders (local_state (update_local gs q ps) p) v).
Proof.
  intros gs q ps p v Hnew Hold.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p. rewrite update_local_same. exact Hnew.
  - rewrite update_local_other by (apply Nat.eqb_neq in E; exact E). exact Hold.
Qed.

(** If an update leaves the echo_senders field unchanged, membership carries
    back to the previous state. *)
Lemma in_echo_senders_update_unchanged :
  forall (gs : GlobalState) (q : ProcessId) (ps : ProcessState)
         (p : ProcessId) (v : Value) (x : ProcessId),
    echo_senders ps = echo_senders (local_state gs q) ->
    In x (echo_senders (local_state (update_local gs q ps) p) v) ->
    In x (echo_senders (local_state gs p) v).
Proof.
  intros gs q ps p v x Hfield Hin.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p.
    rewrite update_local_same in Hin. rewrite Hfield in Hin. exact Hin.
  - rewrite update_local_other in Hin by (apply Nat.eqb_neq in E; exact E).
    exact Hin.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Sender-set helpers.
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition good_S (p : ProcessId) : Prop := ~ In p faulty_list.

Lemma NoDup_add_sender : forall (p : ProcessId) (l : list ProcessId),
  NoDup l -> NoDup (add_sender p l).
Proof.
  intros p l Hnd. unfold add_sender.
  destruct (existsb (Nat.eqb p) l) eqn:E.
  - exact Hnd.
  - constructor.
    + intro Hin.
      assert (Etrue : existsb (Nat.eqb p) l = true) by
        (apply List.existsb_exists; exists p; split; [exact Hin | apply Nat.eqb_refl]).
      rewrite Etrue in E. discriminate.
    + exact Hnd.
Qed.

Lemma in_add_sender : forall (p x : ProcessId) (l : list ProcessId),
  In x (add_sender p l) -> x = p \/ In x l.
Proof.
  intros p x l Hin. unfold add_sender in Hin.
  destruct (existsb (Nat.eqb p) l) eqn:E.
  - right. exact Hin.
  - simpl in Hin. destruct Hin as [Hxp | Hxl].
    + left. symmetry. exact Hxp.
    + right. exact Hxl.
Qed.

Lemma sender_list_nodup_after_add :
  forall (snd : Value -> list ProcessId) (v v0 : Value) (p : ProcessId),
    (forall w, NoDup (snd w)) ->
    NoDup (if Nat.eqb v v0 then add_sender p (snd v) else snd v).
Proof.
  intros snd v v0 p Hnd.
  destruct (Nat.eqb v v0) eqn:E.
  - apply NoDup_add_sender. apply Hnd.
  - apply Hnd.
Qed.

Lemma echo_senders_nodup_reachable :
  forall gs, reachable gs -> forall p v, NoDup (echo_senders (local_state gs p) v).
Proof.
  intros gs Hreach.
  induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v. simpl. constructor.
  - intros p v.
    inversion Hstep; subst; simpl in *.
    + (* recv_init *)
      refine (echo_senders_nodup_update gs _ _ p v _ (IH p v)).
      apply sender_list_nodup_after_add. intros. apply IH.
    + (* recv_echo *)
      refine (echo_senders_nodup_update gs _ _ p v _ (IH p v)).
      apply sender_list_nodup_after_add. intros. apply IH.
    + (* recv_ready *)
      refine (echo_senders_nodup_update gs _ _ p v _ (IH p v)). apply IH.
    + (* send_ready_echo *)
      refine (echo_senders_nodup_update gs _ _ p v _ (IH p v)). apply IH.
    + (* send_ready_amplify *)
      refine (echo_senders_nodup_update gs _ _ p v _ (IH p v)). apply IH.
    + (* deliver *)
      refine (echo_senders_nodup_update gs _ _ p v _ (IH p v)). apply IH.
    + (* byzantine *) apply IH.
Qed.

Lemma ready_senders_nodup_reachable :
  forall gs, reachable gs -> forall p v, NoDup (ready_senders (local_state gs p) v).
Proof.
  intros gs Hreach.
  induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v. simpl. constructor.
  - intros p v.
    inversion Hstep; subst; simpl in *.
    + refine (ready_senders_nodup_update gs _ _ p v _ (IH p v)). apply IH.
    + refine (ready_senders_nodup_update gs _ _ p v _ (IH p v)). apply IH.
    + refine (ready_senders_nodup_update gs _ _ p v _ (IH p v)).
      apply sender_list_nodup_after_add. intros. apply IH.
    + refine (ready_senders_nodup_update gs _ _ p v _ (IH p v)).
      apply sender_list_nodup_after_add. intros. apply IH.
    + refine (ready_senders_nodup_update gs _ _ p v _ (IH p v)).
      apply sender_list_nodup_after_add. intros. apply IH.
    + refine (ready_senders_nodup_update gs _ _ p v _ (IH p v)). apply IH.
    + apply IH.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Validity of sender lists: a correct process recorded as an ECHO sender
    really did send ECHO for that value.
    ═══════════════════════════════════════════════════════════════════════════ *)

Lemma echo_senders_valid_step :
  forall (gs : GlobalState) (ev : Transitions.Event) (gs' : GlobalState),
    step gs ev gs' ->
    (forall p v x, In x (echo_senders (local_state gs p) v) -> good_S x -> EchoSent gs x v) ->
    forall p v x, In x (echo_senders (local_state gs' p) v) -> good_S x -> EchoSent gs' x v.
Proof.
  intros gs ev gs' Hstep IH p v x Hmem Hgood.
  inversion Hstep.

  + (* recv_init *)
    rewrite <- H4 in Hmem; simpl in Hmem. rewrite H4.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender receiver x _ Hmem) as [Hx | Hx].
        -- subst x. rewrite <- H4. unfold EchoSent. rewrite update_local_same. simpl. reflexivity.
        -- exact (echo_sent_step_stable gs _ gs' x v0 Hstep (IH _ _ _ Hx Hgood)).
      * exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* recv_echo *)
    rewrite <- H5 in Hmem; simpl in Hmem. rewrite H5.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender sender x _ Hmem) as [Hx | Hx].
        -- subst x. exact (echo_sent_step_stable gs _ gs' sender v0 Hstep (H1 Hgood)).
        -- exact (echo_sent_step_stable gs _ gs' x v0 Hstep (IH _ _ _ Hx Hgood)).
      * exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* recv_ready *)
    rewrite <- H5 in Hmem.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem.
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
  + rewrite <- H5 in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem.
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
  + rewrite <- H5 in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem.
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
  + rewrite <- H5 in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem.
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      rewrite H5.
      exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
  + (* byzantine *)
    rewrite <- H4 in Hmem; simpl in Hmem. rewrite H4.
    exact (echo_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
Qed.

Lemma echo_senders_valid_reachable :
  forall gs, reachable gs ->
    forall p v x, In x (echo_senders (local_state gs p) v) -> good_S x -> EchoSent gs x v.
Proof.
  intros gs Hreach. induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v x Hin. simpl in Hin. contradiction.
  - exact (echo_senders_valid_step gs ev gs' Hstep IH).
Qed.

(** Validity of READY sender lists. *)
Lemma ready_senders_valid_step :
  forall (gs : GlobalState) (ev : Transitions.Event) (gs' : GlobalState),
    step gs ev gs' ->
    (forall p v x, In x (ready_senders (local_state gs p) v) -> good_S x -> ReadySent gs x v) ->
    forall p v x, In x (ready_senders (local_state gs' p) v) -> good_S x -> ReadySent gs' x v.
Proof.
  intros gs ev gs' Hstep IH p v x Hmem Hgood.
  inversion Hstep.

  + (* recv_init *)
    rewrite <- H4 in Hmem. rewrite H4.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem.
      exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* recv_echo *)
    rewrite <- H5 in Hmem. rewrite H5.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem.
      exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* recv_ready: sender is added *)
    rewrite <- H5 in Hmem; simpl in Hmem. rewrite H5.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender sender x _ Hmem) as [Hx | Hx].
        -- subst x. exact (ready_sent_step_stable gs _ gs' sender v0 Hstep (H1 Hgood)).
        -- exact (ready_sent_step_stable gs _ gs' x v0 Hstep (IH _ _ _ Hx Hgood)).
      * exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* send_ready_echo: p is added *)
    rewrite <- H5 in Hmem; simpl in Hmem. rewrite H5.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender p0 x _ Hmem) as [Hx | Hx].
        -- subst x. rewrite <- H5. unfold ReadySent. rewrite update_local_same. simpl. reflexivity.
        -- exact (ready_sent_step_stable gs _ gs' x v0 Hstep (IH _ _ _ Hx Hgood)).
      * exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* send_ready_amplify: p is added *)
    rewrite <- H5 in Hmem; simpl in Hmem. rewrite H5.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender p0 x _ Hmem) as [Hx | Hx].
        -- subst x. rewrite <- H5. unfold ReadySent. rewrite update_local_same. simpl. reflexivity.
        -- exact (ready_sent_step_stable gs _ gs' x v0 Hstep (IH _ _ _ Hx Hgood)).
      * exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* deliver *)
    rewrite <- H5 in Hmem. rewrite H5.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem.
      exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).

  + (* byzantine *)
    rewrite <- H4 in Hmem; simpl in Hmem. rewrite H4.
    exact (ready_sent_step_stable gs _ gs' x v Hstep (IH _ _ _ Hmem Hgood)).
Qed.

Lemma ready_senders_valid_reachable :
  forall gs, reachable gs ->
    forall p v x, In x (ready_senders (local_state gs p) v) -> good_S x -> ReadySent gs x v.
Proof.
  intros gs Hreach. induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v x Hin. simpl in Hin. contradiction.
  - exact (ready_senders_valid_step gs ev gs' Hstep IH).
Qed.

(** Every recorded sender is drawn from the finite universe. *)
Lemma echo_senders_universe_step :
  forall (gs : GlobalState) (ev : Transitions.Event) (gs' : GlobalState),
    step gs ev gs' ->
    (forall p v x, In x (echo_senders (local_state gs p) v) -> In x universe) ->
    forall p v x, In x (echo_senders (local_state gs' p) v) -> In x universe.
Proof.
  intros gs ev gs' Hstep IH p v x Hmem.
  inversion Hstep.

  + (* recv_init *)
    rewrite <- H4 in Hmem; simpl in Hmem.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender receiver x _ Hmem) as [Hx | Hx].
        -- subst x. exact H.
        -- exact (IH _ _ _ Hx).
      * exact (IH _ _ _ Hmem).
    - exact (IH _ _ _ Hmem).

  + (* recv_echo *)
    rewrite <- H5 in Hmem; simpl in Hmem.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender sender x _ Hmem) as [Hx | Hx].
        -- subst x. exact H0.
        -- exact (IH _ _ _ Hx).
      * exact (IH _ _ _ Hmem).
    - exact (IH _ _ _ Hmem).

  + (* recv_ready: echo senders unchanged *)
    rewrite <- H5 in Hmem.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem. exact (IH _ _ _ Hmem).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (IH _ _ _ Hmem).

  + (* send_ready_echo *)
    rewrite <- H5 in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem. exact (IH _ _ _ Hmem).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (IH _ _ _ Hmem).

  + (* send_ready_amplify *)
    rewrite <- H5 in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem. exact (IH _ _ _ Hmem).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (IH _ _ _ Hmem).

  + (* deliver *)
    rewrite <- H5 in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem. exact (IH _ _ _ Hmem).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (IH _ _ _ Hmem).

  + (* byzantine *)
    rewrite <- H4 in Hmem; simpl in Hmem. exact (IH _ _ _ Hmem).
Qed.

Lemma echo_senders_universe_reachable :
  forall gs, reachable gs ->
    forall p v x, In x (echo_senders (local_state gs p) v) -> In x universe.
Proof.
  intros gs Hreach. induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v x Hin. simpl in Hin. contradiction.
  - exact (echo_senders_universe_step gs ev gs' Hstep IH).
Qed.

Lemma ready_senders_universe_step :
  forall (gs : GlobalState) (ev : Transitions.Event) (gs' : GlobalState),
    step gs ev gs' ->
    (forall p v x, In x (ready_senders (local_state gs p) v) -> In x universe) ->
    forall p v x, In x (ready_senders (local_state gs' p) v) -> In x universe.
Proof.
  intros gs ev gs' Hstep IH p v x Hmem.
  inversion Hstep.

  + (* recv_init *)
    rewrite <- H4 in Hmem.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem. exact (IH _ _ _ Hmem).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (IH _ _ _ Hmem).

  + (* recv_echo *)
    rewrite <- H5 in Hmem.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem. exact (IH _ _ _ Hmem).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (IH _ _ _ Hmem).

  + (* recv_ready: sender is added *)
    rewrite <- H5 in Hmem; simpl in Hmem.
    destruct (Nat.eqb p receiver) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender sender x _ Hmem) as [Hx | Hx].
        -- subst x. exact H0.
        -- exact (IH _ _ _ Hx).
      * exact (IH _ _ _ Hmem).
    - exact (IH _ _ _ Hmem).

  + (* send_ready_echo: p is added *)
    rewrite <- H5 in Hmem; simpl in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender p0 x _ Hmem) as [Hx | Hx].
        -- subst x. exact H.
        -- exact (IH _ _ _ Hx).
      * exact (IH _ _ _ Hmem).
    - exact (IH _ _ _ Hmem).

  + (* send_ready_amplify: p is added *)
    rewrite <- H5 in Hmem; simpl in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p. simpl in Hmem.
      destruct (Nat.eqb v v0) eqn:Ev.
      * apply Nat.eqb_eq in Ev. subst v.
        destruct (in_add_sender p0 x _ Hmem) as [Hx | Hx].
        -- subst x. exact H.
        -- exact (IH _ _ _ Hx).
      * exact (IH _ _ _ Hmem).
    - exact (IH _ _ _ Hmem).

  + (* deliver *)
    rewrite <- H5 in Hmem.
    destruct (Nat.eqb p p0) eqn:E.
    - apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hmem. simpl in Hmem. exact (IH _ _ _ Hmem).
    - rewrite update_local_other in Hmem by (apply Nat.eqb_neq in E; exact E).
      exact (IH _ _ _ Hmem).

  + (* byzantine *)
    rewrite <- H4 in Hmem; simpl in Hmem. exact (IH _ _ _ Hmem).
Qed.

Lemma ready_senders_universe_reachable :
  forall gs, reachable gs ->
    forall p v x, In x (ready_senders (local_state gs p) v) -> In x universe.
Proof.
  intros gs Hreach. induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v x Hin. simpl in Hin. contradiction.
  - exact (ready_senders_universe_step gs ev gs' Hstep IH).
Qed.

(** Pull a ReadySent fact back through an update that leaves ready_sent alone. *)
Lemma ready_sent_backward_update :
  forall (gs : GlobalState) (q : ProcessId) (ps : ProcessState)
         (p : ProcessId) (v : Value),
    ready_sent ps = ready_sent (local_state gs q) ->
    ReadySent (update_local gs q ps) p v ->
    ReadySent gs p v.
Proof.
  intros gs q ps p v Hfield Hsent.
  unfold ReadySent in Hsent.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p.
    rewrite update_local_same in Hsent. rewrite Hfield in Hsent. exact Hsent.
  - rewrite update_local_other in Hsent by (apply Nat.eqb_neq in E; exact E).
    exact Hsent.
Qed.

(** Every correct READY sender has an echo quorum, in every reachable state. *)
Lemma ready_has_echo_quorum_reachable :
  forall gs, reachable gs ->
    forall p v, good_S p -> ReadySent gs p v ->
      exists Q : list ProcessId,
        length Q >= n - f /\
        NoDup Q /\
        (forall q, In q Q -> In q universe) /\
        (forall q, In q Q -> good_S q -> EchoSent gs q v).
Proof.
  intros gs Hreach.
  induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v Hcorr Hsent. simpl in Hsent. discriminate.
  - intros p v Hcorr Hsent.
    inversion Hstep.

    + (* recv_init *)
      rewrite H4.
      rewrite <- H4 in Hsent.
      eapply ready_sent_backward_update in Hsent. 2: reflexivity.
      destruct (IH p v Hcorr Hsent) as [Q [HlQ [HnQ [HuQ HeQ]]]].
      exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
      intros q Hq Hqcorr.
      exact (echo_sent_step_stable gs ev gs' q v Hstep (HeQ q Hq Hqcorr)).

    + (* recv_echo *)
      rewrite H5.
      rewrite <- H5 in Hsent.
      eapply ready_sent_backward_update in Hsent. 2: reflexivity.
      destruct (IH p v Hcorr Hsent) as [Q [HlQ [HnQ [HuQ HeQ]]]].
      exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
      intros q Hq Hqcorr.
      exact (echo_sent_step_stable gs ev gs' q v Hstep (HeQ q Hq Hqcorr)).

    + (* recv_ready *)
      rewrite H5.
      rewrite <- H5 in Hsent.
      eapply ready_sent_backward_update in Hsent. 2: reflexivity.
      destruct (IH p v Hcorr Hsent) as [Q [HlQ [HnQ [HuQ HeQ]]]].
      exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
      intros q Hq Hqcorr.
      exact (echo_sent_step_stable gs ev gs' q v Hstep (HeQ q Hq Hqcorr)).

    + (* send_ready_echo: either the new READY, or an older one *)
      rewrite H5.
      rewrite <- H5 in Hsent. unfold ReadySent in Hsent.
      destruct (Nat.eqb p p0) eqn:E.
      2: {
        rewrite update_local_other in Hsent by (apply Nat.eqb_neq in E; exact E).
        destruct (IH p v Hcorr Hsent) as [Q [HlQ [HnQ [HuQ HeQ]]]].
        exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
        intros q Hq Hqcorr.
        exact (echo_sent_step_stable gs ev gs' q v Hstep (HeQ q Hq Hqcorr)).
      }
      apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hsent. simpl in Hsent.
      injection Hsent as Heqv. subst v.
      exists (echo_senders (local_state gs p0) v0).
      split.
      * unfold echo_count, Transitions.q in H2. exact H2.
      * split.
        -- exact (echo_senders_nodup_reachable gs Hreach p0 v0).
        -- split.
           ++ intros q Hq.
              exact (echo_senders_universe_reachable gs Hreach p0 v0 q Hq).
           ++ intros q Hq Hqcorr.
              exact (echo_sent_step_stable gs ev gs' q v0 Hstep
                       (echo_senders_valid_reachable gs Hreach p0 v0 q Hq Hqcorr)).

    + (* send_ready_amplify: find a correct READY sender and reuse its quorum *)
      rewrite H5.
      rewrite <- H5 in Hsent. unfold ReadySent in Hsent.
      destruct (Nat.eqb p p0) eqn:E.
      2: {
        rewrite update_local_other in Hsent by (apply Nat.eqb_neq in E; exact E).
        destruct (IH p v Hcorr Hsent) as [Q [HlQ [HnQ [HuQ HeQ]]]].
        exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
        intros q Hq Hqcorr.
        exact (echo_sent_step_stable gs ev gs' q v Hstep (HeQ q Hq Hqcorr)).
      }
      apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hsent. simpl in Hsent.
      injection Hsent as Heqv. subst v.
      assert (Hlt : length faulty_list < length (ready_senders (local_state gs p0) v0)).
      { unfold ready_count, Transitions.q in H2. lia. }
      destruct (longer_NoDup_has_element_not_in
                  (ready_senders (local_state gs p0) v0) faulty_list
                  (ready_senders_nodup_reachable gs Hreach p0 v0) Hlt)
        as [r [HrIn Hrcorr]].
      assert (Hrready : ReadySent gs r v0) by
        (exact (ready_senders_valid_reachable gs Hreach p0 v0 r HrIn Hrcorr)).
      destruct (IH r v0 Hrcorr Hrready) as [Q [HlQ [HnQ [HuQ HeQ]]]].
      exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
      intros q Hq Hqcorr.
      exact (echo_sent_step_stable gs ev gs' q v0 Hstep (HeQ q Hq Hqcorr)).

    + (* deliver *)
      rewrite H5.
      rewrite <- H5 in Hsent.
      eapply ready_sent_backward_update in Hsent. 2: reflexivity.
      destruct (IH p v Hcorr Hsent) as [Q [HlQ [HnQ [HuQ HeQ]]]].
      exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
      intros q Hq Hqcorr.
      exact (echo_sent_step_stable gs ev gs' q v Hstep (HeQ q Hq Hqcorr)).

    + (* byzantine *)
      rewrite H4.
      rewrite <- H4 in Hsent; simpl in Hsent.
      destruct (IH p v Hcorr Hsent) as [Q [HlQ [HnQ [HuQ HeQ]]]].
      exists Q. split; [exact HlQ | split; [exact HnQ | split; [exact HuQ |]]].
      intros q Hq Hqcorr.
      exact (echo_sent_step_stable gs ev gs' q v Hstep (HeQ q Hq Hqcorr)).
Qed.

(** Pull a Delivered fact back through an update that leaves delivered alone. *)
Lemma delivered_backward_update :
  forall (gs : GlobalState) (q : ProcessId) (ps : ProcessState)
         (p : ProcessId) (v : Value),
    delivered ps = delivered (local_state gs q) ->
    Delivered (update_local gs q ps) p v ->
    Delivered gs p v.
Proof.
  intros gs q ps p v Hfield Hdel.
  unfold Delivered in Hdel.
  destruct (Nat.eqb p q) eqn:E.
  - apply Nat.eqb_eq in E. subst p.
    rewrite update_local_same in Hdel. rewrite Hfield in Hdel. exact Hdel.
  - rewrite update_local_other in Hdel by (apply Nat.eqb_neq in E; exact E).
    exact Hdel.
Qed.

(** Every delivery has a READY quorum, in every reachable state. *)
Lemma delivery_has_ready_quorum_reachable :
  forall gs, reachable gs ->
    forall p v, Delivered gs p v ->
      exists R : list ProcessId,
        length R >= n - f /\
        NoDup R /\
        (forall r, In r R -> good_S r -> ReadySent gs r v).
Proof.
  intros gs Hreach.
  induction Hreach as [| gs ev gs' Hreach IH Hstep].
  - intros p v Hdel. simpl in Hdel. discriminate.
  - intros p v Hdel.
    inversion Hstep.

    + (* recv_init *)
      rewrite H4.
      rewrite <- H4 in Hdel.
      eapply delivered_backward_update in Hdel. 2: reflexivity.
      destruct (IH p v Hdel) as [R [HlR [HnR HrR]]].
      exists R. split; [exact HlR | split; [exact HnR |]].
      intros r Hr Hrc.
      exact (ready_sent_step_stable gs ev gs' r v Hstep (HrR r Hr Hrc)).

    + (* recv_echo *)
      rewrite H5.
      rewrite <- H5 in Hdel.
      eapply delivered_backward_update in Hdel. 2: reflexivity.
      destruct (IH p v Hdel) as [R [HlR [HnR HrR]]].
      exists R. split; [exact HlR | split; [exact HnR |]].
      intros r Hr Hrc.
      exact (ready_sent_step_stable gs ev gs' r v Hstep (HrR r Hr Hrc)).

    + (* recv_ready *)
      rewrite H5.
      rewrite <- H5 in Hdel.
      eapply delivered_backward_update in Hdel. 2: reflexivity.
      destruct (IH p v Hdel) as [R [HlR [HnR HrR]]].
      exists R. split; [exact HlR | split; [exact HnR |]].
      intros r Hr Hrc.
      exact (ready_sent_step_stable gs ev gs' r v Hstep (HrR r Hr Hrc)).

    + (* send_ready_echo *)
      rewrite H5.
      rewrite <- H5 in Hdel.
      eapply delivered_backward_update in Hdel. 2: reflexivity.
      destruct (IH p v Hdel) as [R [HlR [HnR HrR]]].
      exists R. split; [exact HlR | split; [exact HnR |]].
      intros r Hr Hrc.
      exact (ready_sent_step_stable gs ev gs' r v Hstep (HrR r Hr Hrc)).

    + (* send_ready_amplify *)
      rewrite H5.
      rewrite <- H5 in Hdel.
      eapply delivered_backward_update in Hdel. 2: reflexivity.
      destruct (IH p v Hdel) as [R [HlR [HnR HrR]]].
      exists R. split; [exact HlR | split; [exact HnR |]].
      intros r Hr Hrc.
      exact (ready_sent_step_stable gs ev gs' r v Hstep (HrR r Hr Hrc)).

    + (* deliver: the new DELIVER has a READY quorum *)
      rewrite H5.
      rewrite <- H5 in Hdel. unfold Delivered in Hdel.
      destruct (Nat.eqb p p0) eqn:E.
      2: {
        rewrite update_local_other in Hdel by (apply Nat.eqb_neq in E; exact E).
        destruct (IH p v Hdel) as [R [HlR [HnR HrR]]].
        exists R. split; [exact HlR | split; [exact HnR |]].
        intros r Hr Hrc.
        exact (ready_sent_step_stable gs ev gs' r v Hstep (HrR r Hr Hrc)).
      }
      apply Nat.eqb_eq in E. subst p.
      rewrite update_local_same in Hdel. simpl in Hdel.
      injection Hdel as Heqv. subst v.
      exists (ready_senders (local_state gs p0) v0).
      split.
      * unfold ready_count, Transitions.q in H2. exact H2.
      * split.
        -- exact (ready_senders_nodup_reachable gs Hreach p0 v0).
        -- intros r Hr Hrc.
           exact (ready_sent_step_stable gs ev gs' r v0 Hstep
                    (ready_senders_valid_reachable gs Hreach p0 v0 r Hr Hrc)).

    + (* byzantine *)
      rewrite H4.
      rewrite <- H4 in Hdel; simpl in Hdel.
      destruct (IH p v Hdel) as [R [HlR [HnR HrR]]].
      exists R. split; [exact HlR | split; [exact HnR |]].
      intros r Hr Hrc.
      exact (ready_sent_step_stable gs ev gs' r v Hstep (HrR r Hr Hrc)).
Qed.

Lemma delivered_step_stable :
  forall (gs : GlobalState) (ev : Transitions.Event) (gs' : GlobalState) (p : ProcessId) (v : Value),
    step gs ev gs' -> Delivered gs p v -> Delivered gs' p v.
Proof.
  intros gs ev gs' p v Hstep Hsent.
  inversion Hstep; subst; unfold Delivered in *; simpl in *.

  - refine (delivered_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_init *)
  - refine (delivered_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_echo *)
  - refine (delivered_preserved_update gs _ receiver p v Hsent _). reflexivity.  (* recv_ready *)
  - refine (delivered_preserved_update gs _ p0 p v Hsent _). reflexivity.        (* send_ready_echo *)
  - refine (delivered_preserved_update gs _ p0 p v Hsent _). reflexivity.        (* send_ready_amplify *)

  - (* deliver *)
    destruct (Nat.eqb p p0) eqn:E.
    + apply Nat.eqb_eq in E. subst p. rewrite H1 in Hsent. discriminate.
    + exact Hsent.

  - exact Hsent.                                                          (* byzantine *)
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    End-to-end safety theorems over reachable states.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem no_conflicting_ready_reachable :
  forall gs, reachable gs ->
    forall p q : ProcessId, forall v w : Value,
      good_S p -> good_S q ->
      ReadySent gs p v -> ReadySent gs q w ->
      v = w.
Proof.
  intros gs Hreach p q v w Hp Hq Hv Hw.
  exact (@Safety.no_conflicting_ready n f Hbound gs faulty_list universe
           universe_size universe_NoDup faulty_NoDup faulty_bound
           faulty_in_universe
           (ready_has_echo_quorum_reachable gs Hreach)
           p q v w Hp Hq Hv Hw).
Qed.

Theorem agreement_reachable :
  forall gs, reachable gs ->
    forall p q : ProcessId, forall v w : Value,
      good_S p -> good_S q ->
      Delivered gs p v -> Delivered gs q w ->
      v = w.
Proof.
  intros gs Hreach p q v w Hp Hq Hv Hw.
  exact (@Safety.agreement n f Hbound gs faulty_list universe
           universe_size universe_NoDup faulty_NoDup faulty_bound
           faulty_in_universe
           (ready_has_echo_quorum_reachable gs Hreach)
           (fun p v _ Hdel => delivery_has_ready_quorum_reachable gs Hreach p v Hdel)
           p q v w Hp Hq Hv Hw).
Qed.

End Operational.
