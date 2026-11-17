(*******************************************************************************)
(* Quorums.v — Quorum intersection lemmas                                     *)
(*                                                                             *)
(* Key result: two quorums of size >= n-f over n processes must share at      *)
(* least n-2f elements. Since n > 3f, n-2f > f, so the intersection           *)
(* cannot consist entirely of Byzantine processes.                              *)
(*                                                                             *)
(* FULLY PROVED — zero Admitted.                                               *)
(*******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition ProcessId := nat.

(** ═══════════════════════════════════════════════════════════════════════════
    General list helper lemmas — no dependency on n, f, or list_inter.
    ═══════════════════════════════════════════════════════════════════════════ *)

Lemma remove_in_length : forall (a : ProcessId) (l : list ProcessId),
  In a l -> length (remove Nat.eq_dec a l) < length l.
Proof.
  intros a l Hin.
  exact (List.remove_length_lt Nat.eq_dec l a Hin).
Qed.

Lemma NoDup_incl_length : forall (l l' : list ProcessId),
  NoDup l ->
  (forall x, In x l -> In x l') ->
  length l <= length l'.
Proof.
  induction l as [| h t IH].
  - intros. simpl. lia.
  - intros l' Hnd Hincl.
    inversion Hnd as [| ? ? Hnih HnDt]; subst.
    assert (Hh : In h l') by (apply Hincl; left; reflexivity).
    assert (Hrm_incl : forall x, In x t -> In x (remove Nat.eq_dec h l')).
    { intros x Hx.
      apply List.in_in_remove with (eq_dec := Nat.eq_dec).
      - intro Heq. subst. exact (Hnih Hx).
      - apply Hincl. right. exact Hx. }
    assert (Hlen_t : length t <= length (remove Nat.eq_dec h l'))
      by (apply IH; assumption).
    assert (Hlt : length (remove Nat.eq_dec h l') < length l')
      by (apply remove_in_length; exact Hh).
    simpl. lia.
Qed.

Lemma not_all_in_exists_not : forall (l l' : list ProcessId),
  ~ (forall x, In x l -> In x l') ->
  exists x, In x l /\ ~ In x l'.
Proof.
  intros l l' Hnall.
  induction l as [| h t IH].
  - exfalso. apply Hnall. intros x Hin. inversion Hin.
  - destruct (List.in_dec Nat.eq_dec h l') as [Hh | Hnh].
    + assert (Hnt : ~ (forall x, In x t -> In x l')).
      { intro Ht. apply Hnall. intros x [Heq | Hx].
        - subst. exact Hh.
        - exact (Ht x Hx). }
      destruct (IH Hnt) as [x [Hxt Hnx]].
      exists x. exact (conj (or_intror Hxt) Hnx).
    + exists h. exact (conj (or_introl eq_refl) Hnh).
Qed.

Lemma longer_NoDup_has_element_not_in : forall (l l' : list ProcessId),
  NoDup l ->
  length l' < length l ->
  exists x, In x l /\ ~ In x l'.
Proof.
  intros l l' Hnd Hlt.
  apply not_all_in_exists_not.
  intro Hincl.
  assert (length l <= length l') by (apply NoDup_incl_length; assumption).
  lia.
Qed.

Lemma NoDup_filter_list : forall (f : ProcessId -> bool) (l : list ProcessId),
  NoDup l -> NoDup (filter f l).
Proof.
  intros f l H.
  induction l as [| h t IH].
  - constructor.
  - inversion H as [| ? ? Hnih HnDt]; subst.
    simpl. destruct (f h) eqn:Hfh.
    + constructor.
      * intro Hhin. apply List.filter_In in Hhin.
        apply Hnih. exact (proj1 Hhin).
      * exact (IH HnDt).
    + exact (IH HnDt).
Qed.

Lemma NoDup_app_disjoint : forall (l m : list ProcessId),
  NoDup l -> NoDup m ->
  (forall x, In x l -> ~ In x m) ->
  NoDup (l ++ m).
Proof.
  induction l as [| h t IH].
  - intros m _ Hm _. exact Hm.
  - intros m Hndl Hndm Hdisj.
    inversion Hndl as [| ? ? Hnih HnDt]; subst.
    simpl. constructor.
    + intro Hhin. apply List.in_app_or in Hhin.
      destruct Hhin as [Hhin | Hhin].
      * exact (Hnih Hhin).
      * exact (Hdisj h (or_introl eq_refl) Hhin).
    + apply IH.
      * exact HnDt.
      * exact Hndm.
      * intros x Hx. apply Hdisj. right. exact Hx.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    list_subtract: elements of l1 not in l2.
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition list_subtract (l1 l2 : list ProcessId) : list ProcessId :=
  filter (fun x => negb (existsb (Nat.eqb x) l2)) l1.

Lemma in_list_subtract : forall (l1 l2 : list ProcessId) (x : ProcessId),
  In x (list_subtract l1 l2) <-> In x l1 /\ ~ In x l2.
Proof.
  intros l1 l2 x. unfold list_subtract.
  rewrite List.filter_In.
  split.
  - intros [H1 H2]. split.
    + exact H1.
    + apply Bool.negb_true_iff in H2.
      intro Hin.
      assert (Hex : existsb (Nat.eqb x) l2 = true).
      { apply List.existsb_exists. exists x. split. exact Hin. apply Nat.eqb_refl. }
      rewrite H2 in Hex. discriminate.
  - intros [H1 H2]. split.
    + exact H1.
    + apply Bool.negb_true_iff.
      apply Bool.not_true_iff_false.
      intro Hex.
      apply H2.
      apply List.existsb_exists in Hex.
      destruct Hex as [y [Hy Heq]].
      apply Nat.eqb_eq in Heq. subst. exact Hy.
Qed.

Lemma NoDup_list_subtract : forall (l1 l2 : list ProcessId),
  NoDup l1 -> NoDup (list_subtract l1 l2).
Proof.
  intros l1 l2 H. unfold list_subtract.
  apply NoDup_filter_list. exact H.
Qed.

(** length_filter_sum: partition identity for boolean filters. *)
Lemma length_filter_sum : forall (l : list ProcessId) (f : ProcessId -> bool),
  length l = length (filter f l) + length (filter (fun x => negb (f x)) l).
Proof.
  intro l. induction l as [| h t IH]; intro f.
  - reflexivity.
  - specialize (IH f).
    case_eq (f h); intro Hfh; simpl; rewrite Hfh; simpl; lia.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    Section Quorums — arithmetic and intersection lemmas parameterised by n, f.
    ═══════════════════════════════════════════════════════════════════════════ *)

Section Quorums.

Variable n f : nat.
Hypothesis byzantine_bound : n > 3 * f.

Definition q := n - f.

(** A list is a quorum if it has at least q = n-f elements. *)
Definition is_quorum (l : list ProcessId) : Prop :=
  length l >= q.

(** Key arithmetic: q > f. *)
Lemma quorum_size_gt_f : q > f.
Proof. unfold q. lia. Qed.

(** Key arithmetic: n - 2f > f. *)
Lemma n_minus_2f_gt_f : n - 2 * f > f.
Proof. lia. Qed.

(** Key arithmetic: 2*q > n (quorum overlap is guaranteed). *)
Lemma two_quorums_must_overlap : 2 * q > n.
Proof. unfold q. lia. Qed.

(** Intersection of two lists. *)
Fixpoint list_inter (l1 l2 : list ProcessId) : list ProcessId :=
  match l1 with
  | nil => nil
  | h :: t =>
      if existsb (Nat.eqb h) l2
      then h :: list_inter t l2
      else list_inter t l2
  end.

(** Any element in the intersection is in both lists. *)
Lemma in_list_inter : forall l1 l2 x,
  In x (list_inter l1 l2) -> In x l1 /\ In x l2.
Proof.
  induction l1 as [| h t IH]; intros l2 x Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct (existsb (Nat.eqb h) l2) eqn:Hex.
    + simpl in Hin. destruct Hin as [Heq | Hin].
      * subst. split.
        -- left. reflexivity.
        -- apply existsb_exists in Hex.
           destruct Hex as [y [Hiny Heqb]].
           apply Nat.eqb_eq in Heqb. subst. exact Hiny.
      * apply IH in Hin. destruct Hin. split; [right |]; assumption.
    + apply IH in Hin. destruct Hin. split; [right |]; assumption.
Qed.

(** Existing arithmetic lemmas — kept verbatim. *)
Lemma quorum_intersection_arithmetic :
  forall (size_q1 size_q2 size_universe : nat),
    size_q1 >= q ->
    size_q2 >= q ->
    size_universe = n ->
    size_q1 + size_q2 - size_universe >= n - 2 * f.
Proof.
  intros. unfold q in *. lia.
Qed.

Lemma intersection_exceeds_f :
  forall (inter_size : nat),
    inter_size >= n - 2 * f ->
    inter_size > f.
Proof.
  intros. lia.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    New lemmas: concrete list intersection size and quorum correctness.
    ═══════════════════════════════════════════════════════════════════════════ *)

(** NoDup is preserved by list_inter. *)
Lemma NoDup_list_inter : forall l1 l2 : list ProcessId,
  NoDup l1 -> NoDup (list_inter l1 l2).
Proof.
  intros l1 l2 Hnd.
  induction l1 as [| h t IH].
  - constructor.
  - inversion Hnd as [| ? ? Hnih HnDt]; subst.
    simpl. destruct (existsb (Nat.eqb h) l2) eqn:Hex.
    + constructor.
      * intro Hhin.
        apply in_list_inter in Hhin.
        apply Hnih. exact (proj1 Hhin).
      * apply IH. exact HnDt.
    + apply IH. exact HnDt.
Qed.

(** list_inter equals filter with the membership predicate. *)
Lemma list_inter_as_filter : forall l1 l2 : list ProcessId,
  list_inter l1 l2 = filter (fun x => existsb (Nat.eqb x) l2) l1.
Proof.
  intros l1 l2.
  induction l1 as [| h t IH].
  - reflexivity.
  - simpl.
    destruct (existsb (Nat.eqb h) l2) eqn:Hex.
    + simpl. rewrite IH. reflexivity.
    + exact IH.
Qed.

(** Partition identity: |l1| = |inter l1 l2| + |subtract l1 l2|. *)
Lemma length_partition : forall l1 l2 : list ProcessId,
  length l1 = length (list_inter l1 l2) + length (list_subtract l1 l2).
Proof.
  intros l1 l2.
  rewrite (list_inter_as_filter l1 l2).
  exact (length_filter_sum l1 (fun x => existsb (Nat.eqb x) l2)).
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    quorum_intersection_has_correct

    The key exported lemma: given two quorums Q1 and Q2 drawn from a
    universe of n processes, and a faulty set of size <= f, their
    intersection contains at least one correct (non-faulty) process.

    Proof strategy (by contradiction):
      Suppose every element of list_inter Q1 Q2 is in faulty_procs.
      Then |list_inter Q1 Q2| <= |faulty_procs| <= f.
      Partition: |Q1| = |list_inter Q1 Q2| + |list_subtract Q1 Q2|.
      Since list_subtract Q1 Q2 and Q2 are disjoint subsets of universe:
        |list_subtract Q1 Q2| + |Q2| <= |universe| = n.
      Combined: |Q1| <= f + (n - |Q2|) <= f + f = 2f.
      But |Q1| >= n-f > 2f when n > 3f. Contradiction.
    ═══════════════════════════════════════════════════════════════════════════ *)
Lemma quorum_intersection_has_correct :
  forall (universe Q1 Q2 faulty_procs : list ProcessId),
    NoDup universe ->
    NoDup Q1 ->
    NoDup Q2 ->
    NoDup faulty_procs ->
    length universe = n ->
    (forall x, In x Q1 -> In x universe) ->
    (forall x, In x Q2 -> In x universe) ->
    (forall x, In x faulty_procs -> In x universe) ->
    length Q1 >= n - f ->
    length Q2 >= n - f ->
    length faulty_procs <= f ->
    exists c, In c (list_inter Q1 Q2) /\ ~ In c faulty_procs.
Proof.
  intros universe Q1 Q2 faulty_procs
         Hnu HnQ1 HnQ2 Hnf Hus HQ1u HQ2u _Hfu HlQ1 HlQ2 Hbf.
  apply not_all_in_exists_not.
  intro Hcontra.
  assert (Hni : NoDup (list_inter Q1 Q2))
    by (apply NoDup_list_inter; exact HnQ1).
  assert (Hli : length (list_inter Q1 Q2) <= length faulty_procs)
    by (apply NoDup_incl_length; assumption).
  assert (Hpart : length Q1 = length (list_inter Q1 Q2) + length (list_subtract Q1 Q2))
    by apply length_partition.
  assert (Hns : NoDup (list_subtract Q1 Q2))
    by (apply NoDup_list_subtract; exact HnQ1).
  assert (Hsu : forall x, In x (list_subtract Q1 Q2) -> In x universe).
  { intros x Hx. apply HQ1u.
    apply in_list_subtract in Hx. exact (proj1 Hx). }
  assert (Hdisj : forall x, In x (list_subtract Q1 Q2) -> ~ In x Q2).
  { intros x Hx. apply in_list_subtract in Hx. exact (proj2 Hx). }
  assert (HndApp : NoDup (list_subtract Q1 Q2 ++ Q2)).
  { apply NoDup_app_disjoint; assumption. }
  assert (HincApp : forall x, In x (list_subtract Q1 Q2 ++ Q2) -> In x universe).
  { intros x Hx. apply List.in_app_or in Hx.
    destruct Hx as [Hx | Hx].
    - exact (Hsu x Hx).
    - exact (HQ2u x Hx). }
  assert (HlenApp : length (list_subtract Q1 Q2 ++ Q2) =
                    length (list_subtract Q1 Q2) + length Q2)
    by apply List.length_app.
  assert (Hbound2 : length (list_subtract Q1 Q2) + length Q2 <= n).
  { rewrite <- HlenApp. rewrite <- Hus.
    apply NoDup_incl_length; assumption. }
  lia.
Qed.

End Quorums.
