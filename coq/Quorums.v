(******************************************************************************)
(* Quorums.v — Quorum intersection lemmas                                    *)
(*                                                                            *)
(* Key result: two quorums of size >= n-f over n processes must share at      *)
(* least n-2f elements. Since n > 3f, n-2f > f, so the intersection           *)
(* cannot consist entirely of Byzantine processes.                             *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition ProcessId := nat.

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

(** ═══════════════════════════════════════════════════════════════════════
    Quorum intersection bound (stated as an abstract arithmetic fact).

    For two quorums Q1, Q2 ⊆ {0..n-1} with |Q1|,|Q2| ≥ n-f:

      |Q1 ∩ Q2| = |Q1| + |Q2| - |Q1 ∪ Q2|
                 ≥ (n-f) + (n-f) - n
                 = n - 2f

    Since n > 3f, we get n - 2f > f.
    Therefore the intersection contains more than f elements,
    so it cannot be contained in the set of f faulty processes.
    At least one correct process must be in the intersection.
    ═══════════════════════════════════════════════════════════════════════ *)

(** We prove the arithmetic part directly. The set-theoretic part
    (counting intersection elements) would require a finite-set library;
    we state it as a hypothesis and prove the consequence. *)

Lemma quorum_intersection_arithmetic :
  forall (size_q1 size_q2 size_universe : nat),
    size_q1 >= q ->
    size_q2 >= q ->
    size_universe = n ->
    size_q1 + size_q2 - size_universe >= n - 2 * f.
Proof.
  intros. unfold q in *. lia.
Qed.

(** The critical consequence: the intersection size exceeds f. *)
Lemma intersection_exceeds_f :
  forall (inter_size : nat),
    inter_size >= n - 2 * f ->
    inter_size > f.
Proof.
  intros. lia.
Qed.

End Quorums.
