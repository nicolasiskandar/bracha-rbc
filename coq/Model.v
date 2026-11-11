(******************************************************************************)
(* Model.v — System model for Bracha's Reliable Broadcast                    *)
(*                                                                            *)
(* We work with a finite set of processes {0, ..., n-1}.                      *)
(* We parameterize over n (total) and f (max Byzantine).                      *)
(* The Byzantine bound requires n > 3*f.                                      *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(** Process identifiers and values are natural numbers. *)
Definition ProcessId := nat.
Definition Value := nat.

(** System parameters *)
Section SystemModel.

Variable n : nat.
Variable f : nat.

(** The Byzantine fault bound. *)
Hypothesis byzantine_bound : n > 3 * f.
Hypothesis n_positive : n > 0.

(** The quorum size: q = n - f. *)
Definition q : nat := n - f.

(** Key arithmetic: q > f when n > 3f. *)
Lemma q_gt_f : q > f.
Proof.
  unfold q. lia.
Qed.

(** Key arithmetic: n - 2f > f when n > 3f. *)
Lemma n_minus_2f_gt_f : n - 2 * f > f.
Proof. lia. Qed.

(** Key arithmetic: 2*q > n when n > 3f (quorum overlap). *)
Lemma two_quorums_overlap : 2 * q > n.
Proof. unfold q. lia. Qed.

(** Faulty process predicate. *)
Variable faulty : ProcessId -> Prop.

(** Decidability of faulty (needed for classical reasoning). *)
Hypothesis faulty_dec : forall p, {faulty p} + {~ faulty p}.

(** At most f processes are faulty.
    We express this via a bounding list. *)
Variable faulty_list : list ProcessId.
Hypothesis faulty_complete : forall p, faulty p -> In p faulty_list.
Hypothesis faulty_bound_len : length faulty_list <= f.

(** A process is correct iff it is not faulty. *)
Definition correct (p : ProcessId) : Prop := ~ faulty p.

End SystemModel.
