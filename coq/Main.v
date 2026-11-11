(******************************************************************************)
(* Main.v — Summary of verified properties                                   *)
(*                                                                            *)
(* Imports all modules and states the top-level results.                      *)
(******************************************************************************)

Require Import State.
Require Import Quorums.
Require Import Safety.
Require Import Liveness.

(**
  Summary of Bracha RBC Formal Verification
  ==========================================

  FULLY PROVED (no Admitted):
  ---------------------------
  1. Echo Integrity     [Safety.echo_integrity]
     echo_sent(p) = Some v ∧ echo_sent(p) = Some w → v = w

  2. READY Integrity    [Safety.ready_integrity]
     ready_sent(p) = Some v ∧ ready_sent(p) = Some w → v = w

  3. Delivery Integrity [Safety.delivery_integrity]
     delivered(p) = Some v ∧ delivered(p) = Some w → v = w

  4. Quorum arithmetic  [Quorums.quorum_size_gt_f]
     q = n-f > f when n > 3f

  5. Quorum intersection bound [Quorums.quorum_intersection_arithmetic]
     |Q1| ≥ n-f ∧ |Q2| ≥ n-f → |Q1∩Q2| ≥ n-2f

  6. Intersection exceeds fault bound [Quorums.intersection_exceeds_f]
     |Q1∩Q2| ≥ n-2f → |Q1∩Q2| > f (when n > 3f)

  7. List intersection membership [Quorums.in_list_inter]
     x ∈ inter(l1,l2) → x ∈ l1 ∧ x ∈ l2


  STATED WITH PROOF SKETCH (Admitted):
  ------------------------------------
  8. No Conflicting READY  [Safety.no_conflicting_ready]
     Requires execution-trace induction + quorum intersection.

  9. Agreement             [Safety.agreement]
     Depends on no_conflicting_ready.


  LIVENESS (Admitted, depend on explicit fairness axioms):
  -------------------------------------------------------
  10. Validity    [Liveness.validity]
  11. Totality    [Liveness.totality]

  Fairness axioms:
    fair_delivery   : correct→correct messages eventually delivered
    fair_scheduling : correct processes eventually scheduled
*)
