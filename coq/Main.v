(*******************************************************************************)
(* Main.v — Summary of verified properties                                    *)
(*                                                                             *)
(* Imports all modules and states the top-level results.                      *)
(*******************************************************************************)

Require Import State.
Require Import Quorums.
Require Import Safety.
Require Import Transitions.
Require Import Exec.
Require Import Operational.
Require Import Liveness.

(**
  Summary of Bracha RBC Formal Verification
  ==========================================

  SAFETY — FULLY PROVED (zero Admitted in Model, Messages, State, Quorums,
           Transitions, Safety, Exec, and Operational):
  -------------------------------------------------------------------------
  1. Echo Integrity       [Safety.echo_integrity]
       EchoSent(p,v) /\ EchoSent(p,w) -> v = w

  2. READY Integrity      [Safety.ready_integrity]
       ReadySent(p,v) /\ ReadySent(p,w) -> v = w

  3. Delivery Integrity   [Safety.delivery_integrity]
       Delivered(p,v) /\ Delivered(p,w) -> v = w

  4. Quorum arithmetic    [Quorums.quorum_size_gt_f]
       q = n-f > f when n > 3f

  5. Quorum intersection bound  [Quorums.quorum_intersection_arithmetic]
       |Q1| >= n-f /\ |Q2| >= n-f -> |Q1 INTERSECT Q2| >= n-2f

  6. Intersection exceeds fault bound  [Quorums.intersection_exceeds_f]
       |Q1 INTERSECT Q2| >= n-2f -> |Q1 INTERSECT Q2| > f (when n > 3f)

  7. List intersection membership  [Quorums.in_list_inter]
       x IN inter(l1,l2) -> x IN l1 /\ x IN l2

  8. Concrete quorum intersection has correct process
     [Quorums.quorum_intersection_has_correct]
       Two quorums drawn from a universe of n processes share
       a process not in faulty_list (of size <= f).

  9. Witness-based safety core
       [Safety.no_conflicting_ready, Safety.agreement]
       Fully proved under explicit echo-quorum and READY-quorum witnesses.
       All correct members of those witnesses must support the relevant
       value; Byzantine members need not send anything.

  10. Trace-level safety  [Exec.echo_quorum_invariant,
                          Exec.ready_quorum_invariant,
                          Exec.no_conflicting_ready_top,
                          Exec.agreement_top]
       Every well-formed READY/DELIVER trace has the required quorum
       witnesses, and two correct READYs or DELIVERs agree.  No Admitted
       and no unproved witness hypotheses.

  11. Operational safety bridge  [Operational.ready_has_echo_quorum_reachable,
                                  Operational.delivery_has_ready_quorum_reachable]
       Every state reachable by Transitions.reachable satisfies the
       witness hypotheses of Safety.  Sender lists are stable, valid,
       duplicate-free, and drawn from the finite universe.

  12. End-to-end operational safety
      [Operational.no_conflicting_ready_reachable,
       Operational.agreement_reachable]
       For every reachable global state, two correct processes cannot send
       READY for different values, and two correct processes cannot deliver
       different values.

  LIVENESS (Admitted — depend on explicit fairness axioms):
  ---------------------------------------------------------
  13. Validity    [Liveness.validity]
  14. Totality    [Liveness.totality]

  Fairness axioms:
    fair_delivery   : correct -> correct messages eventually delivered
    fair_scheduling : correct processes eventually scheduled

  Liveness proofs require a full asynchronous execution model
  with fairness reasoning and are left as future work.  No liveness
  result is used in the safety path.
*)
