# Rocq Proof Overview

This document explains the structure of the Rocq formal verification in `coq/`.

## Goal

We machine-check Bracha BRB safety in three layers:

1. a snapshot core with explicit quorum-witness hypotheses,
2. a well-formed abstract READY/DELIVER trace model, and
3. a small-step operational model whose reachable states instantiate the
   snapshot witnesses.

No `Admitted`, `Axiom`, or unproved witness hypothesis appears in the safety
path. Liveness remains separate: it uses explicit fairness axioms and admitted
proofs.

## Proof Dependency Graph

```
Model.v  (early arithmetic precursor)
Messages.v → State.v
              ├──→ Quorums.v      (fully proved)
              ├──→ Safety.v       (integrity + witness core, fully proved)
              │        └──→ Exec.v (well-formed traces, fully proved)
              └──→ Transitions.v  (operational model)
                       └──→ Operational.v
                              (uses Transitions + Safety, fully proved)

Liveness.v (axioms + admitted liveness) ──→ Main.v
```

## File-by-File Walkthrough

### `Model.v`: Early System Model

Contains the original arithmetic formulation (`q_gt_f`,
`n_minus_2f_gt_f`, `two_quorums_overlap`) under an abstract faulty predicate.
The main development uses the concrete, list-based statements in `Quorums.v`.

### `State.v`: Process State

A direct formalization of the Rust `ProcessState` struct:

```coq
Record ProcessState := mkPS {
  echo_sent     : option Value;
  ready_sent    : option Value;
  delivered     : option Value;
  echo_senders  : Value -> list ProcessId;
  ready_senders : Value -> list ProcessId
}.
```

Using `option Value` rather than `bool` records the committed value, which
makes integrity proofs immediate: two `Some` values must be equal.

`GlobalState` carries the local-state function plus a message `history`.

### `Transitions.v`: Small-Step Operational Model

Defines concrete protocol events and an inductive transition relation with a
finite `universe`, an explicit duplicate-free `faulty_list`, and guards that
check receiver/sender membership and correctness:

```coq
Inductive step : GlobalState -> Event -> GlobalState -> Prop :=
  | step_recv_init        (* record ECHO and add the sender *)
  | step_recv_echo        (* record ECHO and add the sender *)
  | step_recv_ready       (* record READY and add the sender *)
  | step_send_ready_echo  (* n-f ECHOs -> READY *)
  | step_send_ready_amplify (* f+1 READYs -> READY *)
  | step_deliver          (* n-f READYs -> DELIVER *)
  | step_byzantine        (* inject a message under a faulty identity *).
```

`reachable` is the reflexive-transitive closure of `step` from `init_gs`.
Byzantine processes can inject arbitrary messages under their own identity,
but they do not have to send any message to justify a correct process's
quorum.

### `Quorums.v`: Quorum Intersection (Fully Proved)

The mathematical core of the safety argument. Two quorums of size at least
`n - f` over a universe of size `n` intersect in at least `n - 2f` processes.
Since `n > 3f`, this is strictly more than `f`, so a concrete intersection
must contain a process outside `faulty_list`.

Key results include `quorum_size_gt_f`, `quorum_intersection_arithmetic`,
`intersection_exceeds_f`, `in_list_inter`, and
`quorum_intersection_has_correct`.

### `Safety.v`: Witness-Based Safety Core (Fully Proved)

Integrity theorems are proved directly from `option` injectivity:

- `echo_integrity`
- `ready_integrity`
- `delivery_integrity`

Inside `Section SafetyWithWitnesses`, two explicit hypotheses connect a
snapshot `GlobalState` to protocol justifications:

- `echo_justified`: every correct READY sender has a duplicate-free
  `n - f` quorum drawn from the universe; only *correct* members are required
  to have echoed the value.
- `delivery_has_ready_quorum`: every correct Delivered fact has an existential
  duplicate-free `n - f` quorum; only *correct* members are required to have
  sent READY for the delivered value.

Then:

- `Safety.no_conflicting_ready` finds a correct process in the intersection of
  the two echo quorums and applies `echo_integrity`.
- `Safety.agreement` finds a correct READY sender in each delivery witness and
  reduces to `no_conflicting_ready`.

There are no admitted proof obligations in this file.

### `Exec.v`: Abstract Trace Layer (Fully Proved)

`Exec.v` defines `ExecEv` (`ERdy`, `EDel`) and `wf_trace`. Each event records
its local justification:

- a READY event is justified by an echo quorum or by `f + 1` earlier READY
  events for the same value;
- a DELIVER event is justified by a READY quorum.

The following are fully proved:

- `echo_quorum_invariant`: every correct READY event in a well-formed trace has
  an echo quorum. Amplification is handled by selecting a correct sender from
  an `f + 1` READY set, since at most `f` senders are faulty.
- `ready_quorum_invariant`: every correct DELIVER event has a READY quorum.
- `no_conflicting_ready_top`
- `agreement_top`

This layer is independent of how the snapshot state evolves.

### `Operational.v`: Reachable-State Bridge (Fully Proved)

`Operational.v` supplies the Safety witnesses for every state reachable by
`Transitions.step`.

The bridge proves that sender lists are:

- stable under updates that do not change the relevant field,
- valid: every correct listed ECHO/READY sender actually sent that message,
- duplicate-free, and
- drawn from the finite universe.

It then proves:

- `ready_has_echo_quorum_reachable`: every correct READY sender has an echo
  quorum. A newly sent READY uses its `n - f` ECHO witnesses; amplification
  selects a correct earlier READY sender from the `f + 1` set and reuses that
  sender's echo quorum.
- `delivery_has_ready_quorum_reachable`: every Delivered fact has a READY
  quorum; a new delivery uses the `n - f` READY senders counted by the
  transition guard.
- `no_conflicting_ready_reachable`
- `agreement_reachable`

The final two theorems instantiate `Safety.no_conflicting_ready` and
`Safety.agreement`, so they are machine-checked end-to-end safety results over
`Transitions.reachable`, not merely proof sketches.

### `Liveness.v`: Liveness Under Fairness (Admitted)

Liveness cannot be proved from a safety invariant alone; it needs assumptions
about fair delivery and fair scheduling. These are declared explicitly as
axioms with placeholder statements (`fair_delivery`, `fair_scheduling`) so the
dependency is visible.

Under these axioms, `validity` and `totality` are stated with proof sketches
but remain `Admitted`. Neither theorem is imported into the safety path.

### `Main.v`: Status Summary

Imports the modules and records the proved/admitted status of each top-level
result. It states the operational safety theorems and separates them from the
admitted liveness results.

## What Is Proved vs. Admitted

| Theorem | Status | Basis |
|---------|--------|-------|
| `echo_integrity` | Proved | `option` injectivity |
| `ready_integrity` | Proved | `option` injectivity |
| `delivery_integrity` | Proved | `option` injectivity |
| `quorum_size_gt_f` | Proved | `lia` from `n > 3f` |
| `quorum_intersection_arithmetic` | Proved | list arithmetic |
| `intersection_exceeds_f` | Proved | `lia` |
| `in_list_inter` | Proved | list induction |
| `quorum_intersection_has_correct` | Proved | finite-list cardinality |
| `Safety.no_conflicting_ready` | Proved | witness hypotheses + quorum intersection |
| `Safety.agreement` | Proved | delivery witnesses + `no_conflicting_ready` |
| `Exec.no_conflicting_ready_top` | Proved | well-formed trace induction |
| `Exec.agreement_top` | Proved | trace READY quorums |
| `Operational.no_conflicting_ready_reachable` | Proved | reachable-state bridge |
| `Operational.agreement_reachable` | Proved | reachable-state bridge |
| `Liveness.validity` | Admitted | requires fair delivery/scheduling |
| `Liveness.totality` | Admitted | requires fair delivery + amplification |

## Relationship to Rust Implementation

The machine-checked end-to-end safety results stop at the Rocq operational
model. The Rust implementation is connected to that model by:

1. unit tests in `brb-core` checking each protocol rule in isolation;
2. adversarial simulation in `brb-simulator` with many seeds per scenario; and
3. structural correspondence between the Rust `ProcessState` and the Rocq
   `ProcessState` record.

A machine-checked refinement from Rust to the Rocq transition system is not
claimed.
