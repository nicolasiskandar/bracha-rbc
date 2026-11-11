# Coq Proof Overview

This document explains the structure of the Coq formal verification in `coq/`.

## Goal

We formally establish that the abstract Bracha BRB protocol satisfies its safety properties. The Coq proofs provide machine-checked mathematical guarantees that are independent of the Rust implementation.

## Proof Dependency Graph

```
Model.v → Messages.v → State.v → Transitions.v
                           │
                           ├──→ Quorums.v  (fully proved)
                           │
                           └──→ Safety.v   (integrity: proved; agreement: admitted)
                                   │
                                   └──→ Liveness.v (axiomatized)
                                               │
                                               └──→ Main.v
```

## File-by-File Walkthrough

### `Model.v`: System Model

Defines the basic types and hypotheses:

```coq
Variable n f : nat.
Hypothesis byzantine_bound : n > 3 * f.

Definition q := n - f.
Definition correct (p : ProcessId) := ~ faulty p.
```

Key lemmas (all proved from `lia`):
- `q_gt_f`: q > f (quorum exceeds fault bound)
- `n_minus_2f_gt_f`: n − 2f > f (intersection exceeds fault bound)
- `two_quorums_overlap`: 2q > n (two quorums must share elements)

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

Using `option Value` (not `bool`) means the value committed to is recorded: which makes integrity proofs trivial: if `echo_sent = Some v` and `echo_sent = Some w`, then `v = w` by injectivity of `Some`.

### `Transitions.v`: Step Relation

Defines `step gs ev gs'`: a small-step transition from global state `gs` to `gs'` via event `ev`. Correct processes must follow the protocol rules; Byzantine processes may inject any message:

```coq
Inductive step : GlobalState -> Event -> GlobalState -> Prop :=
  | step_recv_init : ...      (* Rule 1: echo *)
  | step_recv_echo : ...      (* accumulate echoes *)
  | step_recv_ready : ...     (* accumulate READYs *)
  | step_send_ready_echo : ...    (* Rule 2a: n-f ECHOs → READY *)
  | step_send_ready_amplify : ... (* Rule 2b: f+1 READYs → READY *)
  | step_deliver : ...        (* Rule 3: n-f READYs → deliver *)
  | step_byzantine : ...      (* arbitrary action *)
```

Reachable states are defined as the reflexive-transitive closure of `step`.

### `Quorums.v`: Quorum Intersection (Fully Proved)

The mathematical core of the safety argument.

**Key lemma: `quorum_intersection_arithmetic`**

For any two quorums Q1, Q2 (each of size ≥ n−f) over a universe of n processes:

```
|Q1| + |Q2| ≤ n + |Q1 ∩ Q2|    (union ≤ universe)
|Q1 ∩ Q2| ≥ |Q1| + |Q2| − n
           ≥ (n−f) + (n−f) − n
           = n − 2f
```

**Key consequence: `intersection_exceeds_f`**

Since n > 3f: n − 2f > f. The intersection is strictly larger than the fault bound, so it cannot consist entirely of Byzantine processes. At least one correct process is in every two-quorum intersection.

**List intersection membership: `in_list_inter`** (proved by induction)

```coq
Lemma in_list_inter : forall l1 l2 x,
  In x (list_inter l1 l2) -> In x l1 /\ In x l2.
```

### `Safety.v`: Safety Theorems

**Theorems 1, 2, 6: Integrity (fully proved)**

Echo/READY/delivery integrity follows immediately from `option` monotonicity:

```coq
Theorem echo_integrity :
  forall gs p v w, EchoSent gs p v -> EchoSent gs p w -> v = w.
Proof.
  (* Both hypotheses say echo_sent = Some v and Some w.
     Rewrite one into the other; apply injectivity of Some. *)
  intros. unfold EchoSent in *. rewrite H in H0.
  apply option_some_inj. exact H0.
Qed.
```

The proof is 3 lines and requires no induction: the `Option<Value>` state design makes it trivial.

**Lemma: `no_conflicting_ready` (admitted with proof sketch)**

This is the deepest result. The proof requires induction over the execution trace and the quorum intersection argument:

1. Consider the first correct READY event in the execution.
2. It must be triggered by n−f ECHOs (Rule 2a), forming quorum Q1.
   - If triggered by f+1 READYs (Rule 2b), at least one of those must be correct (since f Byzantine can't supply f+1): contradicting "first".
3. If a second correct READY for a different value w exists:
   - If triggered by n−f ECHOs → quorum Q2.
     - By quorum intersection, ∃ correct r ∈ Q1 ∩ Q2.
     - r echoed both v and w → contradicts `echo_integrity`.
   - If triggered by f+1 READYs → at least 1 correct sent READY earlier → contradicts "first".

**Theorem 3: Agreement (admitted)**

Follows from `no_conflicting_ready` plus the observation that delivery quorums must contain correct READY senders.

### `Liveness.v`: Liveness Under Fairness

Liveness cannot be proved from safety axioms alone. It requires assumptions about execution fairness:

```coq
Axiom fair_delivery :
  forall p q t, correct p -> correct q ->
  (* messages from p to q are eventually received *)

Axiom fair_scheduling :
  forall p t, correct p ->
  (* p eventually processes all pending messages *)
```

These axioms are explicitly stated (not hidden) so the dependency is clear.

Under these axioms:

- **Validity**: correct broadcaster → all correct eventually deliver
- **Totality**: one correct delivers → all correct eventually deliver

Both are admitted because they require temporal logic reasoning over infinite traces that is beyond the scope of this initial formalization.

## What Is Proved vs. Admitted

| Theorem | Status | Why |
|---------|--------|-----|
| `echo_integrity` | ✅ Proved | Option monotonicity; 3-line proof |
| `ready_integrity` | ✅ Proved | Same |
| `delivery_integrity` | ✅ Proved | Same |
| `quorum_size_gt_f` | ✅ Proved | `lia` from `n > 3f` |
| `quorum_intersection_arithmetic` | ✅ Proved | `lia` |
| `intersection_exceeds_f` | ✅ Proved | `lia` |
| `in_list_inter` | ✅ Proved | List induction |
| `no_conflicting_ready` | 🔶 Admitted | Needs execution-trace induction infra |
| `agreement` | 🔶 Admitted | Needs `no_conflicting_ready` |
| `validity` | 🔶 Admitted | Needs fair_delivery + trace induction |
| `totality` | 🔶 Admitted | Same |

The admitted theorems have detailed proof sketches in the source. The key mathematical content (quorum arithmetic) is fully proved.

## Relationship to Rust Implementation

The Coq proofs establish correctness of the **abstract protocol**. The Rust implementation is validated against the protocol by:

1. **Unit tests** in `brb-core/tests/` checking each protocol rule in isolation
2. **Adversarial simulation** in `brb-simulator/tests/` with 100+ random seeds per scenario
3. **Structural correspondence**: the `ProcessState` struct mirrors the Coq `ProcessState` record field-for-field

True refinement verification (proving the Rust code implements the Coq spec) would require tools like Verus or Creusot and is left as future work.
