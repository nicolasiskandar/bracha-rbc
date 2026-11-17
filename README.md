# Bracha RBC: Formally Verified Byzantine Reliable Broadcast

A complete implementation of Bracha's 1987 asynchronous Byzantine Reliable Broadcast (BRB) protocol in Rust, with a formal Coq specification and correctness proofs.

## Overview

This project implements and verifies a fundamental primitive in fault-tolerant distributed systems: **Byzantine Reliable Broadcast**. It guarantees that honest processes cannot disagree about a delivered value, even when up to ⌊(n−1)/3⌋ processes behave arbitrarily.

The project has two independent but related artifacts:
- **Rust workspace**: a modular, adversarially-tested implementation
- **Coq proof library**: machine-checked safety proofs plus explicitly axiomatized liveness

## Directory Structure

```
bracha-rbc/
├── Cargo.toml                     # Workspace root
├── crates/
│   ├── brb-core/                  # Pure protocol engine (no async)
│   │   ├── src/
│   │   │   ├── message.rs         # INIT / ECHO / READY types
│   │   │   ├── state.rs           # ProcessState (echo_sent, ready_sent, delivered)
│   │   │   ├── thresholds.rs      # Config { n, f }, threshold calculations
│   │   │   ├── protocol.rs        # BroadcastInstance, handle_message(), initiate()
│   │   │   └── errors.rs          # ProtocolError
│   │   └── tests/protocol_tests.rs
│   ├── brb-simulator/             # Deterministic adversarial simulator
│   │   ├── src/
│   │   │   ├── network.rs         # SimNetwork (tick-driven delivery)
│   │   │   ├── scheduler.rs       # SchedulePolicy (Fifo, Random, Partition)
│   │   │   ├── adversary.rs       # ByzantineProcess + ByzantineStrategy
│   │   │   ├── scenarios.rs       # Scenarios A–E constructors
│   │   │   └── trace.rs           # JSON trace export
│   │   └── tests/scenarios_test.rs
│   ├── brb-network/               # Tokio TCP networking layer
│   └── brb-experiments/           # CLI for scenarios and benchmarks
├── coq/                           # Coq formal verification
│   ├── Model.v                    # System model
│   ├── Messages.v                 # Message types
│   ├── State.v                    # Process state + predicates
│   ├── Transitions.v              # Step relation
│   ├── Quorums.v                  # Quorum intersection (fully proved)
│   ├── Transitions.v              # Finite small-step operational model
│   ├── Safety.v                   # Integrity + witness-based safety core
│   ├── Exec.v                     # Well-formed trace safety theorems
│   ├── Operational.v              # Reachable-state safety bridge
│   ├── Liveness.v                 # Fairness axioms + admitted liveness
│   ├── Main.v                     # Verified status summary
│   └── _CoqProject
└── docs/
    ├── specification.md           # Protocol rules and pseudocode
    ├── system_model.md            # Fault model and network assumptions
    ├── proof_overview.md          # Coq proof walkthrough
    └── evaluation.md              # Experimental results template
```

## Quick Start

### Build

```bash
source ~/.cargo/env   # if cargo not in PATH
cargo build --workspace
```

### Test (22 tests, all passing)

```bash
cargo test --workspace
```

### Run Adversarial Scenarios

```bash
# Scenario A: honest broadcaster, 1 silent Byzantine
cargo run -p brb-experiments -- run --scenario a --seed 42

# Scenario B: byzantine broadcaster equivocating INIT
cargo run -p brb-experiments -- run --scenario b --seed 42

# Scenario C: duplicate message flooding
cargo run -p brb-experiments -- run --scenario c --seed 42

# Scenario D: network partition + recovery
cargo run -p brb-experiments -- run --scenario d --seed 42

# Scenario E: conflicting READY messages
cargo run -p brb-experiments -- run --scenario e --seed 42

# Run each scenario 100 times with different seeds
cargo run -p brb-experiments -- run --scenario a --seed 0 --reps 100

# Benchmark across configurations n ∈ {4,7,10,13}
cargo run -p brb-experiments -- bench --sizes 4,7,10,13 --rounds 20
```

Traces are written as JSON to the `results/` directory.

### Compile Coq Proofs

```bash
cd coq
coq_makefile -f _CoqProject -o Makefile
make
```

## Protocol Summary

The protocol uses three message types:

| Message | Purpose |
|---------|---------|
| `INIT(v)` | Broadcaster proposes value `v` |
| `ECHO(v)` | Process acknowledges `v` |
| `READY(v)` | Process signals sufficient support for `v` |

**Rules** (with q = n − f):

1. On first `INIT(v)` from broadcaster → broadcast `ECHO(v)` exactly once
2. On q ECHOs for v → broadcast `READY(v)` (if not already sent)
3. On f+1 READYs for v → broadcast `READY(v)` (amplification, if not already sent)
4. On q READYs for v → deliver v (at most once)

## Adversarial Scenarios

| Scenario | Attack | Expected Outcome |
|----------|--------|-----------------|
| A | Silent Byzantine (doesn't participate) | All 3 correct processes deliver |
| B | Byzantine broadcaster sends conflicting INIT | No conflicting deliveries |
| C | Duplicate ECHO/READY flooding | Duplicates ignored; delivery unaffected |
| D | Network partition + recovery | Safety during partition; liveness after |
| E | Byzantine sends conflicting READY | Honest processes never disagree |

All 5 scenarios are tested with 100 random seeds each.

## Formal Verification

The safety development has three machine-checked layers, with no `Admitted`,
no `Axiom`, and no unproved witness hypotheses in the safety path:

1. **Snapshot core** (`Safety.v`): integrity plus witness-based
   `no_conflicting_ready` and `agreement`. Witness hypotheses require only
   correct quorum members to have sent the relevant message; Byzantine members
   may be silent.
2. **Abstract traces** (`Exec.v`): well-formed READY/DELIVER traces supply
   their own quorum witnesses, giving `no_conflicting_ready_top` and
   `agreement_top`.
3. **Operational model** (`Transitions.v` → `Operational.v`): every state
   reachable by `Transitions.reachable` supplies the Safety witnesses, giving
   `no_conflicting_ready_reachable` and `agreement_reachable`.

Fully proved in Coq:

- Echo Integrity: a correct process echoes at most one value per instance
- READY Integrity: a correct process broadcasts READY for at most one value
- Delivery Integrity: a correct process delivers at most once per instance
- Quorum arithmetic: `|Q1 ∩ Q2| ≥ n − 2f > f` when `n > 3f`
- No Conflicting READY: trace form and reachable-state form
- Agreement: trace form and reachable-state form

Only liveness remains outside the proved safety path:

- **Axiomatized fairness**: `fair_delivery`, `fair_scheduling`
- **Admitted with proof sketches**: Validity (honest broadcaster → all correct
  eventually deliver), Totality (one correct delivers → all correct eventually
  deliver)

These results concern the abstract protocol models. Rust refinement is
validated by tests and structural correspondence, not by a machine-checked
refinement proof.

## Fault Model

- **Fault bound**: n > 3f (minimum n=4, f=1)
- **Network**: fully connected, asynchronous, eventually reliable between correct processes
- **Authentication**: mutually authenticated channels (identity from connection, not message payload)
- **Byzantine power**: equivocation, omission, flooding, replay, selective delivery

## References

1. G. Bracha, "Asynchronous Byzantine Agreement Protocols," *Information and Computation*, 1987.
2. [Living with Asynchrony: Bracha's Reliable Broadcast](https://decentralizedthoughts.github.io/2020-09-19-living-with-asynchrony-brachas-reliable-broadcast/)
3. Bonomi et al., "Practical Byzantine Reliable Broadcast on Partially Connected Networks," 2016.
