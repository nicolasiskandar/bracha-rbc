# System Model

## Processes

The system consists of n processes:

```
P = {P₀, P₁, ..., P_{n-1}}
```

One process, the **broadcaster**, wants to transmit a value v to all others.

## Fault Model

### Byzantine Bound

At most f processes may be **Byzantine** (arbitrarily faulty). The protocol requires:

```
n > 3f    (equivalently: f < n/3)
```

| n | max f |
|---|-------|
| 4 | 1 |
| 7 | 2 |
| 10 | 3 |
| 13 | 4 |
| 20 | 6 |
| 31 | 10 |

**Why n > 3f?** The quorum size is q = n − f. For two quorums to intersect in a correct process, we need: `|Q1 ∩ Q2| > f`. By inclusion-exclusion: `|Q1 ∩ Q2| ≥ 2q − n = n − 2f`. We need `n − 2f > f`, i.e., `n > 3f`. This bound is tight, with n = 3f, agreement cannot be guaranteed.

### Byzantine Capabilities

A Byzantine process can:
- Send **different values** to different processes (equivocation)
- Send **malformed messages** (invalid encodings, wrong instance IDs)
- **Refuse** to send any messages (silent crash)
- Send **duplicate messages** repeatedly
- **Coordinate** with other Byzantine processes
- Send messages **out of order** or with arbitrary timing

A Byzantine process **cannot**:
- Forge another process's identity (authentication prevents this)
- Observe private state of correct processes
- Prevent message delivery between correct processes indefinitely

## Network Model

### Asynchronous Channels

The network is **asynchronous** and **fully connected**:
- Messages may be delayed for an **arbitrary but finite** time
- There are **no global clocks** and no synchronized rounds
- There are **no timeouts** in the base protocol
- Messages between correct processes are **eventually delivered**

> [!IMPORTANT]
> The absence of timeouts is intentional. Any protocol with timeouts in an asynchronous network either sacrifices safety (may deliver wrong values on timeout) or sacrifices progress (may block indefinitely). Bracha's protocol achieves both safety and liveness purely through message counting.

### Authenticated Channels

The protocol requires **point-to-point authenticated channels**:
- Each connection endpoint is verified (e.g., via TLS mutual authentication)
- The **sender identity comes from the channel**, not the message payload
- A Byzantine process can send arbitrary content under its own identity
- It cannot impersonate a correct process

This is weaker than digital signatures on each message, classic Bracha broadcast does not require a PKI.

### What "Eventually Delivered" Means

For liveness, correct-to-correct messages must eventually be received. This does **not** mean:
- Messages arrive in a fixed time (there is no time bound)
- Messages arrive in order (they may be reordered)
- Messages aren't duplicated (duplicates are harmless due to deduplication)

**Safety** (Agreement, Integrity) holds even if correct-to-correct messages are dropped or delayed indefinitely. Only **liveness** (Validity, Totality) requires eventual delivery.

## Safety vs. Liveness

| Property | Type | Meaning |
|----------|------|---------|
| **Agreement** | Safety | No two correct processes deliver different values |
| **Integrity** | Safety | Correct processes don't equivocate (echo/ready/deliver once) |
| **Validity** | Liveness | If broadcaster is correct and broadcasts v, all correct eventually deliver v |
| **Totality** | Liveness | If one correct delivers v, all correct eventually deliver v |

Safety properties hold in **all** executions, including those with network partitions.

Liveness properties hold only under **fairness** (fair message delivery + fair scheduling).

## Relationship Between Assumptions

```
n > 3f
├── Guarantees: quorum intersection contains ≥ n-2f > f elements
│   ├── At least 1 correct process in every two quorum intersection
│   ├── Agreement (no two conflicting deliveries)
│   └── Integrity (no equivocation forces delivery)
└── Guarantees: n-f correct processes form a quorum
    ├── Validity (correct broadcaster → delivery)
    └── Totality (one delivery → all deliver)

Fair delivery + Fair scheduling
└── Liveness (Validity + Totality)
```

## Simulator vs. Real Network

The simulator enforces the same model constraints:
- Byzantine processes are given their own `ByzantineProcess` struct and cannot access honest process state
- Message sender identity is provided by the envelope (`from: ProcessId`), not the message payload
- Deduplication is enforced inside `ProcessState` via `HashSet<ProcessId>`
- Each broadcast instance has completely independent state (`InstanceId` isolates)
