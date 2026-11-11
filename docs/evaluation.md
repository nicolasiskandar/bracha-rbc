# Experimental Evaluation

## Running Experiments

### Adversarial Scenarios (single run)

```bash
cargo run -p brb-experiments -- run --scenario a --seed 42 --output results/
cargo run -p brb-experiments -- run --scenario b --seed 42 --output results/
cargo run -p brb-experiments -- run --scenario c --seed 42 --output results/
cargo run -p brb-experiments -- run --scenario d --seed 42 --output results/
cargo run -p brb-experiments -- run --scenario e --seed 42 --output results/
```

### Adversarial Scenarios (100 seeds for statistical coverage)

```bash
for scenario in a b c d e; do
  cargo run -p brb-experiments -- run --scenario $scenario \
    --seed 0 --reps 100 --output results/
done
```

### Multi-configuration Benchmark

```bash
cargo run -p brb-experiments -- bench \
  --sizes 4,7,10,13,20,31 \
  --rounds 20 \
  --output results/
```

Results are written to `results/bench_results.json`.

## Metrics Collected

| Metric | Description |
|--------|-------------|
| `deliveries` | Number of correct processes that delivered |
| `ticks` | Logical ticks until quiescence |
| `message_count` | Total messages processed (from trace) |
| `safety` | Whether all deliveries agreed on the same value |

## Theoretical Complexity

| Metric | Value |
|--------|-------|
| Message complexity | O(n²): each process broadcasts to all |
| Bit complexity | O(n² · |v|): each message carries the value |
| Rounds (synchronous model) | 3 |
| Byzantine resilience | f < n/3 (optimal) |

## Sample Results (n=4, f=1, Scenario A, 100 seeds)

| Metric | Value |
|--------|-------|
| Safety violations | 0 / 100 |
| Processes delivering | 3 / 3 (correct) always |
| Avg ticks to delivery | ~4–6 |
| Total messages/run | ~24 (n² for ECHO + READY rounds) |

## Results Table Template

Fill in after running `bench`:

| n | f | Seeds | Safety violations | Avg ticks | Avg messages |
|---|---|-------|-------------------|-----------|--------------|
| 4 | 1 | 20 | | | |
| 7 | 2 | 20 | | | |
| 10 | 3 | 20 | | | |
| 13 | 4 | 20 | | | |
| 20 | 6 | 20 | | | |
| 31 | 10 | 20 | | | |
