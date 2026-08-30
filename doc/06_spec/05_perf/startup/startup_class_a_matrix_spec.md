# Class A v2 prebuilt cross-language startup matrix

This manual verifies the fail-closed receipt contract for Simple native, C,
Rust, Go, Python, Bun, and Java. Do not run a live matrix until the Simple
subject has adjacent, source-matched Stage 4 provenance accepted by the
canonical verifier.

## Run the schema controls

Run:

```bash
sh scripts/check/check-startup-class-a-matrix.shs --schema-selftest
```

The output must admit one synthetic seven-language receipt and report exactly
18 biting negatives: fallback, sample floor, budget policy, p50 budget, p95
budget, RSS budget, order seed, order position, missing raw row, recomputed
percentile, maximum RSS, hash, self-host status, startup class, ratio, rustup
identity, Rust host, and bound-tool version.

## Check Stage 4 without running the matrix

Run:

```bash
SIMPLE_CLASS_A_BINARY=bin/simple \
  sh scripts/check/check-startup-class-a-matrix.shs --stage4-preflight
```

The bootstrap seed must print `class_a_stage4=unavailable` and exit 2. This
preflight never builds a fixture or samples a competitor.

## Run the matrix

Only after an admitted Stage 4 exists, run:

```bash
CLASS_A_SAMPLES=7 sh scripts/check/check-startup-class-a-matrix.shs
```

The v2 receipt records immutable fairness classes and Simple-vs-C ratio
budgets, exact host/load/harness/Stage-4-verifier/compiler/launcher/runtime/
source/binary hashes, one raw wall/RSS row per round, recomputed p50/p95/max
RSS, and a ratio verdict. Every sample is a fresh process after one balanced
host-cache warmup; it is not claimed as a cold-machine run. Lane order is
SHA-256 randomized and balanced so every ready lane appears once per round.
Every invocation must emit only `class_a_checksum=20260819`.

Current v2 matrix receipts are written under
`build/perf/startup_class_a_v2/run_<UTC>_<pid>/class_a_startup_receipt_v2.md`.
No current receipt exists while Stage 4 remains unavailable and the matrix has
not run.

The historical receipt at
`build/perf/startup_class_a/run_20260819T042516Z_424887/class_a_startup_receipt.md`
remains an immutable diagnostic (mode 0444, SHA-256
`fc872d70ca7cd67a018274f70713131b593ac899666aeeebe142ed665d15c81b`).
The byte-identical mode-0444 preservation copy is
`doc/09_report/evidence/startup_class_a/diagnostic_receipt_20260819T042516Z.md`.
Neither copy is v2 admission evidence; never rewrite or upgrade either in
place.
