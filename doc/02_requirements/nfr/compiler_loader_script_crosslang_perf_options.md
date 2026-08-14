<!-- codex-research -->
# Compiler loader script cross-language performance: NFR options

No target set is selected. The user must explicitly choose one; then this file
is deleted and the chosen NFRs are written to the final NFR document.

## Option A — Current strict budgets

Retain the provisional NFR-001..NFR-006 contract: cached failed probes at most
10% of the uncached baseline; deterministic cache counts 100/1; packed bytes
remain one byte per element with RSS no more than four times payload for the
native fixture; 1 MiB fixture time below 1 second and 32 MiB below 30 seconds;
bounded subprocesses and fail-closed provenance; scoped foreign capabilities;
and host/tool metadata for every retained row.

- Pros: preserves the existing executable thresholds and strongest evidence.
- Cons: requires an admitted deployed CLI and Linux GNU-time fixture; strict
  RSS may expose unrelated runtime overhead.
- Effort: L, approximately 8-15 implementation/test/report files.

## Option B — Correctness-first budgets with performance baselines

Make cache count, provenance, timeout, semantic checksum, packed storage, and
foreign lifetime hard gates. Record latency/RSS baselines now, but select hard
latency/RSS thresholds only after three admitted runs on one named host class.

- Pros: avoids guessing thresholds before admissible data exists; retains
  safety and semantic gates.
- Cons: performance regression protection is incomplete until the baseline
  follow-up; results are less immediately comparable.
- Effort: M, approximately 6-12 files plus a baseline-review follow-up.

## Option C — Portability matrix budgets

Keep Option A on Linux and require equivalent host-specific elapsed/RSS
commands and thresholds for macOS, FreeBSD, and Windows before feature close.

- Pros: produces broad, explicit capability coverage and prevents silent
  Linux-only assumptions.
- Cons: high infrastructure cost; heterogeneous RSS semantics prevent one
  aggregate threshold; unavailable hosts block completion.
- Effort: XL, approximately 20-35 files across CI, scripts, fixtures, and docs.
