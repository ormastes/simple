# Bug: Stage 4 `--low-memory` build grows past 25 GB RSS

## Status

Open. The bounded incremental Stage 4 build was stopped deliberately before
host/session failure; no Stage 4 artifact was produced, so the canonical
essential test/lint/duplication gate remains pending.

## Reproduction

Use the constructor-preserving Stage 3 compiler to build only the full CLI with
`--runtime-bundle core-c-bootstrap`, `--entry-closure`, `--low-memory`, two
threads, and the existing native cache. The exact invocation is the
`bootstrap_native_build_main` command in
`scripts/bootstrap/bootstrap-from-scratch.sh`; this run did not invoke the full
bootstrap pipeline.

Observed on 2026-07-18:

- one `simple native-build` process remained CPU-active (about 100% CPU), so it
  was not classified as a deadlock;
- elapsed time exceeded 10 minutes without an output artifact or progress
  marker;
- RSS reached 24,916,288 KiB (about 23.8 GiB) despite `--low-memory`;
- the process was interrupted once with exit 130 under the runaway/budget
  guard; it was not retried.

## Required fix and regression

1. Add bounded phase/progress reporting to the pure-Simple native-build driver
   so compilation, aggregation, and linking can be distinguished without a
   debugger.
2. Profile retained module/MIR/object state in the Stage 4 entry-closure path
   and release completed-module state under `--low-memory`.
3. Add an isolated Stage 4 resource smoke that samples max RSS and fails on
   timeout or an agreed memory ceiling before the essential-tools gate.
4. After the resource smoke passes, run
   `scripts/check/check-bootstrap-essential-tools-smoke.shs` exactly once with
   the resulting Stage 4 binary.

Acceptance requires a produced full CLI, bounded warm elapsed time/RSS evidence,
and green test-runner, lint, and duplication probes. A CPU-active process with
unbounded RSS is not a passing “slow build.”
