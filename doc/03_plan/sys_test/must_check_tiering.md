# Must-Check Tiering Test Plan

## Interpreter startup evidence producer

The bootstrap-only producer must retain exact fixture, runtime, compiler,
version, timer, raw-sample, statistics, and Stage 4 blobs under an absent
repository-contained output directory. It measures launches with retained
`CLOCK_MONOTONIC` under a closed `env -i` launch environment, requires one no-fallback interpreter receipt per timed
Simple process, recomputes p50/p95, and fails unless Simple is strictly below
Python, Bun, and Go for both cold and warmed launches. It must reject test
overrides, HEAD/source drift, attachment drift, and noncanonical Stage 4, and
must retain and bind the HEAD producer/checker sources, reject their dirty
worktree forms, and leave signing to an independent reviewer. Runtime-cache
cold uses fresh per-sample isolated `HOME`/`XDG_CACHE_HOME`/`TMPDIR` directories
and explicitly is not OS page-cache cold; warm uses stable per-lane isolated
directories populated by fixed warmups. Focused mutation coverage lives
in `interpreter_startup_samples_test.shs` and
`interpreter_startup_producer_test.shs`.

For v3, producer-side validation and external admission execute private
mode-700 parity and samples-checker snapshots materialized from the retained
HEAD blobs. They do not execute the live worktree copies. The outer shell
producer/importer and the canonical Stage 4 provenance helper still execute as
repository-owned entrypoints; their pre/post HEAD and byte bindings reduce but
cannot make arbitrary shell-source replacement races impossible. Run this gate
only in a controlled repository whose write access is excluded during
production and admission.

External startup admission authenticates the signed summary before loading any
runtime or executable checker attachment. Before authentication, it may load
only the committed reviewer signature and the public key selected by the
repository-pinned reviewer policy. A missing, untrusted, or invalid signature
therefore fails before checker materialization, permission changes, or
execution.

- Prove valid fresh compiler phase rows pass ledger validation.
- Prove stale fingerprints, failed blocking rows, missing rows, duplicate rows,
  and empty manifests fail.
- Prove TODO rows are preserved and visibly reported.
- Prove bootstrap receipt promotion is deterministic and requires all four
  compiler phase oracle lines.
- Prove bootstrap completion also runs automated rows, retains an evidence log,
  binds them to the exact validated Stage 4 candidate despite a conflicting
  ambient `SIMPLE_BINARY`, rejects self-test runner overrides in production,
  and preserves broad TODOs.
- Prove the existing interpreter/JIT/native differential producer is owned by
  the bootstrap tier and cannot run from the lightweight push path.
- Prove PASS rows without timestamps or evidence references fail validation.
- Prove unowned rows, TODO rows without an unblock condition, and PASS rows
  with a pending unblock condition fail validation.
- Prove the bootstrap producer's generated ledger is committed and accepted by
  the real pre-push ref-input consumer without manually fabricating PASS state.
- Prove the push driver directly names no native-build, QEMU, full-test, or
  benchmark command and its focused self-test stays within ten seconds.
- Prove identical ref updates execute the tree gate once, more than two unique
  updates fail closed, and the push tree gate receives bounded `--push-tip`
  mode while its exhaustive fixture campaign is bootstrap-owned.
- Prove production ledger validation rejects absolute external evidence,
  parent traversal, and aggregate evidence beyond 64 MiB before hashing.
- Prove receipt-backed TODO first promotion requires an explicit committed
  evidence blob, preserves its first PASS timestamp for unchanged evidence,
  and carries across fingerprints only while the same blob/hash remains.
- Prove live-worktree evidence modification/removal cannot affect exact-ref
  validation, while a pushed revision that omits its evidence blob fails.
- Prove production bootstrap recording rejects fingerprinted input drift from
  `HEAD`, and compiler/automated evidence is retained in the commit-ready
  tracking tree rather than ignored `build/` state.
- Prove `--ref` rules evaluation ignores a hostile dirty `rules.sdl`, parses the
  committed registry, and fingerprints that policy in producer and consumer.
- On a native Windows host, create two linked worktrees, run
  `powershell -File scripts/setup/install-must-check-hooks.ps1 -Install` in the
  first, then `-Check` and `sh scripts/check/check-hook-installation.shs` from
  the second. Retain the hook hash and both verdicts; until then
  `windows-hook-installation` remains TODO.

Focused command: `sh test/01_unit/scripts/must_check_tiering_test.shs`.

## Traceability

| Requirement | Executable evidence | Scenarios | Status |
|---|---|---:|---|
| REQ-MCT-001, REQ-MCT-003 | `test/03_system/check/must_check_tiering_spec.spl` | push validator | Source present; Stage-4 execution pending |
| REQ-MCT-002, REQ-MCT-005 | `test/03_system/check/must_check_tiering_spec.spl` | bootstrap producer | Source present; Stage-4 execution pending |
| REQ-MCT-004, REQ-MCT-006 | `test/03_system/check/must_check_tiering_spec.spl` | producer-to-consumer and installer | Shell fixture PASS; Stage-4 SSpec pending |
| REQ-MCT-006 Windows | `scripts/setup/install-must-check-hooks.ps1` | linked-worktree install/check | TODO: native Windows host evidence required |

The manual mirror is
`doc/06_spec/03_system/check/must_check_tiering_spec.md`. Regenerate it with
the exact admitted Stage-4 CLI; this worktree has no `bin/simple`, so seed
substitution is forbidden.
