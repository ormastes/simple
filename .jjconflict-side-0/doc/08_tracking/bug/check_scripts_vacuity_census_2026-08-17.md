# scripts/check vacuity census — guards that pass by construction or exit mute

**Date:** 2026-08-17
**Status:** OPEN
**Lane:** scripts
**Related:** `doc/08_tracking/bug/engine_divergence_guard_hardcodes_stale_seed_2026-08-17.md`

## Summary

Census of all 637 `scripts/check/*.shs` against the two vacuity failure modes
named in `.claude/rules/vcs.md`: (a) pinning to a hardcoded, possibly stale
binary, and (b) exiting 0 having checked nothing / exiting non-zero without a
verdict line.

Measured, not inferred, unless marked.

## Census (measured by static scan, 2026-08-17)

| category | count (of 637) |
|---|---|
| A. references `bin/simple` with **no** `SIMPLE_BIN`/`SIMPLE_BINARY` override | 87 |
| B. contains **no** verdict token (`PASS —`/`FAIL —`/`ERROR —`) at all | 478 |
| C. has `PASS —`/`FAIL —` but **no** `ERROR — nothing was checked` path | 37 |
| D. has verdict lines but **no** `--selftest` | 103 |

Restricted to the 67 guards actually **wired** into the pre-push hook /
`land.shs` / `*.sdl` rule groups — i.e. load-bearing:

- **16 wired guards** are in category A (hardcoded `bin/simple`, no override).
  `bin/simple` here resolves to `bin/release/x86_64-unknown-linux-gnu/simple`,
  a Rust seed built **2026-08-16 22:59:37** — a guard pinned to it reports on
  the seed regardless of tree content.
  `check-engine-claiming-specs-use-probe`, `check-env-get-dead-fallback-guard`,
  `check-env-get-nil-abort-guard`, `check-lexer-radix-literal-suffix`,
  `check-lint-binary-staleness`, `check-lint-census`, `check-no-jit-module-drop`,
  `check-predicate-parser-native-build`, `check-render-perf-milestone-gate`,
  `check-simpleos-shell-hello-e2e`, `check-spec-lane`,
  `check-test-tree-divergence`, `check-trait-solver-method-resolution-variant`,
  `check-ui-showcase-layering`, `check-use-warning-oracle-deployed`,
  `check-utf8-slice-audit-live`.
- **12 wired guards** are in category B (no verdict line at all).

## Confirmed fail-open, by execution (exit code read into a variable, never through a pipe)

| guard | exit | last stdout line | defect |
|---|---|---|---|
| `check-cpu-backend-artifacts.shs` | **0** | `cpu_backend_matrix status=SKIP_UNAVAILABLE failures=0 skips=18` | passes having checked **0** of 18 items; no verdict line |
| `check-gpu-backend-layer-evidence.shs` | **0** | `gpu_backend_matrix status=SKIP_UNAVAILABLE backends=5 layers=20 ...` | same shape: every backend skipped, still exit 0 |
| `check-gui-web-2d-completion-criteria-placeholders.shs` | 0 | `gui_web_2d_completion_criteria_report=...` | exit 0, no verdict line |
| `check-x25519mlkem768-cpu-simd.shs` | 0 | `STATUS: PASS ...` | non-conforming verdict format (`STATUS: PASS`, not `PASS — <n> checked`); count never stated |
| `check-bootstrap-platform-handoff-readiness.shs` | **1** | `platform_acceptance_claimed=false` | exits 1 **mute** — same defect class as the trailing-default-param guard |
| `check-lint-census.shs` | 2 | `ERROR: no targets given ...` | exit 2 but non-conforming verdict text |

`SKIP_UNAVAILABLE` returning exit 0 is the highest-severity item here: it is
indistinguishable, to any caller reading only the exit code, from a run that
verified all 18/20 items. Per the project convention, absence of a backend is
absence of evidence and must be `ERROR — nothing was checked` (exit 2), or at
minimum a `PASS` line that STATES `0 checked`, which then trips the
n > 0 rule.

## Why these were not fixed in this pass

Whether `SKIP_UNAVAILABLE` should be ERROR or a recorded-skip PASS is a policy
call about the GPU/CPU-backend and crypto lanes' intent on a machine with no
such hardware, not a mechanical reporting fix. Changing it blind would alter
each guard's verdict, which the scripts lane was explicitly scoped out of.
Filed rather than guessed.

## Fixed in this pass

`scripts/check/check-native-trailing-default-param.shs` only — see that file's
header. Two defects: (1) `set -eu` + bare `test -x bin/simple` exited **1 with
zero bytes of output** from a worktree with no built compiler; (2) a caller's
`FIXTURE`/`SIMPLE_BINARY` env leaked into the `--selftest` recursion, so
`FIXTURE=missing.spl <guard>` aborted with "selftest failed" instead of the
real missing-fixture ERROR. Selftest extended from 7 to 8 fatal fixtures.

## Suggested order of work

1. `check-cpu-backend-artifacts` / `check-gpu-backend-layer-evidence` — the two
   proven fail-opens.
2. `check-bootstrap-platform-handoff-readiness` — mute exit 1.
3. The 16 category-A wired guards — apply the established
   `SIMPLE="${SIMPLE_BIN:-$ROOT/bin/simple}"` pattern plus a refusal to PASS
   when the binary predates the newest source it probes.
