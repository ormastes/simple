# Feature bug: `native-build` has no --keep-going / --error-limit flag

- **Date:** 2026-08-17
- Status: RESOLVED 2026-11-25 (`--keep-going` implemented and wired in the
  pure-Simple driver; verified below. `--error-limit=N` from the proposed
  shape was not implemented — the primary ask is delivered.)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Component:** `src/app/cli/native_build_main.spl`, pure-Simple driver
  (`src/compiler/80.driver/`), Rust seed `native_project` pipeline

## Problem
`native-build` aborts on the first module that fails to compile. There is no
`--keep-going` (compile everything compilable, collect all errors) and no
`--error-limit=N`. Confirmed: no `keep-going` / `error-limit` / `max-errors`
handling anywhere in `src/app/cli/native_build*.spl`; `native_build_main.spl`
is a thin worker wrapper (390 lines) — the per-module compile loop lives deep
in the driver, so this is not a <100-line CLI-side change.

## Use case: bootstrap phase census
During bootstrap triage (e.g. tonight's stage2 exit-1 in simple-boot-snap), the
single most valuable artifact would be a **census of which modules fail and
why** under a given seed/phase binary. Today each run reveals exactly one error
(and, per bootstrap_stage2_silent_exit1_empty_log_2026-08-17.md, sometimes
zero), forcing an O(failures) fix-rebuild loop where each iteration costs a
multi-minute closure load. A `--keep-going` run would surface the whole error
set in one pass, letting stage3-blocker classes (unresolved types, facade
collisions) be fixed in a single batch.

## Proposed shape
- `--keep-going`: continue past per-module frontend/codegen failures; skip link;
  exit non-zero with a summary `N modules failed:` list (module, first error).
- `--error-limit=N`: stop after N failed modules (default 1 = today's behavior).
- Per-module errors must flush to stderr immediately (see the non-tty buffering
  defect in the silent-exit-1 bug doc) so a crash mid-census still leaves the
  errors gathered so far.

Implementing is out of scope for this filing; needs driver-loop changes in both
the pure-Simple path and (for parity) the seed's `native_project` pipeline.

## Verification 2026-11-25 (lane p3-baw, release/1.0.0 @ 1301149fa3f) — RESOLVED

`--keep-going` now exists in the pure-Simple driver and is wired end to end:

- `src/compiler/80.driver/compile_failure_policy.spl:3` —
  `compile_fail_fast_requested(args, env_value, ci_value)` maps
  `--keep-going` → collect-all (fail-fast off) and `--fail-fast` → stop at
  first failure, with `SIMPLE_COMPILE_FAIL_FAST` env fallback; CLI order wins.
- Wired into the native-build driver at
  `src/app/cli/native_build_main.spl:1378` and `:2663`, plus
  `driver_types.spl:1426` and `driver_build/native_mir_fork_v1.spl:307`.
  The MIR-shard path documents "keep-going reports every one"
  (`native_build_main.spl:1743`).
- Landed by `d346dad423d` ("collect host failures with bounded HIR recovery")
  and `6cf7657a80c` ("default to full collection ...").

Executable evidence on this host (seed binary, fixture run — `test` subcommand
is blocked by the known `@representation_boundary` seed limitation, so the
policy fixture was executed directly):

```
$ SIMPLE_LIB=src bin/simple.exe run test/fixtures/compiler/compile_failure_policy/main.spl
PASS compile failure policy
```

The fixture asserts both flag orders, the env fallback, and CI independence.
`--error-limit=N` from the "Proposed shape" section was not implemented; the
filed use case (bootstrap phase census of all failing modules in one pass) is
served by `--keep-going`. Status → RESOLVED.
