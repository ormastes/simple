# `native-build --entry-closure` runs a global stdlib pass regardless of what the program imports

- **ID:** entry_closure_runs_global_stdlib_pass_regardless_of_imports_2026-08-08
- **Date:** 2026-08-08
- **Status:** OPEN — falsification is solid; the pass itself is not yet identified
- **Severity:** high — it is the blocker for the last unfenced AOT audit row, and
  it makes AOT compile time roughly independent of program size for any program
  that touches the stdlib at all.

## Symptom

`native-build --entry-closure` of `test/fixtures/rt_io_file_roundtrip/main.spl`
never completes. Two independent cold attempts (`timeout 560`, `timeout 590`)
both returned **rc=124 with an EMPTY cache dir (0 files)** and both halted at the
**identical last log line** (a `daemon_sdk.protocol` gc-warning), ~1512 lines in.

Two cold runs stopping at the same point with zero cache output is a stall or a
very slow fixed phase, not "needs more wall clock".

## What it is NOT — two hypotheses killed by controls

**Not host load.** `test/fixtures/native_tuple_to_text/main.spl` — another AOT
fence fixture — native-builds **successfully in 164s at comparable or worse load**
(1-min average 43 → 51). The machine is capable of native-build.

**Not this fixture's import surface.** This was the working hypothesis and it is
**falsified**. The fixture has only 2 `use` lines, and neither
`src/lib/nogc_sync_mut/io/file.spl` nor its siblings (`file_ops.spl`,
`file_discovery.spl`, `file_shell.spl`) reference `cuda_sffi`, `vulkan_sffi`,
`daemon_sdk`, or `llvm_loader` at all — despite all of those appearing in the
build log.

**The decisive control:** a brand-new fixture containing *only*

```
use std.common.io.types.{FileMode, SeekFrom}
```

plus a trivial `print` — no `FileHandle`, no `File`, nothing from `io/`, nothing
that does any file I/O — stalls **identically**: same rc=124, same **1515-line
log**, and a **byte-identical last 5 lines** (confirmed with `diff`).

## Conclusion

Touching essentially **any** `std.*` module triggers a fixed, deterministic global
pass that walks far more of the stdlib than the program references, always
reaching the same stopping point regardless of program size. The gc-warnings that
dominate the log name the three runtime families:

```
[gc-warning] Higher-layer module 'std.nogc_sync_mut.daemon_sdk.*' (family: nogc_sync_mut)
             imported in restricted context (family: nogc_async_mut)
```

so the pass is plausibly family-boundary / duplicate-symbol scanning across
`nogc_sync_mut` / `nogc_async_mut` / `gc_async_mut`. **That is a hypothesis about
which pass, not a measured fact** — the falsification above is what is solid.

This contradicts `--entry-closure`'s documented promise to walk only the entry's
reachable modules (`src/app/cli/bootstrap_main.spl:165`).

`native_tuple_to_text` builds in 164s precisely because it touches **zero** stdlib
modules — the pass is skipped entirely rather than being fast. That is the whole
difference between the two fixtures.

## Why this matters beyond one fence

- It is the reason the AOT half of the `rt_io_file_*` row cannot be fenced. See
  `scripts/check/check-rt-io-file-native-jit-stub.shs` (header) and
  `doc/09_report/infra/aot_lane_regression_fence_audit_2026-08-07.md`.
- If AOT compile time is dominated by a fixed global pass, then **every**
  stdlib-touching AOT build pays it, and per-module incremental caching cannot
  help — which is consistent with the separately-recorded finding that a one-file
  edit reuses 0/3 objects
  (`scripts/check/check-native-object-cache-granularity.shs`).

## Next steps for whoever picks this up

1. Identify the pass. Run with `SIMPLE_COMPILER_TRACE=1` and find what executes
   between the last gc-warning and the stall. The log stopping at a consistent
   line number across runs makes this tractable.
2. Determine whether it is a genuine stall (deadlock/livelock) or merely very
   slow. Two runs halting at the identical line hints at the former, but neither
   run exceeded 590s, so "slow" is not excluded.
3. Check whether `--entry-closure` is meant to gate this pass and does not.

**Do not** attempt to fix this by shrinking a fixture's imports — the control
above proves that cannot work.

## Measurement caveat

The agent Bash tool caps at 600000ms, so no attempt has actually tested a 900s
window. `rc=124 at ≤590s` does **not** establish that 900s also fails.
