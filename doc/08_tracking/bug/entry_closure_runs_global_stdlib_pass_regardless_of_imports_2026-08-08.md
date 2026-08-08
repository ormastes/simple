# `native-build --entry-closure` runs a global stdlib pass regardless of what the program imports

- **ID:** entry_closure_runs_global_stdlib_pass_regardless_of_imports_2026-08-08
- **Date:** 2026-08-08
- **Status:** OPEN, but the "stall" framing is FALSIFIED (see Update 2026-08-08b) —
  it is a slow-but-finite pipeline, `--entry-closure` scoping is CORRECT for both
  the source-load BFS and codegen, and the fixed ~1469-1515-line prefix is the
  native-build WORKER's own interpreter self-bootstrap, unrelated to the target
  program.
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

## Update 2026-08-08b: not a stall, and `--entry-closure` is NOT the scoping bug

Repro: ran the worker directly (bypasses parent stdout buffering, same recipe
as `doc/08_tracking/bug/native_build_entry_closure_slow_2026-07-31.md`) against
a fresh minimal fixture (`use std.common.io.types.{FileMode, SeekFrom}` + a
`print`), with `SIMPLE_COMPILER_TRACE=1` added:

```
env SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1 \
    SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1 SIMPLE_COMPILER_TRACE=1 \
    SIMPLE_EXECUTION_MODE=interpret SIMPLE_BINARY=<binary> \
    stdbuf -oL -eL <binary> run src/app/cli/native_build_worker.spl \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure --entry <fixture> --cache-dir <scratch>/cache \
    -o <scratch>/out.o --emit-object
```

**Three runs cut short by the agent tool's own timeout (~120s each) all landed
at the byte-similar 1467-1469 lines** — this reproduces the "identical stopping
point" observation, but it is an artifact of all three runs sharing the same
wall-clock budget, not evidence of a stall.

**A fourth run given a real 290s budget (`timeout 280` inside, `timeout: 290000`
on the tool call itself — the earlier attempts never actually passed the tool's
`timeout` parameter, so they were silently cut at the tool's 2-minute default)
progressed to 4091 lines before hitting that budget, rc=124.** It moved well
past the previous "stopping point" into new phases:

- `[native-build] closure timing n=1 ... n=2` — the entry-closure BFS itself,
  which runs immediately after the last gc-warning (line ~1469) and visits
  exactly **2 files** (`main.spl`, `src/std/common/io/types.spl`) in 138ms +
  421ms. This matches the fixture's 1 import exactly.
- `[BOOTSTRAP-PHASE] compile:start` / `phase1:load_sources` — a second,
  separate full-pipeline invocation (HIR/MIR lowering) starts after the
  closure BFS.
- `[llvm-direct] module-name <fixture main>` / `function-count 1`, then
  `[llvm-direct] module-name std.common.io.types` / `function-count 8` — the
  LLVM-direct backend codegen (`src/compiler/70.backend/backend/
  llvm_codegen_adapter.spl:53-99`, tag emitted at lines 55-99) processes
  **exactly the 2 closure modules**, 9 functions total — not "far more of the
  stdlib".

**Conclusion: `--entry-closure` is correctly scoped, both for source loading
and for codegen.** The "walks far more of the stdlib than the program
references" framing in the original Conclusion section above is **falsified**
by this trace — the scoping bug hypothesis is dead.

### The actual mechanism for the fixed ~1469-1515-line prefix

It is **not** a pass over the target program at all. It is the native-build
**worker process's own interpreter self-bootstrap**, paid once per worker
invocation regardless of what the target program imports:

1. `run_native_build_worker` (`src/app/cli/native_build_main.spl:217-221`)
   unconditionally forces `SIMPLE_EXECUTION_MODE=interpret` for the whole
   worker subprocess (already known from the 2026-07-31 sibling bug, cause 1).
2. Before the entry-closure BFS can run (`[native-build] closure entry read`
   appears at line ~1476, *after* all the gc-warnings), the interpreter must
   load/execute the **compiler's own** driver and backend module graph
   (`llvm_native_link.spl`, `llvm_codegen_adapter.spl`, etc. under
   `src/compiler/70.backend/`, `80.driver/`) just to get the worker running.
   That graph transitively imports `std.nogc_sync_mut.sffi.llvm_loader`,
   `std.nogc_sync_mut.sffi.dynamic`, `std.nogc_sync_mut.daemon_sdk.{types,lock,
   client,protocol}`, `std.nogc_sync_mut.io.{cuda_sffi,vulkan_sffi}`.
3. Each such import fires `check_gc_family_boundary`
   (`src/compiler/10.frontend/core/interpreter/module_loader_core.spl:522`,
   message templates at lines 553/561: `"[gc-warning] ... module '{module_name}'
   (family: {imported_family}) imported in {no-GC|no-alloc} context (family:
   {importer_family})"`) because the compiler's own driver code runs in a
   `nogc_async_mut`-restricted context while these dependencies live in
   `nogc_sync_mut`. This is why the gc-warnings name daemon_sdk/cuda_sffi/
   vulkan_sffi/llvm_loader regardless of what the *user's* program imports —
   they belong to the compiler's own dependency closure, not the fixture's.

This also explains the original doc's control result precisely: it is
identical between the file-roundtrip fixture and the FileMode/SeekFrom-only
fixture because **both are looking at the worker's own bootstrap, not
anything scoped to their respective imports.**

### Is it a stall or slow-but-finite?

**Slow-but-finite**, confirmed by forward progress past the previous
"stopping point" once given more wall clock. It is not a deadlock/livelock.

Two contributing costs, both consistent with the aggregate-interpreter-
dispatch-tax root cause already documented in
`doc/08_tracking/bug/native_build_entry_closure_slow_2026-07-31.md` (point 2:
"aggregate interpreter dispatch tax across many small operations per file, not
one hot function") but now measured in a *different* phase:

- The fixed worker self-bootstrap prefix (~1469-1515 lines, tens of seconds)
  — compiler-internal module loading under forced interpret, independent of
  program size.
- The LLVM-direct backend codegen phase itself is drastically slower than the
  closure BFS: translating the ONE trivial `main` function took from line 4026
  to ~4078 (52 lines of trace) before codegen for the 8-function
  `std.common.io.types` module even started, and that phase was still only 12
  lines into its own translation when the 280s budget ran out. This is
  `llvm_translate_module_direct_ir` / `llvm_compile_module_direct`
  (`src/compiler/70.backend/backend/llvm_codegen_adapter.spl:41,53`) building
  LLVM IR call-by-call, interpreted, under the same forced
  `SIMPLE_EXECUTION_MODE=interpret` as everything else in the worker — i.e. the
  same class of defect as the 07-31 bug, hitting codegen instead of/in addition
  to the closure walk.

`native_tuple_to_text` (zero stdlib touched) still pays the fixed worker
self-bootstrap prefix (it's unconditional), but its closure and codegen are
each 1 trivial module/function, so the codegen-phase tax the FileMode/SeekFrom
fixture pays (9 functions across 2 modules, including a stdlib type with
`Result`/enum-heavy methods that likely lower to much larger MIR/LLVM IR than a
plain tuple print) is avoided. This was not fully isolated function-by-function
in this session — flagging as the most promising next-investigation target
rather than a proven root cause.

### Verdict on `--entry-closure`

**Not a scoping bug.** Both the source-load BFS and the LLVM-direct codegen
phase correctly process only the entry's reachable modules (2 files, 9
functions) for this fixture. The performance problem is (a) a fixed
per-invocation worker self-bootstrap cost that is unconditional by design
(forced-interpret startup, unrelated to `--entry-closure`), and (b)
interpreter dispatch tax inside LLVM-direct codegen translation, which is also
unconditional by design (the whole worker runs under forced interpret) rather
than a gating failure. Neither is fixed by touching `--entry-closure`'s BFS
logic — this is a performance defect in forced-interpret execution of
compiler-internal passes (self-bootstrap + codegen), not a correctness/scoping
bug. Do not attempt a fix here; this doc is investigation-only per the task
that produced this update.
