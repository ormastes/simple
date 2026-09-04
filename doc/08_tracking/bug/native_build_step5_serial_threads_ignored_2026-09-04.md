# native-build late phases are serial: `--threads` is plumbed end-to-end and then discarded

**Date:** 2026-09-04
**Area:** `src/compiler/80.driver/driver_build/parallel.spl`, `driver_aot_native_output.spl`
**Status:** OPEN (root cause located; fix is blocked on a named prerequisite)

## Measurement envelope

Numbers below are cited from the session that filed this, not re-derived (a long
MCP-server build owned the CPU; per `.claude/agents/perf.md` only bounded probes
were run here).

| item | value |
|---|---|
| binary | `bin/release/aarch64-unknown-linux-gnu/simple`, 154,560,904 B, 2026-09-04 14:46:17 |
| host | aarch64 Ubuntu 24.04, 20 cores, 121 GB RAM |
| load / concurrency at probe time | load avg 1.51, 4 concurrent `simple` processes |
| host memory pressure | 9 GB used / 70 GB free / 112 GB available — **not under pressure** |

Observed build: MCP server, 102 units, `--source src/compiler --source src/app
--source src/lib`, `--threads 20`.

| phase | wall |
|---|---|
| steps 1-4 (load_sources -> parse -> hir -> monomorphize -> lower_to_mir) | ~27 min |
| reported as step 5 (`aot:lower_to_mir` / native codegen) | **>1h33m, did not finish**; blew the 7200 s worker timeout. See the phase-identification section below — this is either step 4/6 (mir) or step 5/6 (native_compile); both are serial. |

So **>75% of wall clock is in one phase that never uses more than one core.**

## Which phase is "step 5" — match it against your own log

`log_build_progress` carries an explicit `(step, total)` pair, and the phase
label `aot:lower_to_mir` comes from a *different* stream (`log_phase`). They do
not line up, so identify the stalled phase from the last `[build] N/6` line you
actually saw:

- `4/6 mir` -> MIR lowering, `driver_pipeline_lowering.spl:262-311` (`:306` passes `4, 6`).
- `5/6 native_cache` / `native_compile` / `link` -> per-module LLVM emission,
  `driver_aot_native_output.spl:1041`, `:1165`, `:1311`, `:1381` (all pass `5, 6`).

If the last `log_phase` line was `aot:lower_to_mir:start` with no matching
`:done`, the stall was step 4, not step 5. **Both phases are serial and both fix
sites are recorded below**, so the finding holds either way; only the fix site
differs. This doc does not have the original run's log and does not assert which
one it was.

## Root cause — `ParallelBuilder.build()` has no parallelism at all

`src/compiler/80.driver/driver_build/parallel.spl:389` `me build(compile_fn)` has
two branches and **both are sequential**:

- `:416` sequential branch — taken when `deterministic` or `total < parallel_threshold`.
- `:480` "parallel" branch — taken otherwise. It chunks the ready set into groups
  of `max_workers`, marks the chunk in-progress, and then at **`:510-513`** runs

  ```
  while chunk_idx < chunk_end:
      val build_unit = ready[chunk_idx]
      val result = compile_fn(build_unit.path)
  ```

  a plain serial loop with **no spawn, no thread, no concurrency**. The outer
  `batch_idx = chunk_end` walk covers every unit, so total work is identical to
  the sequential branch. `max_workers` moves a chunk boundary and nothing else.

Until this change it also printed `[PARALLEL] batch-concurrent mode, {n} workers`
under `--verbose`, which actively asserts concurrency that does not exist.

### The full `--threads` chain, ending in a discard

| # | site | what happens |
|---|---|---|
| 1 | `src/app/io/_CliCompile/native_build.spl:490-506` | `--threads` / `--jobs` / `-j` parsed |
| 2 | `native_build.spl:657` (and `compile_targets.spl:921`) | exported as `SIMPLE_NATIVE_BUILD_THREADS` |
| 3 | `driver_aot_native_output.spl:248` `driver_native_build_threads()` | read back |
| 4 | `driver_aot_native_output.spl:1211-1222` | -> `ParallelBuildConfig.num_threads` |
| 5 | `parallel.spl:130-139` `effective_threads()` | resolved; **auto-detect is capped at 8**, so `--threads 20` is honoured only as a literal 20 and an unset value becomes 8, never 20 |
| 6 | `parallel.spl:510` | **discarded** — used as a chunk size for a serial loop |

Two extra clamps worth knowing: when a `BackendSession` is admitted, threads are
forced to `1` outright (`driver_aot_native_output.spl:1211-1214`, stateful
adapter with no reentrancy capability); and `build()` is entered with
`parallel_threshold: 4`, so <4 uncached modules take the sequential branch by
design.

### The real parallel implementations exist and are dead code

`build_parallel()` (`parallel.spl:553`) and `build_supervised()` (`:697`) are the
genuine `rt_process_spawn_async` implementations. `grep` for `.build_parallel(` /
`.build_supervised(` across `src/` returns **zero callers**. `build()`'s own
comment at `:399-405` states why: `compile_fn` closes over the caller's
**in-memory frozen MIR capsules**, which a child process cannot receive. Wiring
the process path needs a one-module compile CLI so `spawn_fn` has something to
launch — already tracked as `doc/03_plan/infra/unstable_mode_build_side.md`.

Step 4/6 is serial for a different and harder reason: the MIR loop at
`driver_pipeline_lowering.spl:262-311` shares ONE mutable `MirLowering` whose
`.symbols` is reassigned per module (`:283`) after a cross-module
`prescan_module_struct_names` prepass (`:271-277`). Parallelising it needs
`MirLowering` changes under `src/compiler/50.mir/**` plus MIR serialisation.

## `--backend llvm` vs `--backend llvm-lib` — alias on the seed, REAL on the pure-Simple side

They are **not** the same thing, and it depends on which compiler you are in.
An earlier draft of this doc got this wrong by reading only the seed.

**On the Rust seed CLI it is a pure alias:** `src/compiler_rust/driver/src/cli/native_build.rs:69`
normalises `"llvm-lib" | "llvmlib" => "llvm"` before parsing. So on the seed the
flag genuinely does nothing.

**On the pure-Simple side it selects a distinct codegen adapter** — this is the
path the interpreted worker actually runs:

- `backend_helpers.spl:249` and `:369` map `llvm-lib`/`llvmlib` to
  `BackendKind.LlvmLib`, a separate variant from `BackendKind.Llvm`.
- `get_effective_backend_name()` (`backend_helpers.spl:562-563`) preserves
  `"llvm-lib"` rather than folding it.
- `src/compiler/70.backend/backend/llvm_lib_backend.spl:1-9` — `LlvmLibCodegenAdapter`
  drives the **LLVM C API loaded dynamically via DynLib: "no external tools
  needed (no llc, no opt)"**, MIR -> in-memory IR -> `LLVMTargetMachineEmitToFile`.
- `src/app/io/_CliCompile/native_build.spl:338` calls it "the pure Simple LLVM
  pipeline"; `:846` requires `--backend=llvm-lib` on that command path.

So the original timeout hint's "in-process backend" **was pointing at something
real** — `llvm-lib`, which avoids per-module external tool invocation. It is
only merged with `llvm` for *cache hashing* (`compile_options_hash.spl:238`) and
for the *link* step (`driver_aot_native_output.spl:828`, `:1383`), never for
per-module codegen dispatch. The bootstrap uses `--backend llvm`.

Worth knowing separately: worker-vs-in-process is selected by
`native_build_should_use_worker()` (`src/app/cli/native_build_main.spl:219-229`)
— `SIMPLE_NATIVE_BUILD_FORCE_WORKER`, `SIMPLE_BOOTSTRAP`,
`SIMPLE_EXECUTION_MODE=interpret`/`interpreter`, **or the mere presence of
`--timeout`**. That is orthogonal to `--backend`.

Note also `driver_aot_native_output.spl:1211-1214`: an admitted `BackendSession`
forces `num_threads` to 1. If `llvm-lib` is admitted as a session-backed provider
it takes the serial lane by construction, so switching backends is not by itself
a parallelism fix.

## Memory

Not a leak, and the two knobs named in the original brief are not memory knobs:

- Source contents are **already reclaimed unconditionally** on the streaming path
  (`driver_hir_pipeline_lowering.spl:432-437`). `SIMPLE_KEEP_SOURCE_CONTENTS=1`
  only **skips** that reclaim; it is a diagnostic gate added 2026-09-03 for the
  ZeroKind corruption investigation, not a tuning option.
- What is retained through steps 4-5 is all 102 `ctx.hir_modules` plus an
  accumulating `ctx.mir_modules` (`driver_pipeline_lowering.spl:301`), as
  interpreter heap objects. **Code-reading inference, UNMEASURED:** the
  interpreter's per-node object overhead is the likely multiplier turning that
  into tens of GB. No heap profile was run — `SIMPLE_COMPILER_PHASE_PROFILE=1`
  needs a real build, which the bounded-probe constraint forbade here. Confirm
  before acting on it.
- Eviction already exists behind `--low-memory`: HIR at
  `driver_aot_pipeline.spl:92-94`, per-module MIR at
  `driver_aot_native_output.spl:1007`, `:1118`, `:1292`. `--low-memory` is parsed
  on the `cli_native_build` path (`compile_targets.spl:609`).

So the memory finding is **"the knob exists and the invocation does not pass
it"**, not a code defect. The host was at 9/121 GB used during this
investigation — no pressure. Existing budget:
`scripts/check/check-bootstrap-stage3-memory-admission.shs`.

## Proposed fix (not implemented here)

1. **Prerequisite:** a one-module compile CLI (`doc/03_plan/infra/unstable_mode_build_side.md`)
   so a frozen capsule can be addressed by name from a child process.
2. Then point `driver_aot_native_output.spl:1231` at `build_parallel()` /
   `build_supervised()` instead of `build()`. Both already exist and are tested
   shapes; only the `spawn_fn` is missing. This is the change that converts the
   >1h33m phase into an N-way one, IF the stall was step 5/6.
3. Raise or remove the `effective_threads()` cap of 8 (`parallel.spl:137`) once
   units are processes with independent LLVM contexts, guided by
   `shard_mem_clamp` the way parse/HIR sharding already is.

Note that steps 2-3 of the pipeline are **already** process-sharded and do honour
`--threads` — `run_parse_shards` / `run_hir_shards`
(`native_build_main.spl:388-427`, `:542`, `:625-636`). Step 5 is the one phase
that was never given the same treatment. That is the whole finding.

## What was changed in this session

Diagnostics only — no behaviour change:

- `parallel.spl:480-497` — the `[PARALLEL] batch-concurrent mode, N workers`
  print no longer claims concurrency. It now states that units compile
  sequentially and that `--threads` sets chunk size only, matching the
  honest-downgrade notice this same function already emits for unstable mode
  (`:406-411`).
- `native_build_main.spl:688-693` — the timeout hint is now phase-agnostic: it
  tells the reader to match the last `[build] N/6` line, names steps 4 and 5 as
  serial with their file:line, and replaces the vague "in-process backend" with
  the concrete `--backend llvm-lib` alongside `--low-memory` and cache warming.

Neither edited file was linted: `bin/simple lint` costs ~12 s startup plus a
content-driven per-declaration cost, which exceeds the bounded-probe budget this
session was held to. Both edits are string/comment-only. The multi-line
`print "..." + "..."` continuation in `parallel.spl` matches, in shape, the
existing precedent at `parallel.spl:406-411` in the same function; the `eprint`
strings added to `native_build_main.spl` contain no `{}` interpolation at all.
