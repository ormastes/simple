# `native-build bootstrap_main.spl` appears to stall after `source_closure 655/655 step 1/6 complete` (2026-08-21)

**Status:** diagnosed; diagnosability fix applied (uncommitted); see "What remains".

## Symptom

Every `bin/release/x86_64-unknown-linux-gnu/simple native-build ... src/app/cli/bootstrap_main.spl -o <out>`
on the shared host printed

```
[build] source_closure 655/655 step 1/6 complete
```

and then nothing: the parent `simple native-build` process sat at 0% CPU with
all five threads in `futex_wait_queue` / `hrtimer_nanosleep`, no binary after a
30-min timeout. The same recipe had taken 290s at ~05:10 the same day.

## Evidence (attach-free, live sibling build pid 1573840, 2026-08-21 06:36)

- Parent `simple native-build` (pid 1573840): `State: S`, 5 threads, all
  `futex_wait_queue` except one `hrtimer_nanosleep`, RSS 100 MB. Its only
  open files: the caller's log and `.simple/logs/simple.log.2026-08-21`.
  **It is waiting on its child**, not on a lock file or a daemon socket.
- Child worker (pid 1573852): `bin/release/.../simple run
  src/app/cli/native_build_worker.spl src/app/cli/bootstrap_main.spl -o ... --threads 8`,
  env `SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_EXECUTION_MODE=interpret`.
  `ps`: etime 15:15, **TIME 15:10, 99.5% CPU**; one thread with 91,051
  CPU ticks, RSS 2,998,112 kB flat, minor faults still climbing (~100/s).
  Its stdout/stderr are redirected to `/mnt/data/tmp/simple_out_<ppid>_*.txt`,
  so nothing reaches the caller's terminal until the worker exits.
- No `.cache_scope` lane lock, no daemon socket and no pipe is among the
  worker's fds. `SIMPLE_CACHE_SCOPE` was unset (lane `default`). The test
  daemon backlog path (7a6f6459a81) is not on this code path.

So the "stall" is a **CPU-bound interpreted phase 2 (parse) with no progress
output**: the parent legitimately blocks on the worker; the worker is the Rust
seed tree-walking the self-hosted full frontend over all 655 modules.

## Why it was silent

`src/compiler/80.driver/driver_source_pipeline_parsing.spl`: only the
`--entry-closure` / `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` branch of
`parse_all_impl` emitted `log_build_progress("parse", "files", ...)` per file.
The sibling's recipe (`native-build src/app/cli/bootstrap_main.spl -o ...`,
no `--source src/app --entry-closure`) takes the **plain** loop at the end of
the function, which had zero progress or phase markers. Between
`source_closure ... complete` and `parse N/N complete` a full-tree interpreted
parse (tens of minutes on a box at load 25-30/32) is indistinguishable from a
hang. The 290s run earlier in the day used the entry-closure recipe, which
parses only the entry closure and prints per-file progress.

## Fix (uncommitted)

- `src/compiler/80.driver/driver_source_pipeline_parsing.spl`: the plain parse
  loop now emits `[build] parse i/N step 1/6 <path>` per file (the same
  `log_build_progress` shape as the entry-closure branch) plus
  `log_phase("phase2:parse:file:start ...")`, so `SIMPLE_BUILD_PROGRESS_EVENTS`
  / `SIMPLE_COMPILER_PHASE_PROFILE_FILE` name the exact file being parsed.

## What remains

- The plain (non-closure) recipe is inherently a whole-tree interpreted parse;
  use `--source src/app --entry-closure --entry src/app/cli/bootstrap_main.spl`
  for stage builds. That recipe's wall time on this host is recorded below.
- A genuine hang-vs-slow verdict still requires the progress line; a bounded
  wall-clock watchdog per parsed file is not added here (per-file cost varies
  by >100x under load; a fixed budget would fail closed on a healthy build).

## Run log (this session)

### Run 1 (entry-closure recipe, `SIMPLE_COMPILER_PHASE_PROFILE=1`, started 06:38)

`native-build --source src/app --entry-closure --entry src/app/cli/bootstrap_main.spl`,
`SIMPLE_CACHE_SCOPE=fable-stage3`. Worker reached
`[build] source_closure 655/655 step 1/6 complete` at 06:49:34 (11 min, CPU-bound
startup + closure walk under load 25-30). Then nothing for 10+ min at 100% CPU,
RSS 3.0 GB flat. **Phase profile's last marker:**

```
phase=phase1:load_sources:closure:done scanned=655 logical=941
```

`phase1:load_sources:done` (driver_orchestration.spl, emitted right after
`load_sources_impl` returns and the aot fingerprint is computed) never arrived.
So on this recipe the hot spot is NOT phase 2 parse: it is the tail of
`load_sources_impl` (`driver_source_pipeline_loading.spl` after line 280:
`_driver_module_name_collision`, the owner-copy loop added by c089809a253 at
05:23 -- AFTER the last known-good 05:10 build -- and/or
`driver_native_sources_fingerprint`). The entry-closure recipe and the
sibling's plain recipe share this code, matching both stalling at the same
line. Interpreter micro-probes (`scratchpad/{bytes,iface,push}_probe.spl`) put
each candidate primitive at ms per file, so the culprit is a whole-closure
interaction rather than one slow primitive; run 2 names it with markers.
Killed at 07:03 (25 min CPU past closure:done) to rerun instrumented.

### Instrumentation added (uncommitted)

- `driver_source_pipeline_loading.spl`: `log_phase` markers
  `phase1:load_sources:bulk:done`, `...:collision_check:done`,
  `...:owner_copy:done n=<N>`.
- `driver_orchestration.spl`: `phase1:load_sources:fingerprint:start`.

## ROOT CAUSE (2026-08-21, run 3 + in-process bisect): seed interpreter env-template cache defeated by every local assignment

Run 3 added a marker every 32 sources inside `driver_native_sources_fingerprint`:
the loop advanced uniformly at **1.3-2.5 s per source** (941 sources, so
~30 min for a phase that is 21 s standalone for 1,859 files). Nothing was
stuck; one interpreted function was ~100x slower than it should be.

Reproduced without a build (`scratchpad/bisect/*`, seed `bin/release/x86_64-unknown-linux-gnu/simple`, 05:10 build, sha256 5d35debc...; identical on the 08-19 `.bak2` seed):

| probe (same function, same 130 KB input) | ms |
|---|---|
| function copied into the main file | 86 |
| imported from a tiny scratch module | 72 |
| imported from the real `compiler.driver.driver_aot_output` | **11,426** |
| scratch module = verbatim copy of `driver_aot_native_output.spl` | 11,512 |
| ...with only `use compiler.driver.driver_bootstrap.{...}` kept | 11,529 |
| ...with only `use std.platform.{get_host_os}` kept | 210 |

So the penalty is a property of executing inside an **imported module with a
large imported-global set**, scaling with the import graph. Per-primitive
microbenchmarks (`char_code_at`, `starts_with`, `trim`, `push`, `for`) are
identical heavy vs light; what differs is the cost of an **intra-module call**
(module fn -> module fn): 2000 calls = 11,131 ms heavy vs 163 ms light
(5.5 ms/call vs 0.08 ms), while 5000 calls of a module `pub fn` from `main`
cost 1 ms.

`SIMPLE_INTERP_ENV_CACHE_STATS=1` (threshold lowered to 1,000 in a scratch
build): **`hits=4 misses=4996`** -- the owned-env template cache in
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
(`captured_env_with_live_globals`) missed on essentially every call, so each
call rebuilt the env from `MODULE_GLOBAL_BINDINGS_BY_OWNER` (thousands of
imported names for a driver module). `SIMPLE_INTERP_ENV_CACHE_STATS=2` bump
backtraces (#860000, during the hot loop):

```
 2: interpreter::node_exec::exec_assignment
 3: interpreter::node_exec::exec_node
 4: interpreter::block_exec::exec_block
 5: interpreter::interpreter_control::exec_for
 ...
 8: interpreter_call::core::function_exec::execute_function_body
```

`exec_assignment` (and `place.rs`, `patterns.rs`) did
`MODULE_GLOBALS.with(|cell| { let mut globals = cell.borrow_mut(); if globals.contains_key(name) {...} })`
-- an unconditional `borrow_mut()` on a `GenTrackedCell`, whose `borrow_mut`
bumps the module-globals generation. **Every plain local assignment
(`i = i + 1`) therefore invalidated the env template**, and the next
intra-module call paid a full rebuild. In a light module the rebuild is
cheap, which is why only compiler modules looked slow and why standalone
probes never reproduced it. This is not specific to the fingerprint: phase 2
parse and every later interpreted phase pay the same tax, which is why the
sibling's plain-path build also sat for 27+ min CPU.

### Fix (seed, uncommitted)

- `compiler/src/interpreter/node_exec.rs`, `interpreter/place.rs`,
  `interpreter_helpers/patterns.rs`: peek with `borrow()` and take the write
  borrow only when the name really is a module global.
- `compiler/src/value.rs` `CowEnv::template_key`, `function_exec.rs`: the
  template cache is keyed on `(owner, captured-env base identity)` instead of
  requiring an empty captured env (secondary; the bump fix is what moves the
  needle).
- After: `hits=4990 misses=10`; 2000 intra-module calls 11,131 -> 563 ms;
  48-file in-process fingerprint 48,252 -> 8,608 ms. Remaining gap vs the
  light module (~0.28 ms/call vs 0.08) is the per-call clone of the
  template's `global_bindings` map -- not addressed here.
- Spec: `test/05_perf/interp/intra_module_call_env_cache_spec.spl` (+
  `fixtures/heavy_import_module.spl`): old seed FAILS (`10130ms < 2500ms:
  false`), patched seed PASSES.
- Patched seed built from a scratch copy of `src/{compiler_rust,runtime}` +
  `tools/counterpart` (cargo refuses this jj worktree's `.git`:
  "did not expect repo ... to be bare") into `/mnt/data/.cargo-target-fable`.
  Not deployed to `bin/`.

Commit bisect (stage3-base worktree at c089809a253) became moot: the defect is
in the seed binary's interpreter and is independent of today's commits; the
"290s at 05:10" run could not be reproduced or located in any log.
