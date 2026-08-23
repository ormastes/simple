---
name: unstable-build-fixes
description: Use when a Simple bootstrap/native-build is unstable, slow, or exposes many errors and needs an inventory-to-end sweep, grouped root-cause fixes, isolated parallel mini builds, cache-preserving retries, or fail-fast release gates until a verified executable is produced.
---

# Unstable Build Fixes

Goal: produce the requested Simple executable without throwing away useful cache.

## Modes

- Use **fail-fast** for normal CI/release gates and when one hard failure prevents
  later work from being observed. Stop at the first real root cause.
- Use **inventory-to-end** when the build is failing one file at a time, many
  errors are expected, or the user asks to find as many bugs as possible. Freeze
  the source/runtime/compiler identities and a deterministic manifest, check the
  entire requested scope in isolated processes, and do not edit until the sweep
  reaches the end.
- Label all evidence with compiler executable, execution mode, target, host, and
  manifest. A Rust-seed/static/check sweep is diagnostic evidence, not proof that
  a pure-Simple Stage 4 binary builds or runs.

## Rules

- Profile the whole execution path before optimizing a slow leaf. Identify the
  actual executable, host/runtime, execution mode, orchestration overhead, and
  semantic work. In particular, a checker launched from source may be evaluated
  by the Rust interpreter; compare that path with a cached compiled checker
  before attributing latency to checking logic, Rust, Python, AOP, or linking.
- Measure one representative file cold and warm, then a small manifest. Record
  wall time, max RSS, files/second, exit status, and output parity. Optimize the
  dominant layer first; do not infer a per-file compiler cost from end-to-end
  source-run startup time.
- Keep one main cache-backed build as source of truth:
  `--cache-dir build/bootstrap/native_cache --mode dynload`.
- Do not delete the cache between retries unless a concrete stale-cache bug is proven.
- Do not run parallel writers into the same cache dir. Use isolated shard caches:
  `build/mini_cache_<entry>`.
- If a source fix lands while a build is still before object output, prefer letting it fail or finish. Restart only when no cache/output can be lost.
- Keep every log under `build/mini_builds/` or `build/native_probe/`.
- Publish low-overhead progress as manifest total, completed, failed, remaining,
  throughput, and ETA. Persist per-item status so an interrupted sweep resumes
  instead of restarting successful work.
- Set `SIMPLE_NO_STUB_FALLBACK=1` for every candidate or verification build;
  a binary containing generated unresolved stubs is debug evidence only.
- At an LLVM failure, inspect the earliest broken IR boundary before changing
  the backend. An unresolved owner or undeclared `GlobalLoad` is HIR/MIR input,
  malformed `.ll` is text generation, rejected bitcode is LLVM validity, and
  verified bitcode rejected by `llc` is target code generation. During a
  seed-assisted bootstrap, `SIMPLE_LLVM_DIAGNOSTIC_DIR=<dir>` preserves partial
  `.ll`/`.bc`, MIR, and an error receipt. Add
  `SIMPLE_LLVM_DIAGNOSTIC_MODE=all` only when complete successful-module
  artifacts justify its I/O cost. Replay text/bitcode with
  `sh scripts/check/replay-llvm-artifact.shs <module.ll|module.bc> <out-dir>`.
  Rust-seed artifacts are diagnostic only; acceptance still requires the
  produced pure-Simple executable and its smoke gates.
- Prefer the pure-Simple LLVM boundary when it is reachable:
  `SIMPLE_LLVM_BITCODE_DEBUG=1 SIMPLE_KEEP_LLVM_IR=1 <pure-simple> native-build
  --backend llvm ...` must run Simple MIR-to-text emission, `llvm-as` to `.bc`,
  `opt -passes=verify`, then `llc` on bitcode. The first failing stage owns the
  bug category. Use the Rust seed capture only when an earlier bootstrap stage
  prevents the pure-Simple path from running.

## Inventory-To-End Loop

1. Freeze the source revision, compiler/runtime identities, target, roots, cache
   paths, and deterministic file/task manifest. Start or keep one main build only
   if it can make useful cache/object progress independently.
2. Run the whole diagnostic manifest with the compiled checker, bounded batches,
   per-process timeouts, and durable results:
   ```bash
   python3 scripts/check/compiled-check-tree.py --checker=<compiled-simple-check> \
     --root=src/compiler --root=src/lib --root=src/app \
     --output-dir=build/mini_builds/full-tree-check --workers=<jobs> \
     --batch-size=64 --timeout=<seconds>
   ```
   Continue after failures. Retain `manifest.tsv`, `run.json`, and every batch or
   isolated-file result, including timeouts and crashes. Use `--resume` only with
   the same frozen checker and manifest. The legacy
   `bootstrap-diagnostic-sweep.shs` is suitable for short fail-fast probes, but
   its temporary rows are not inventory-to-end evidence.
3. Normalize the first real diagnostic and group repeated symptoms into root-cause
   categories. Separate independent bugs from cascades, duplicates, warning-only
   output, and unavailable-platform results.
4. Record and claim each category in the bug database before edits. Assign one
   independent category to one agent; never assign one agent per repeated file,
   and never let agents write the same owner files or cache concurrently.
5. Fix the smallest shared owner/root cause for all affected files in one batch.
   Add an exact reproducer plus adjacent/similar-situation regression tests for
   every category. A batch may span many symptoms, but still needs one merge
   owner to review shared compiler/runtime changes.
6. Rerun only failed shards first with their existing caches. Then run the main
   build once with its existing cache:
   ```bash
   SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib \
     --entry-closure --threads 8 --cache-dir build/bootstrap/native_cache --mode dynload \
     --entry src/app/cli/_CliMain/main_and_help.spl -o build/native_probe/simple
   ```
7. If the CLI is produced, sanity-check it, then exercise as many supported
   commands/features as the artifact and host allow. Categorize new runtime bugs
   and repeat the failed-shard-first cycle.
8. Stop after at most three verify/fix cycles. Success requires the scoped
   inventory to be complete, every unique category fixed or explicitly recorded
   as blocked/unavailable, failed shards green, and the requested artifact and
   sanity gates green. Do not rerun an already-green criterion.

Useful independent mini-build shards include:

   - `src/app/cli/bootstrap_main.spl` -> `build/mini_cache_bootstrap`
   - `src/app/cli/native_build_main.spl` -> `build/mini_cache_native_build`
   - `src/app/mcp/main.spl` -> `build/mini_cache_mcp`

If a complete per-file sweep is too expensive, do not silently switch to
one-error-at-a-time repair. Preserve the manifest and resume state, report the
measured throughput/ETA, and use a coarser module/root manifest that still
reaches the end of the requested scope.

## Patterns

- If `--entry-closure` is CPU-bound before HIR/driver debug output, inspect the
  closure queue first. Shared imports need a queued-set as well as `seen`;
  checking only processed files can enqueue the same module many times.
- If LLVM reaches `llc` or link with an undefined runtime helper, fix the call
  name and declaration together. For example, `get_args`/`get_cli_args` should
  lower to the exported runtime symbol `rt_get_args`, and every text/lib LLVM
  declaration list must include that symbol.
- If a bootstrap fast path mirrors a normal lowering path, preserve the normal
  scope and state side effects (`push_scope`/`pop_scope`, `has` flags, call-frame
  snapshots). Fast paths may avoid fragile payload extraction, but not semantic
  state.
- When a self-hosted compiler rejects an extern/runtime value that passes a
  core-C self-check, inspect the candidate symbol provider with `nm`/`objdump`.
  Stage 2/3 may execute the Rust runtime plus `runtime_memory.c`; keep ownership
  helpers behaviorally paired with `runtime_native.c` instead of assuming the
  final core-C bundle is already authoritative.
- If `/proc/<pid>/environ` proves an arena/config flag is set but interpreted
  module globals revert after nested calls, inspect return-side frame sync.
  Callee-refreshed overlays are readable snapshots, not caller writes; never
  copy them back over newer owner-global state unless the caller mutates them.
  Carry updates with their owner through foreign-module frames, then refresh
  the matching caller so an outer dirty snapshot cannot clobber a deeper write.
- If owned and imported parallel arenas diverge after reset, preserve the
  imported alias's `(defining owner, source name)` in the frame. Bare-name
  return sync can persist local resets while silently discarding imported ones.

## Error Triage

Use:
```bash
rg -n "error:|FAILED|Failed|native-build worker|Bootstrap LLVM|llc failed|unknown extern|undefined|mismatch" <log>
find <cache-dir> -name '*.o' | wc -l
```

Ignore warning-only output unless it is the only changed behavior.

## Field notes 2026-08-23 (macOS arm64)

- Symptom: stage2 native-build exit 1, "Stage4 runtime capsule defines
  owner-provided runtime symbols STRONGLY (the outer runtime could not override
  them): _rt_heap_live_bytes, _rt_heap_peak_bytes". Cause: Apple llvm-nm prints
  weak *definitions* as `T` in POSIX `-g -p` output; the weakness only appears
  in the `-m` flag field as `weak external`. The seed's
  `archive_weak_global_symbols`
  (src/compiler_rust/compiler/src/pipeline/native_project/tools.rs) and
  `read_global_symbol_types`
  (src/compiler_rust/compiler/src/pipeline/native_project/linker.rs) accepted
  only GNU/ELF `W`/`V`, so every `__attribute__((weak))` C fallback was misread
  as STRONG and the stage-4 capsule gate refused the link. Fix: pass `-m` to nm
  on macOS hosts and normalize `weak external`/`weak reference` lines to weak in
  both parsers. Verify: `nm -m` shows `weak external _f` where `nm -g -p` shows
  `T _f` for the same weak definition.
- Symptom: "FAILED FILES (1): src/compiler/10.frontend/core/__init__.spl =>
  timeout (300s)", "native-build aborted: 1 file(s) failed to compile". The
  300s is a hard default `file_timeout: 300` in
  src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:537 (config
  builder `.timeout(secs)`); there is no env var or CLI flag override. The
  `--timeout` flag in `simple native-build --help` is the *worker subprocess*
  timeout (default 7200), a different knob owned by
  src/app/cli/native_build_main.spl. `--jobs=full` on a 10-core/24GB host
  saturates CPU (~950%) and can push big files past 300s; retry with
  `--jobs=half` — the native cache resumes and only failed/uncached files
  recompile. Same file passing with fewer jobs = contention, not a compile hang.
- Stale bootstrap locks: a killed bootstrap leaves
  `build/.simple-bootstrap-locks/.output-*.lock`/`.claim-*` files; the next run
  fails fast with "timed out waiting for bootstrap output ownership". Kill the
  stale process tree (verify PPID first) and remove the stale lock files.
- Killing a bootstrap wrapper does NOT kill its children: orphaned
  cargo/rustc/native-build processes survive with PPID 1. Check `ps -o pid,ppid`
  before killing anything mid-build; killing the wrong child aborts a healthy
  build.
- native-build buffers stdout/stderr to non-tty until completion: a 0-byte
  stage2-native-build.log does NOT mean stalled. Judge liveness by
  `build/bootstrap/bootstrap-progress.log` milestones and `ps` CPU, not the log.
  Progress-monitor `tree_processes=0` samples are an artifact during
  single-child phases; rustc/simple at ~950% CPU means `--jobs=full` is working.
- jj colocated-repo pitfalls: `jj rebase -r X -d Y` rebases X and its
  DESCENDANTS only, re-parenting X directly onto Y — ancestors of X are left
  behind (stack silently dropped). Move a stack with
  `jj rebase -s <stack-root> -d Y`. A commit showing `(empty)` after rebase
  means its diff collapsed (e.g. a revert whose target files do not exist on the
  new base) — re-apply it. `git worktree remove/prune` in a colocated repo does
  not snapshot jj state; prefer jj-native operations.
