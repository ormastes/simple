# `--entry-closure` BFS averages ~1-2s/file (not "cheap") — localized, not fixed

- **Status:** localized only; landed a level-gated timing probe, no behavior change.
- **Symptom:** `_native_build_entry_closure` in `src/app/io/_CliCompile/compile_targets.spl`
  (the `--entry-closure` BFS import-resolution walk) measured at ~2.2s/file average crawling a
  484-file closure (~18 minutes total), dominating a 22-minute `native-build` run. The function's
  own comment calls this "a cheap, purely-syntactic scan."
- **Repro:** run the worker directly (bypasses the parent's stdout buffering, which is why this
  went unnoticed — the parent only prints the worker's captured output after it exits):
  ```
  env SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1 \
      SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1 SIMPLE_EXECUTION_MODE=interpret \
      SIMPLE_BINARY=<binary> stdbuf -oL -eL <binary> run src/app/cli/native_build_worker.spl \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure --entry src/app/cli/main.spl \
      --cache-dir <scratch>/cache -o <scratch>/out.o --emit-object
  ```

## Root mechanism (verified empirically)

1. **The worker unconditionally runs under the tree-walking interpreter.**
   `run_native_build_worker` (`src/app/cli/native_build_main.spl:217-221`) does:
   ```
   val mode = env_get("SIMPLE_EXECUTION_MODE")
   if mode == nil or mode == "":
       env_set("SIMPLE_EXECUTION_MODE", "interpret")
   ```
   unconditionally, for the whole worker subprocess — including the closure BFS, which does not
   need the protection this exists for (see point 3). This is already noted, for a different
   symptom (a fail-open preflight check paying the same tax), in the comment block at
   `native_build_main.spl:267-299` referencing
   `doc/08_tracking/bug/native_build_scoping_and_bootstrap_readthrough_2026-07-30.md`.

2. **Measured per-file cost correlates with file size, not BFS/queue position.** 57 files
   traced with the new `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1` probe (interpret mode, host
   load 12-22 from unrelated concurrent sessions):

   | content_len bucket | avg elapsed | n |
   |---|---|---|
   | <1 KB | 216 ms | 10 |
   | 1-10 KB | 640 ms | 24 |
   | >10 KB | 2.39 s | 23 |

   Max single file: 8.13s for a 64 KB file (16 imports). Sorting by `content_len` shows a
   near-monotonic cost trend; sorting by BFS position `n` or live `queued` size shows **no**
   trend (first-28-files average 1.42s vs. rest-of-run average 1.13s — flat to slightly
   *decreasing*, not growing). This rules out an O(n²) accumulation bug in the BFS's own state
   (`discovered` bucket-set, `queue`/`result` arrays) as the driver — those structures are not
   the bottleneck.
   Small/empty files still cost 100-700ms (a fixed floor), consistent with per-call interpreter
   dispatch tax on the dozens of string/dict/array method calls the loop body makes per file
   regardless of content (bucket-set add/has, dict cache lookup, `rt_file_exists`/
   `rt_file_read_text`, line-split scan) — not any single quadratic hot spot found in the scan
   code itself.

3. **Switching off forced-interpret does not help — JIT is worse here.** Overriding
   `SIMPLE_EXECUTION_MODE=jit` (unset) for the same command reached only 25 files in 90s (vs. 50
   files in 90s under `interpret`), because parts of the worker's own module graph cannot JIT at
   all: `[INFO] JIT compilation failed, falling back to interpreter: ... function
   'HirLowering.format_type' creates a lambda/closure; the JIT closure ABI does not tag-box
   lambda arguments ... deferring to interpreter`. So this is not a one-line "just don't force
   interpret" fix — the forcing exists because JIT is actively broken for (unrelated) parts of
   the same process's module graph, and the closure walk pays that cost as a bystander because it
   shares a process/mode with the rest of the worker.

## Contained follow-up candidates (not applied — out of scope for this task)

- `_driver_entry_import_module_paths_cache` (`src/compiler/80.driver/driver_source_loading.spl:471`)
  is a `Dict<text, [text]>` keyed by the **full file content string**. In a single `--entry-closure`
  walk each physical file is visited once, so this cache never pays off (zero hits) but still
  forces a hash/compare over the whole (up to 64 KB+) content string on every call — pure
  overhead in this call path specifically.
- `_driver_resolve_numbered_compiler_import` (`driver_source_loading.spl:583`) probes up to 17
  prefix rewrites, each trying up to ~9 `rt_file_exists` candidates (extension × root
  combinations) before giving up — up to ~150 stat-shaped calls for one *first-occurrence*
  `compiler.*` import. `resolve_cache` memoizes by segment key so repeats are free, but the
  first hit of each unique compiler import pays the full cascade, and every one of those calls is
  itself interpreted.
- Neither of these was isolated as the dominant single cause; the size-correlated, floor-bounded
  shape of the data (point 2 above) points at aggregate interpreter dispatch tax across many
  small operations per file, not one hot function. A structural fix (run the closure walk under a
  faster engine while keeping the rest of the worker on forced-interpret) would need the
  worker to change execution mode mid-process, which is architecturally nontrivial and out of
  scope here.

## What landed

`_native_build_entry_closure` gained a default-off `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1`
probe (in addition to the existing `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1` 25-file checkpoint) that
prints per-file `elapsed_us`, `imports`, `content_len`, and `queued` so this shape can be
re-verified without re-deriving it from scratch. No behavior change when unset (the default).
