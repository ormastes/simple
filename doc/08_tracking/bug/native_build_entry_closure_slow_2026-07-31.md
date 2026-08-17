# `--entry-closure` BFS averages ~1-2s/file (not "cheap") — localized, not fixed

- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  removed); the other was measured and found to be a no-op on this path, left alone.
  See "Follow-up: contained candidates resolved (2026-07-31)" at the bottom.
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

## Follow-up: contained candidates resolved (2026-07-31)

Both candidates from the section above were re-measured against the same repro (worker run
directly, `--source src/compiler --source src/app --source src/lib --entry-closure --entry
src/app/cli/main.spl --emit-object`, `SIMPLE_EXECUTION_MODE=interpret`, host load 7-15 from
unrelated concurrent sessions, first ~80 files of the closure sampled per run since the full
484-file closure still takes ~18 min).

### 1. `_driver_entry_import_module_paths_cache` — real, fixed

Confirmed zero hits on this path exactly as suspected: every caller (`_native_build_entry_closure`
via the BFS's own `discovered` dedup, and the `phase1:load_sources` closure scan in
`driver_source_pipeline_loading.spl` via its own `closure_scanned_paths` dedup) already visits each
physical file at most once per call site, so the content-keyed `Dict<text, [text]>` cache in
`_driver_entry_import_module_paths` (`driver_source_loading.spl`) paid a full hash of the whole
(up to 64 KB+) content string twice per call — `contains_key` + insert — for a permanent miss.
Rekeying by path was not possible without changing the function's arity: the public
`_driver_entry_import_module_paths(content)` single-arg call form is exercised directly with
content-only literals (no backing file/path) by
`test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl` and
`test/01_unit/compiler/driver/native_entry_closure_gate_source_spec.spl`, and the same literal
single-arg call site is depended on (with 2 already-pre-existing-red assertions, unrelated to this
change) by `test/01_unit/app/cli_native_build_main_contract_spec.spl` and
`test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl`. Removed the cache instead — the
function is pure in `content`, so behavior is unchanged either way.

Per-bucket timing, same repro, before vs. after (n = files captured in each ~2-minute sample
window; content_len buckets as in the table above):

| bucket | before (n) | after (n) |
|---|---|---|
| <1 KB | 154 ms (15) | 147-148 ms (15) |
| 1-10 KB | 505 ms (32) | 518-519 ms (32-33) |
| >10 KB | 2402 ms (32) | 2262-2306 ms (32) |

(Two independent after-runs shown for the >10 KB bucket to bound noise: 2262 ms and 2306 ms.)
~4-6% win concentrated in the >10 KB bucket, where the two extra full-content hashes cost the
most; <1 KB and 1-10 KB are flat within run-to-run noise, as expected since hash cost scales with
content length. Modest, not the dominant cost (matches point 2's conclusion above: aggregate
interpreter dispatch tax across many small per-file operations, not one hot function) but real and
free of correctness risk. Verified the BFS visits the identical file set in the identical order
before and after (diffed the full `file=` sequence of the first 79 files across a before-run and an
after-run: byte-identical).

### 2. `_driver_resolve_numbered_compiler_import` — not a real cost on this path, left alone

This was NOT the cost this doc estimated ("up to ~150 stat-shaped calls"). Instrumented with a
temporary `rt_file_exists` probe counter (added, measured, then reverted — the finding is recorded
here instead) and traced 31 consecutive calls reached from the BFS: **all 31 hit `is_numbered =
false` and returned immediately with 0 `rt_file_exists` calls.** Root cause of the discrepancy: the
BFS's caller chain builds `module_path` via `_nb_join_segments` in `compile_targets.spl`, which
joins with `/` (contract-tested: `expect(source.contains("segs.join(\"/\")")).to_equal(false)` just
confirms it's hand-rolled, not that it's dot-joined — it isn't dot-joined either), e.g.
`"compiler/driver/foo"`. `_driver_resolve_numbered_compiler_import`'s `is_numbered` gate checks
`module_path.starts_with("compiler.")` — a **dot**. A slash-joined path never matches, so the
up-to-18-candidate cascade this doc worried about never executes a single `rt_file_exists` from
this call path. The BFS's actual numbered-directory resolution (`compiler.driver` ->
`compiler/80.driver`) happens earlier and separately, in `_nb_resolve_segs`'s own fallback loop via
`_nb_resolve_under_root` (`compile_targets.spl`) — a different implementation this doc did not
name. `_driver_resolve_numbered_compiler_import` is real (and does pay the full candidate-cascade
cost) only for callers that pass dotted `module_path`, e.g. the `phase1:load_sources` closure scan
in `driver_source_pipeline_loading.spl` — outside the profiled BFS hot path, so out of scope here.
Left unchanged apart from a comment recording this so a future reader doesn't re-chase the same
"~150 probes" estimate against the wrong call path. No code/behavior change.
