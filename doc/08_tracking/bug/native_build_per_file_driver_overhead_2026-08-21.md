# native-build: non-parse driver overhead before and inside the per-file loop

- Date: 2026-08-21
- Status: PARTIALLY FIXED (source-closure preamble 4.0x faster; residue tracked below)
- Area: `src/compiler/80.driver/`, `src/compiler/10.frontend/core/interpreter/`
- Scope: everything the native-build driver does per file that is NOT parsing.
  The lexer/parser itself and the front-end result cache / parse sharding are
  separate lanes and are deliberately untouched here.

## How this was measured

Probe (this session's own run, not the shared stage1 lane):

```
SIMPLE_CACHE_SCOPE=ovh SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1 \
  bin/simple native-build --source src/app --entry-closure \
  --entry src/app/cli/bootstrap_main.spl -o /mnt/data/seedperf/stage1.ovh \
  --threads 4 --timeout 3600
```

Phase boundaries come from the `[build] <phase> ... +<total>ms dt=<n>ms` receipts
that `log_build_progress` already emits (`80.driver/driver_log_helpers.spl:130`).
Sub-step costs inside the closure come from a new level-gated counter set in
`80.driver/driver_source_loading.spl`, default OFF, enabled by
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING=1` (the name the 2026-07-31 closure
investigation already used); it emits a cumulative
`[closure-timing] imports=…ms/n resolve=…ms/n collect=…ms/n` line every 64
collections, so a run killed mid-phase still leaves a usable trail — every probe
of this phase has been killed mid-phase.

Shared box, 20+ concurrent `simple` processes: treat absolute numbers as an
envelope. Every pre/post pair below was taken in the SAME tree with the SAME
binary, toggling only the change under test.

## Phase table (662-file entry closure, first parse receipts)

| phase | pre | post | note |
|---|---|---|---|
| `load_sources` -> `source_closure` | 14 ms | 1-3 ms | trivial |
| `source_closure` (149 physical files) | **104,346 ms** (~700 ms/file) | **26,329 ms** (~176 ms/file) | all non-parse |
| `source_closure` -> `parse` | 2,241 ms | 218 ms | |
| first `[build] parse` receipt at | 106,587 ms | 26,547 ms | |
| per-file `parse` dt | 4.8 - 22.2 s | unchanged | other lanes own this |

## Sub-step table (same call counts, so directly comparable)

| sub-step | calls | pre | post | per call pre -> post |
|---|---|---|---|---|
| `_driver_entry_import_module_paths` | 1209 | 56,504 ms | 12,397 ms | **46.7 -> 10.3 ms** |
| `_driver_resolve_entry_import` | 2004 | 2,237 ms | 709 ms | 1.12 -> 0.35 ms |
| `_driver_collect_entry_import_source` | 704 | 1,386 ms | 429 ms | 1.97 -> 0.61 ms |

## Hypotheses REFUTED by measurement (recorded so they are not re-investigated)

- **Interpreted SHA-256 per file.** `sha256_text` over 20 KB measures **3 ms**,
  and no sha256 call site is on the per-file build path at all (`sha256_text` in
  `80.driver` appears only in VHDL artifacts, cache keys, promotion receipts and
  the CAS store). Not a factor. There is no `rt_sha256` primitive to route to
  (`src/runtime/runtime.h` has only `rt_tls13_sha256` and `rt_hash_text`) and
  none is needed.
- **`[gc-warning]` diagnostics per import.** `check_gc_family_boundary`
  (`10.frontend/core/interpreter/module_loader_core.spl`) already dedups on a
  `(importer_family, imported_family, module_name)` key; a full stage-1 log
  carries **6** such lines, not hundreds.
- **`[BOOTSTRAP-PHASE]` log writes.** `log_phase` is gated behind
  `SIMPLE_COMPILER_PHASE_PROFILE` / `SIMPLE_COMPILER_TRACE` and is silent by
  default.
- **Per-file `[build]` receipts.** One `print` + `rt_stdout_flush` per file,
  against a multi-second per-file cost. Deliberately kept — it is what makes a
  stalled file name itself on a host where profiling is blocked.

## Defects found and fixed

### 1. `_driver_entry_import_module_paths` did per-line comment work on every line

`80.driver/driver_source_loading.spl:432` (`_driver_entry_import_module_paths_text_fallback`).
For EVERY line of EVERY file in the closure it ran `_driver_text_index_of(line, "#")`
(a `contains` plus a `split` plus a length), a `contains("\"\"\"")`, a `trim`, and up
to four `starts_with` tests. Only lines whose trimmed form starts with a use/import
keyword can contribute — comment stripping removes a TRAILING part, so it can never
turn a non-keyword line into one, and a line starting with `#` strips to empty.

Fix: a whole-content early-out (`no "use " and no "import "` -> `[]`) plus a
per-line fast reject ahead of the comment scan, preserving the triple-quote
toggle. **56.5 s -> 12.4 s** over 1209 calls (4.6x) in the interpreted worker;
471 ms -> 303 ms over 8 scans of a 1212-line file through the JIT.

Reproduce: `test/01_unit/compiler/driver/driver_entry_import_scan_cost_spec.spl`
(1 of 2 red pre-fix). It pins BEHAVIOUR (docstring, `#`-commented, lazy, named-lazy,
`pub use`/`export use`/`import` spellings) and the MECHANISM. It deliberately does
NOT assert wall time: through the JIT the gap is only 1.55x, too narrow to threshold
without flaking, and the 4.6x that matters is paid by the interpreted worker a spec
does not run in.

### 2. The driver text set was O(bucket length) on both add and lookup

`80.driver/driver_source_loading.spl` `_driver_text_bucket_set_{new,add,has}`.
Keys were stored newline-delimited inside `[text]` buckets, so `add` rebuilt a
growing bucket STRING and `has` ran `starts_with`/`contains` over it. Five sets in
the closure BFS (`seen_sources`, `closure_seen_mods`, `closure_loaded_mods`,
`closure_queued_paths`, `discovered`) push thousands of keys through it.

Measured on 4000 realistic keys: **add 7644 ms -> 84 ms (91x), lookup 3997 ms ->
26 ms (154x)** for the primitive itself. Through the existing helper API the
realised numbers are add 1007 ms, lookup 63 ms — the residual add cost is a
whole-Dict copy at the CALL BOUNDARY, not inside the helper.

Fix: exact `Dict<text, bool>` membership via `contains_key` (never `.get()`, per
`doc/07_guide/language/dict_native_pitfalls.md`). The `bucket_count` parameter is
kept as an accepted capacity hint so that all ~30 call sites — which all infer the
type from the constructor — need no edit, keeping this change out of the two other
lanes' files entirely.

Reproduce: `test/01_unit/compiler/driver/driver_text_set_lookup_cost_spec.spl`
(exact membership incl. prefix keys, plus a 1500 ms budget for 4000 lookups that
the old shape cannot meet at ~4.0 s).
`test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl:88`
already pinned the OLD encoding in source text; its three behavioural expectations
are unchanged and its mechanism assertions were re-pointed at the new one.

### 3. Interpreter module registry lookups were linear scans

`10.frontend/core/interpreter/module_loader_core.spl`. `module_alias_loaded` runs
on EVERY import (three call sites in the load paths) and called
`module_find_by_file_path`, which walked `loaded_module_file_paths` element by
element calling the Dict-backed `module_is_loaded` per element.
`module_get_file_path` walked the same array. With N registered modules and M
imports that is O(N*M) interpreted iterations.

Fix: `file_path -> first index` and `module_name -> file_path` Dicts maintained in
`module_mark_loaded`. Both fall back to the linear scan when the memoized index
names a module that has since been unloaded, so "first CURRENTLY LOADED match wins"
is preserved exactly.

Reproduce: `test/01_unit/compiler/interpreter/module_registry_lookup_o1_spec.spl`.
It asserts on a COUNTER (`module_registry_scan_steps()`), not on wall time:
pre-fix 400 elements visited per worst-case lookup, post-fix 0. 2 of 3 red pre-fix.

Note: this one cannot be credited in the phase table above. The registry lives in
the interpreter that is COMPILED INTO `bin/simple`, so its win only lands after a
bootstrap redeploy, unlike the two driver fixes which the worker reads as source.

## Residue (not fixed here)

- `_driver_entry_import_module_paths` is still **10.3 ms/call and called 1209
  times for ~704 collected files** — roughly 1.7 calls per file. A path-keyed memo
  would collapse the duplicate calls, but the only clean place to key it is the
  call site in `driver_source_pipeline_loading.spl:224`, which belongs to the
  front-end-cache lane. A content-keyed memo was tried and removed on 2026-07-31
  (`native_build_entry_closure_slow_2026-07-31.md`) because hashing the whole
  content twice cost more than it saved; a path key does not have that problem.
- ~14 s of the remaining 26 s `source_closure` is outside the three instrumented
  helpers (the BFS body itself, and the per-add Dict copy at the helper call
  boundary). Collapsing the three set helpers into direct Dict operations at their
  call sites would recover the copy, but those call sites are in
  `driver_source_pipeline_loading.spl` and `src/app/io/_CliCompile/compile_targets.spl`.
- Per-file `parse` dt remains 4.8-22.2 s and is untouched: that is the parser lane.
