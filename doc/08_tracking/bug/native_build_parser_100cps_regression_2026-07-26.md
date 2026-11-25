# native-build lane parses at ~100 chars/sec — kernel closure can never finish any budget

- **Date:** 2026-07-26 (run 9 trace evidence, first observable harness build)
- **Lane:** deployed stage4 `bin/release/aarch64-apple-darwin-macho/simple` `native-build` (cranelift, `--target x86_64-unknown-none`, `--entry-closure`, harness env `SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=$ROOT/src SIMPLE_ALLOW_FREESTANDING_STUBS=1`)
- **Status:** fixed — enum and closure registries routed through the shared O(1) open-addressing immortal-pointer hash table in `src/runtime/runtime_native.c` (in-code PERF comments cite this record); verified 2026-11-25, see end of file

## Measured (SIMPLE_COMPILER_TRACE=1, harness run 9, 10800s wall — expired in parse)
`[BOOTSTRAP-PHASE] phase2:parse:file` timings from `native-build.out` (19MB):

| file | chars | parse wall | rate |
|---|---|---|---|
| `gui_entry_desktop.spl` (first) | 27,726 | 436.4s | ~64 cps |
| `console.spl` | 2,418 | 12.7s | ~190 cps |
| `boot/cpu.spl` | 4,284 | 44.8s | ~96 cps |
| `bga_init.spl` | 11,165 | 144.5s | ~77 cps |
| `display_backend_core.spl` (2h27m in) | 815 | 27.2s | ~30 cps |
| `window_protocol/geometry.spl` | 1,083 | 39.0s | ~28 cps |

48 files parsed in 8,917s (~186s/file avg); rate DEGRADES as `heap_registry`
grows (7k → 4.1M entries). At ~100 cps the full kernel closure (hundreds of
files) cannot finish in any practical budget — runs 5, 7, 9 all died here
(runs 5/7 invisibly, pre-observability).

## Contrast (same binary!)
The identical deployed binary parses large stdlib closures in SECONDS on the
`run` lane (2D showcase: full parse+interpret+render in 103s total). The
collapse is specific to the native-build/bootstrap-env lane, and worsens with
accumulated heap — signature of an O(heap) or O(n²) cost per token/expr in a
mode-gated path (candidates: bootstrap-mode interning, freestanding-stub
resolution per identifier, heap-registry bookkeeping in the phase2 parse loop,
trace overhead is NOT it — only 1,795 `[parser-expr]` events total).

## History
07-17: stage3 binary built the WHOLE kernel with a 300s/file cap — only the 3
giant-literal files exceeded 60s; normal files were fast. Today every 1KB file
costs ~30s+. Regression window: stage3 (07-17) → current stage4 deploys.

## Impact
- SimpleOS-WM matrix cell unfillable until fixed (runs 5-9 all `build-timeout`).
- Masked until today by the zero-observability defect (fixed 2026-07-26,
  `simpleos_harness_silent_native_build_2026-07-26.md`).

## Root cause CONFIRMED (2026-07-26 evening, correlation test on run-9 rows)
`src/runtime/runtime_native.c` (core-c-bootstrap bundle): enum and closure
objects are registered in flat arrays that are **linearly scanned on every
`match`/`Option`/`Result` read (`rt_core_is_registered_enum`, :995) and every
closure invocation (`rt_core_as_closure`, :1128)** — and there is NO
unregister path for either (only arrays/mutexes have one) and no GC. Registry
size grows monotonically with total allocations, so per-file cost is
O(chars × registry_size): a moving-target O(n²) over the run. The `run` lane
is fast simply because a single invocation never reaches the multi-million
registry sizes where the scan dominates.

Falsification test on the 47 complete `phase2:parse:file` rows from run 9:
`wall/(chars×heap_registry)` cv=0.91 (spread ~4x) vs `wall/chars²` cv=1.72
(spread ~70x) — the registry model fits; the pure file-size model does not.

Secondary contributors on record: lexer full-text reslice per char (O(size²)
in-file term, `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`)
and the write-only `lex_source_codes` accumulation (leak, lexer.spl:198-212).

## Fix direction
O(1) membership for enum/closure discrimination (header-tag check like the
O(1) `rt_core_as_array` path, or a hash set), plus unregister-on-free if
lifetime allows. Lives in the C runtime — takes effect for the compiler
itself only after the next stage4 rebuild+redeploy.

## Verification 2026-11-25 (p2w3-ae lane, release/1.0.0 worktree)

The confirmed root cause — flat arrays linearly scanned on every
`rt_core_is_registered_enum` / `rt_core_as_closure` call, with no unregister
path — is fixed in current `src/runtime/runtime_native.c`:

- Enum registry (:1907-1934): a `PERF
  (native_build_parser_100cps_regression_2026-07-26)` comment block describes
  this exact defect and its fix; `rt_core_is_registered_enum` is now a single
  `rt_core_is_registered_immortal_ptr(e)` call — the shared O(1)
  open-addressing hash table already used by strings/dicts/floats.
- Closure registry (:2053-2083): same treatment; `rt_core_as_closure` goes
  through `rt_core_untag_registered_immortal` (pointer-only hash membership,
  no dereference of untrusted values) plus a kind check. The bespoke
  array+spinlock scan is gone.

This is exactly the "O(1) membership for enum/closure discrimination" fix
direction the record named. It takes effect for the compiler itself on the
next stage4 rebuild+redeploy, as the record noted; the source-level defect is
nonetheless closed.

A live re-measurement (SimpleOS WM harness native-build) was not possible in
this lane: Windows host, no aarch64-darwin stage4 deploy, and the pinned seed
binary at `bin/simple.exe` rejects the `@representation_boundary` decorator
added tree-wide by cfd89933699. Verification is by code inspection of the two
registry paths cited above; the secondary contributors noted in the record
(lexer full-text reslice, `lex_source_codes` accumulation) are tracked in
`bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`.

**Verdict: STALE-CLOSED.**
