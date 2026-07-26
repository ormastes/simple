# native-build lane parses at ~100 chars/sec — kernel closure can never finish any budget

- **Date:** 2026-07-26 (run 9 trace evidence, first observable harness build)
- **Lane:** deployed stage4 `bin/release/aarch64-apple-darwin-macho/simple` `native-build` (cranelift, `--target x86_64-unknown-none`, `--entry-closure`, harness env `SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=$ROOT/src SIMPLE_ALLOW_FREESTANDING_STUBS=1`)
- **Status:** open — measured, root cause not yet isolated

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

## Next
Isolate with a 2-file probe under the exact harness env vs plain env; bisect
which env knob (SIMPLE_BOOTSTRAP / SIMPLE_LIB / freestanding stubs / target)
triggers the collapse; then profile the parse loop hot path.
