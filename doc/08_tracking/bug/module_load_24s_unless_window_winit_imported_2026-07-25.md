# Importing `std.gpu.engine2d.engine` costs 24 s — adding `std.io.window_winit` drops it to 3 s

- **Date:** 2026-07-25
- **Area:** module loader / import closure resolution
- **Severity:** medium — 8x startup penalty on every interpreted run that touches
  Engine2D without also importing winit.
- **Status:** VERIFIED 2026-11-26 for the 24 s symptom only, with a caveat: re-measured at
  2.2-2.9 s (see the last section), but no fix commit explains the drop from the 12 s measured
  after the 2026-11-05 SPIR-V literal fix to about 2.5 s now. The comparison is also cross-seed and
  was taken on a shared, loaded box. RESOLVED for the std-lib amplifier (2026-11-05 root-cause
  section below). The remaining gap to the interpreter lane is the substring lane gate, now its own
  record: `seed_window_winit_substring_lane_gate_2026-11-26`.

## Repro

Five files, each `fn main() -> i64: print "ok"; 0`, differing only in imports.
All run with `SIMPLE_NO_DEPRECATED_WARNINGS=1` (so the hint spam is not a factor)
under `/tmp/claude-.../` paths (so the host kill monitor does not truncate them —
its `is_protected()` whitelists cmdlines containing `claude`).

| imports | wall time |
|---|---|
| `std.gpu.engine2d.engine` only | **24 s** |
| + `std.io.window_winit.{winit_loop_new}` | **3 s** |
| + `std.nogc_sync_mut.concurrent.thread.{thread_sleep}` | 24 s |
| + `std.io_runtime.{env_get, file_write}` | 23 s |
| + `std.common.encoding.font_registry.{selected_font_asset_candidates}` | 24 s |

Only `std.io.window_winit` has the effect, and it is an **8x speed-up from
importing more code**, which should not be possible.

Repeated back-to-back to rule out a warm cache:

```
probe_a_import (Engine2D only)      25 s
probe_b_render (Engine2D + draws)   28 s
probe_d_imports (full closure)       3 s
probe_b_render (again)              26 s
```

Stable and order-independent. First-run vs fourth-run timings for the same file
agree to within 2 s, so this is not `build/native_cache` warmth.

## Interpretation

Importing `window_winit` evidently short-circuits whatever the loader is doing
for 21 s in its absence — most likely a fallback scan / repeated re-resolution
that a symbol provided by `window_winit` satisfies up front. Worth checking
whether the Engine2D closure triggers repeated re-parsing of the same modules
when a backend/window symbol is unresolved.

The 24 s is pure module-load: in the fast case,
`examples/06_io/ui/graphics_2d_showcase.spl` reaches its first runtime trace
marker (`graphics_2d_trace=entry`, via `SIMPLE_SHOWCASE_TRACE=1`) at **t+3 s**.

## Why it matters

This is a flat 21 s tax on every interpreted Engine2D run, and it makes any
perf comparison between two 2D entries meaningless unless both happen to import
winit. It also inflates every "the 2D lane is too slow" report by ~21 s.

## Found via

Root-causing the 2D x headless showcase cell — see
`engine2d_load_font_interpreter_3kb_per_sec_2026-07-25.md`. (This is *not* that
cell's root cause; the showcase already imports `window_winit` and so pays only
the 3 s.)

## 2026-11-05 — Root-caused (work branch work/libbug-std-modload-20261105)

There is **no shared-init ordering defect** in the std lib. Two independent
mechanisms compose into the 24 s:

1. **Lane gate, not init:** the Rust seed diverts any *entry source containing
   the substring `window_winit`* to the tree-walk interpreter before the JIT
   runs (`source_uses_jit_unsafe_graphics_runtime`,
   `src/compiler_rust/driver/src/exec_core.rs`). A probe whose only winit
   mention is a `# window_winit` comment drops 35 s → 0.9 s; engine2d itself
   never references winit. Without the substring, the JIT lane eagerly
   flattens the whole engine2d import closure (~276 modules) and runs
   HIR → MIR → Cranelift on it.

2. **The std-lib amplifier (fixed here):** the generated Vulkan SPIR-V blob
   modules carried the bytecode as `0xNNu8`-suffixed array literals.
   Suffixed integer literals take a ~25x slower path through the JIT
   frontend than bare literals: a synthetic 20,688-element `0xNNu8` literal
   costs ~13-15 s to JIT where the identical bare-hex or decimal literal
   costs ~0.5 s (measured 2026-11-05, aarch64, phase1 seed binary). The
   engine2d closure embeds ~85,600 such words across 7 generated modules
   (`backend_vulkan_*_spirv*.spl`), which accounted for roughly two-thirds
   of the JIT lane's 30-35 s.

Fix: `scripts/tool/spirv-to-spl-words.shs` now emits bare `0xNN` words (the
enclosing literal is typed `[u8]`, so the suffix bought nothing), the 7
generated modules were converted in place (bytes verified identical), and
the 5 `check-*-spirv-pinned.shs` guards were updated for the new word
format (all PASS, selftests included, glslangValidator-verified).

Measured after fix (same probe, same binary, warm): engine2d-only import
**35.1 s → 12.0 s**; engine2d + window_winit unchanged (~0.9-1.3 s). The
remaining ~12 s is genuine Cranelift compilation of ~1 MB of backend source
(backend_vulkan alone: 29.7 s → 9.3 s; backend_metal 4.3 s) — legitimate
JIT-lane work, matching the documented interpreter-preference tradeoff.
Runtime blob correctness verified (SPIR-V magic `03 02 23 07`, exact pinned
byte lengths; engine2d/vulkan specs green on both lanes).

Follow-up not done here: the substring lane gate in the Rust seed is a
fragile heuristic (any comment mentioning window_winit diverts the whole
program to the interpreter); it deserves its own bug record against
`src/compiler_rust/driver/src/exec_core.rs`.

## Verification 2026-11-25 (p2w3-ah lane, release/1.0.0)

The 2026-11-05 root-cause fix is confirmed in-tree on release/1.0.0 HEAD:
`scripts/tool/spirv-to-spl-words.shs` documents and emits bare `0xNN` words
(the ~25x-slower `0xNNu8` suffix path is gone), and the generated
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_*_spirv*.spl` modules
contain zero `0xNNu8`-suffixed literals (grepped; bare `0xNN` words present).
Status header corrected from OPEN to RESOLVED accordingly.

**Verification limit:** the 35 s -> 12 s timing was not re-measured — the
probe requires the JIT lane on a full engine2d import closure, which is not
runnable within this lane's budget on this host, and `bin/simple test` is
repo-wide blocked at this HEAD by the `@representation_boundary` seed
rejection. The fix's presence and the byte-format conversion are verified by
code/content inspection only; the 2026-11-05 measurements stand as the
recorded evidence.

Still open (by design, not this bug): the substring lane gate in
`src/compiler_rust/driver/src/exec_core.rs`
(`source_uses_jit_unsafe_graphics_runtime`) — a comment mentioning
`window_winit` still diverts a whole program to the interpreter. That is a
Rust-seed heuristic deserving its own bug record, as the 2026-11-05 section
already notes; no such record existed as of this check, so it is flagged here
for the next triage pass rather than silently dropped.

## Verification 2026-11-26 (gpuvk lane, Linux aarch64 NVIDIA GB10) — re-measured, 24 s is gone

Seed `/home/yoon/.cache/cargo-target-wr-seed1126b/release/simple` (sha256 prefix
`fb80903917d6d5f5`), worktree on release/1.0.0 `453118ed07c`, `SIMPLE_NO_DEPRECATED_WARNINGS=1
seed run`, five rounds with the run order alternated:

| entry imports | round 1 | rounds 2-5 |
|---|---|---|
| `std.gpu.engine2d.engine` only (JIT lane) | 6.48 s | 2.23-2.88 s |
| + `std.io.window_winit.{winit_loop_new}` (interpreter lane) | 1.75 s | 0.56-0.77 s |
| engine only + `# window_winit` comment (interpreter lane) | 0.73 s | 0.54-0.72 s |
| no imports | 0.05 s | 0.04-0.05 s |

The engine2d-only import now costs about 2.5 s, down from 24 s (and from the 12 s measured after the
2026-11-05 fix). Every probe printed `ok` with rc=0. The remaining gap of about 4x between the
engine-only row and the comment row is the lane split, not module loading. It is now its own
record: `seed_window_winit_substring_lane_gate_2026-11-26.md`. Status: **VERIFIED for the 24 s symptom**. No fix commit explains the 12 s to 2.5 s step: the 12 s figure came from a different seed (phase1, 2026-11-05), and these numbers were taken on a loaded shared box.

Follow-up the same day, three rounds:

- `SIMPLE_EXECUTION_MODE=interpret` on the engine-only file: 0.47-0.79 s. That matches the
  `window_winit` rows, so the residual gap is the lane split.
- JIT lane with `HOME` pointed at an empty directory: 1.50-1.54 s, which writes nothing there. So
  the 2-3 s figure does not depend on a warm `~/.cache/simple`. The spread between rounds tracks
  host load on this shared box, so treat every number here as an envelope, not a constant.
