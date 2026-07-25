# Bug: `block` / `grid` as identifier names trip the parser near named-field construction

**Found:** 2026-06-16 · **Severity:** P3 (parser ergonomics) · **Area:** parser / frontend
**Status:** source fixed for `grid` in Rust parser 2026-07-15; focused execution
pending (`block` was not reserved)

## Summary
Using `block` (and apparently `grid`) as a function **parameter / local name** causes a
parse error `E0002: unexpected token, expected: Colon, found: Comma` at a *later*
named-field struct construction in the same function — the error points at the construction's
first comma, not at the identifier. Renaming the params (`block` → `block_dim`, `grid` →
`grid_dim`) resolves it. A standalone probe with the identical construction but parameter
names `g`/`b` compiles cleanly, isolating the trigger to the identifier names.

## Repro (shape)
```simple
use gc_async_mut.gpu_types.{GpuLaunchConfig}

fn f(grid: i64, block: i64) -> i64:
    val cfg = GpuLaunchConfig(grid_x: grid, grid_y: 1, grid_z: 1, block_x: block, block_y: 1, block_z: 1)
    #                                   ^-- E0002 "expected Colon, found Comma" at this comma
    cfg.grid_x
```
Rename `grid`/`block` → `grid_dim`/`block_dim` and it compiles. `block` is the likely
soft-keyword (block expressions/closures); `grid` may be incidental.

## Impact
Surprising: the error location (a comma several tokens later) misdirects diagnosis. Cost a
debugging detour while wiring `compute_run.spl` (GPU launch config). Low severity but a real
ergonomics trap.

## Fix direction
Either (a) allow `block`/`grid` as ordinary identifiers in value position (they are not in
the documented reserved list: gen, val, def, exists, actor, assert, join, pass_*), or
(b) emit a precise diagnostic at the identifier with a "reserved/soft-keyword" message
instead of a misleading colon-expected error at a downstream comma.

## Resolution

The collision was specific to the Rust parser's `grid` token; `block` is an
ordinary identifier and was incidental. Grid-literal parsing is now selected
only by its contextual lookahead, while other `grid` uses produce an identifier.
The pure-Simple parser already handled both names normally. A focused regression
uses the original function-parameter and named-field construction shape.

## Discovered by
std.compute runtime-pipeline build (`src/lib/gc_async_mut/compute/compute_run.spl`).
Worked around: params named `grid_dim`/`block_dim`.
