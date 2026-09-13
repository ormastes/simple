# Bug: `grid` as class field / named constructor argument fails to parse

## Closed 2026-09-13 — Already fixed (2026-06-14 lexer named-arg mapping); no longer reproduces

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): `class P: grid: i64` + `val p = P(grid: 7)` + `print "grid={p.grid}"` runs clean and prints `grid=7`. No `Unexpected token: expected Newline, found Integer`.
- **inferred**: matches the Resolution note — `TokenKind::Grid => Some("grid")` in the named-arg helper. The follow-up suggestion (revert `grid_dim`/`block_dim` in `src/lib/nogc_sync_mut/gpu/queue.spl`) is optional cosmetics, not this defect, and is deliberately left alone.

- **Date:** 2026-06-13
- **Severity:** P2 (grammar regression — common identifier unusable in named-arg position)
- **Status:** CLOSED 2026-09-13 (resolved 2026-06-14, re-verified)
- **Area:** parser (likely GPU launch grammar `kernel<<<grid, block>>>(args)` token handling)

## Resolution (2026-06-14)

`grid` is the lexer keyword `TokenKind::Grid` (2D matrix literals). The named-arg
helper in `src/compiler_rust/parser/src/expressions/helpers.rs` now maps
`TokenKind::Grid => Some("grid")`, so `P(grid: 0)` parses as an ordinary named
argument. Verified: `P(grid: 7)` runs and prints `grid=7`; `block` and `<<<...>>>`
launch syntax unaffected. The workaround fields (`grid_dim`/`block_dim`) in
`src/lib/nogc_sync_mut/gpu/queue.spl` may be reverted to `grid`/`block` once the
seed is redeployed.

## Repro

```simple
class P:
    grid: i64

fn main():
    val p = P(grid: 0)
    print "{p.grid}"
```

Both seed JIT and interpreter fail identically:

```
error: compile failed: parse: Unexpected token: expected Newline, found Integer(0)
```

Pointing at the value after `grid:` (e.g. `queue.spl:50:34`). The identical
program with the field renamed to `g` or `block` runs fine — `block` is NOT
affected, only `grid`.

## Notes

- Field *declaration* `grid: i64` parses; only the named-argument use
  `P(grid: 0)` breaks, so `grid` appears to be consumed as a special token in
  call-argument context (suspect: `<<<grid, block>>>` launch-config parsing in
  `src/compiler/10.frontend/parser_types_expr.spl:241` /
  `lexer_types.spl:144 TripleLess`).
- Hit while implementing `LaunchShape(grid: ..., block: ...)` for the SYCL
  parity Wave 1 work
  (`doc/03_plan/language/gpu_fpga/sycl_parity_unified_kernel_plan_2026-06-13.md`).
- Workaround applied: fields renamed `grid_dim` / `block_dim` in
  `src/lib/nogc_sync_mut/gpu/queue.spl`. Revert to `grid`/`block` once fixed.

## Expected

`grid` is an ordinary identifier; it must be usable as a field name and named
argument everywhere outside the literal `<<<...>>>` launch syntax.
