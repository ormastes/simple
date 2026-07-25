# Defer fall-off-end extension (#172 follow-up)

## Change

File touched: `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
(only file changed; 50 insertions / 16 deletions, mostly comment updates).

`convert_decl_fn`'s fall-off-the-end defer replay block previously only
appended pending defers when the function's last raw top-level statement was
itself a `defer` (nothing trailing it). Any other trailing-statement shape hit
the loud-fail `__defer_unsupported_placement__` sentinel — including the most
common real-world shape: ordinary statements after a `defer`, no explicit
`return`.

Fix: hoisted `has_ret = ret > 0` (whether the function declares a `-> T`
return type) to be computed before the body-conversion loop, then gated the
new append path on it:

- `has_ret == false` (no declared return type -> HIR uses
  `lower_hir_block_unit`, which never extracts a tail value from the last
  statement): append the pending defers, LIFO, after the real last statement.
  Safe unconditionally, since there is no implicit-return-value slot to
  steal.
- `has_ret == true` (declared return type -> HIR uses `lower_hir_block`,
  which lifts the last expression-statement into the block's implicit
  tail/return value): left untouched, still loud-fails. Combining a
  defer-replay append with an implicit tail-value return is a different,
  harder shape explicitly out of scope — verified in a non-battery sanity
  check (still refuses loudly, see below).

The already-landed cases (explicit `return` at any depth, last raw statement
being `defer` itself, nested-block/`errdefer` placements) are unchanged.

## Battery results (verified by construction, not oracle — interpreter
double-runs defers, so native binary was hand-checked against the expected
LIFO order)

| # | Case | Expected (by construction) | Native output | Result |
|---|------|------------------------------|----------------|--------|
| 1 | `fn work(): defer print(91); defer print(92); print(1); print(2)` called from `main` | `1,2,92,91` | `129291` | PASS |
| 2 | `fn work(n): defer print(90); if n>0: print(10); return / print(20)` — called with n=5 then n=-1, bracketed by prints | n=5: `10,90` (early-return path runs defer once); n=-1: `20,90` (fall-through path runs defer once) | `10001090200020903000` = `1000,10,90,2000,20,90,3000` | PASS — each path runs defer exactly once, no double-run |
| 3 | `fn work(): defer print(77); print(5); return` (explicit return, already-supported) | `5,77` unchanged | `577` | PASS |
| 4 | `fn work(n): if n>0: defer print(99); print(1)` (defer nested inside `if`) | build fails loudly, no binary | exit 1, `HIR lowering error ... unresolved name: __defer_unsupported_placement__`, no binary produced | PASS |
| 5 | Multi-construct: three functions (shape1=battery 1, shape2=battery 2, shape3=battery 3) called in sequence from `main` | `1,2,92,91,10,90,20,90,5,77` | `12929110902090577` | PASS |

Extra (non-battery) sanity check: `fn work() -> i64: defer print(9); print(1); 42`
(declared return type, fall-off-end with trailing tail-value expression after
defer) — still loud-fails with the same `unresolved name:
__defer_unsupported_placement__` error, confirming the `has_ret == true`
shape stays out of scope and does not silently misroute the return value.

## Full smoke matrix

`sh scripts/check/native-smoke-matrix.shs` from the worktree:

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

Only failure: `option_nil_check` (pre-existing/allowed per gate criteria,
unrelated to defer). Gate requirement (>=14/15, 0 codegen_fallback_hits, only
allowed fail = option_nil_check) met.

## Files touched

- `/tmp/wt_defer2/src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
  (patch saved at `/home/ormastes/dev/pub/simple/scratchpad/defer_falloff.patch`)

No commits made; worktree removed after patch export per instructions.
