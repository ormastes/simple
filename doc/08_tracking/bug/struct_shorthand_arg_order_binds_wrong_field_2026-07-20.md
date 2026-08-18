# Bug: struct-literal shorthand argument binds to `nil` when it follows an explicit named argument

- **Status (2026-08-17, later pass): FIXED IN SOURCE, verified with a locally
  built seed; NOT yet in the deployed `bin/simple`.**

  Confirmed still RED with the deployed seed first
  (`readlink -f bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
  `59537240 2026-08-17 12:58:51 +0000`):
  ```
  bin/simple test test/feature/usage/struct_shorthand_spec.spl --no-session-daemon
  Results: 15 total, 13 passed, 2 failed
  bin/simple test test/01_unit/compiler/frontend/struct_shorthand_after_named_arg_spec.spl --no-session-daemon
  Results: 3 total, 1 passed, 2 failed
  ```

  **Fix applied** at the isolated root cause,
  `src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs`:
  the second pass now precomputes the set of field names claimed by named
  arguments in the same call, and advances `positional_idx` past any
  already-claimed slot before consuming a positional (shorthand) argument. So
  `Point(x: 10, y)` skips slot 0 (`x`, filled by name) and binds `y` to `y`.

  Re-verified with a seed built from this source into an isolated
  `CARGO_TARGET_DIR=/mnt/data/tmp-cargo-shorthand` (deployed `bin/simple`
  untouched):
  ```
  /mnt/data/tmp-cargo-shorthand/release/simple test test/feature/usage/struct_shorthand_spec.spl --no-session-daemon
  Results: 15 total, 15 passed, 0 failed
  ... test/01_unit/compiler/frontend/struct_shorthand_after_named_arg_spec.spl
  Results: 3 total, 3 passed, 0 failed
  ... test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl
  Results: 8 total, 8 passed, 0 failed
  ```
  **Unblock condition:** next seed rebuild/bootstrap that deploys
  `src/compiler_rust/**`; the three specs stay RED under the currently deployed
  binary until then. The latent same-shape site at
  `interpreter_call/core/bitfield_support.rs:115,129-132` was NOT touched.

- **Status (2026-08-17, lane A): STILL LIVE — reproduced at tip, root cause now
  isolated, fix NOT applied (owning file is outside this lane's scope).**

  Reproduced with the deployed Rust seed `bin/simple`:
  ```
  bin/simple test test/feature/usage/struct_shorthand_spec.spl --no-session-daemon --timeout 900
  Results: 15 total, 13 passed, 2 failed
  ```
  Failing: `uses explicit then shorthand` (expected 0 to equal 20) and
  `mixes in complex struct` (expected 0 to equal 30). Note the observed value is
  `0` (the i64 default), not `nil` as the 2026-07-20 write-up said.

  **Root cause (isolated this pass):**
  `src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs:358`
  declares `let mut positional_idx = 0;` and `:417-420` consumes a positional
  (shorthand) argument as `class_def.fields[positional_idx]`, incrementing the
  counter **only for positional args** and never skipping field slots already
  filled by a preceding named arg. For `Point(x: 10, y)`: `x: 10` is inserted by
  name, then the shorthand `y` is taken as position 0 and overwrites field `x`
  with 20, leaving `y` at its default `0`. For `Point(x, y: 20)` the positional
  arg comes first, so index 0 is correct — exactly the reported asymmetry.
  Same shape (latent) at `interpreter_call/core/bitfield_support.rs:115,129-132`.

  **Fix shape:** mark a field consumed when a named arg fills it, and advance
  `positional_idx` past already-filled fields before taking a positional arg.

  **The HIR/compiled path is NOT affected:**
  `src/compiler_rust/compiler/src/hir/lower/expr/collections.rs:425-449` splits
  args into a named map plus a positional queue and walks declared field order,
  preferring the named entry and otherwise pulling the next positional — so a
  positional after a named arg lands in the first *unfilled* declared slot. The
  Rust parser leaves bare identifiers unnamed
  (`src/compiler_rust/parser/src/expressions/postfix.rs`); there is no
  shorthand-to-named rewrite, so the interpreter's counter is the only place the
  mix is resolved. **This is therefore an interpreter-only silent wrong result,
  and the pure-Simple `10.frontend` parser is not implicated** — the original
  "parser_stmts.spl" attribution was wrong.

  Evidence specs added (both RED at tip, both run interpreted, which is where the
  defect lives — no subprocess needed):
  - `test/01_unit/compiler/frontend/struct_shorthand_after_named_arg_spec.spl`
    (reproducing) — `Results: 3 total, 1 passed, 2 failed`
  - `test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl`
    (class detection: any name-resolved argument must bind independently of
    argument order) — `Results: 8 total, 3 passed, 5 failed`. It catches strictly
    more than the reproducer: text/bool fields (whose defaults are not `0`, so
    the desync shows a visibly different wrong value), a shorthand whose value is
    a struct, and shorthands fed by expressions/calls.

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/struct_shorthand_spec.spl`)
- **Area:** struct-literal call argument binding (interpreter or HIR lowering,
  not isolated further in this pass), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`struct_shorthand_spec.spl`, 2 failures:

```
✗ uses explicit then shorthand
  struct Point: x: i64, y: i64
  val y = 20
  val point = Point(x: 10, y)      # shorthand `y` means `y: y`
  expect point.y == 20             --> expected nil to equal 20

✗ mixes in complex struct
  struct Config: host: text, port: i64, timeout: i64
  val config = Config(host, port: 8080, timeout)
  expect config.host == "localhost" --> expected nil to equal 30 (timeout check;
                                          host check also fails per the batch run)
```

The sibling example in the same file, "mixes shorthand with explicit named
argument" (`Point(x, y: 20)` — shorthand **first**, explicit **second**),
**passes**. Only the reverse order (explicit first, shorthand after) breaks.

## Minimal repro

```simple
struct Point:
    x: i64
    y: i64

describe "repro":
    it "explicit then shorthand":
        val y = 20
        val point = Point(x: 10, y)
        expect point.x == 10
        expect point.y == 20
```

## Root cause

Not isolated to a specific source location in this pass (would need to trace
struct-literal call lowering / argument binding). The order-dependence (works
shorthand-then-explicit, fails explicit-then-shorthand) suggests the binder
processes explicit-named and positional/shorthand arguments via two separate
passes or index-tracking mechanisms that get out of sync once an explicit
named arg appears before a shorthand one — e.g. the shorthand arg after the
named one may be getting bound by positional index against the wrong
struct-field slot (or dropped) rather than resolved by its identifier name.

## Fix direction (not applied — compiler-internals change, needs rebuild)

Trace struct-literal call argument binding (likely
`src/compiler_rust/compiler/src/interpreter*` or HIR lowering for
`Expr::Call`/`StructInit`-shaped nodes) and confirm shorthand args are always
resolved by matching their identifier name against the struct's field name,
regardless of whether preceding arguments were explicit or shorthand.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/struct_shorthand_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.

## 2026-08-17 20:1x — RESOLVED on the DEPLOYED seed

Binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (bin/simple), md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45 — the REDEPLOYED seed carrying this session's fixes.

```
$ bin/simple test test/feature/usage/struct_shorthand_spec.spl --no-session-daemon --timeout 900
Results: 15 total, 15 passed, 0 failed
$ bin/simple test test/01_unit/compiler/frontend/struct_shorthand_after_named_arg_spec.spl --no-session-daemon --timeout 900
Results: 3 total, 3 passed, 0 failed
$ bin/simple test test/01_unit/compiler/frontend/name_resolved_argument_order_independence_class_spec.spl --no-session-daemon --timeout 900
Results: 8 total, 8 passed, 0 failed
```

Matches the isolated-build result exactly (15/15, 3/3, 8/8). No regression.
The latent same-shape site at `interpreter_call/core/bitfield_support.rs:115,129-132`
is still untouched.

**Status: RESOLVED** (verified on the deployed binary).
