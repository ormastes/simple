# `--native` enum match with payload binding — FIXED for identifier bindings, guards, AND nested destructuring (2026-08-11)

- **ID:** BUG-2026-08-11-native-match-enum-payload-binding
- **Supersedes:** narrows the open gap in
  `doc/08_tracking/bug/match_on_enum_native_lowering_status_2026-08-07.md`
  (payload-bearing enum match refused under `--native`).
- **Status:** FIXED, in two landings:
  1. (earlier this date) `match`/`case` arms whose enum payload sub-patterns
     are plain identifiers/`mut` identifiers/wildcards (`Result.Ok(v)`,
     `Result.Err(msg)`, `Shape.Circle(r)`) compile and run correctly under
     `simple compile --native`.
  2. (this landing) `case ... if guard:` arms, and payload sub-patterns that
     nest a `Tuple`/`Array`/`Struct` destructure whose own leaves are plain
     identifiers/wildcards (`Pair.Two((a, b))`,
     `Shape2.Dot(Point { x: a, y: b })`), ALSO compile and run correctly under
     `--native`.

Still refused fail-closed with the same `[PatternMatch]` diagnostic, and
**deliberately not touched by this landing**: a payload sub-pattern that
bottoms out in something other than an identifier/wildcard — a literal test
(`Const(Str(x), _)`), an `Or`/`Range`/`Typed`/`Rest` sub-pattern, or a
`Struct`/`Tuple`/`Array` pattern used directly as the top-level `case`
pattern (not nested inside an enum payload).

## Repro (before this landing's fix, guards + nested destructuring)

```
$ bin/simple compile test/fixtures/native_match_enum_payload/guard_repro.spl --native -o out
error: semantic: cannot compile to standalone native binary: 1 function(s) contain constructs that require the interpreter:
  - classify: [PatternMatch]

$ bin/simple compile test/fixtures/native_match_enum_payload/nested_repro.spl --native -o out
error: semantic: cannot compile to standalone native binary: 1 function(s) contain constructs that require the interpreter:
  - describe: [PatternMatch]
```

Confirmed RED against a real rebuilt seed binary (origin-tip
`compilability.rs`, `/mnt/data/cargo-target-match2/release/simple`) — both
fixtures listed above failed to compile with exactly this diagnostic before
the gate change in this landing, and compiled + ran correctly after it, with
no other file changed in between.

## Investigation: was this a gate problem or a codegen gap?

Before touching the gate, both real gaps were probed directly by relaxing
`is_native_payload_free_enum_match` locally (first to drop the
`arm.guard.is_some()` early return, then to also accept any payload shape)
and rebuilding the real seed compiler — not by reasoning from the doc
comments, which were themselves the thing under test:

- **Guards**: HIR already combines a match arm's structural pattern condition
  and its `if` guard into ONE boolean expression via `lower_match_guard`
  (`hir/lower/stmt_lowering.rs:1917`) — `guarded_condition = pattern_cond AND
  guard_cond` — shared unmodified across the JIT, interpreter, and native
  lanes. Native isel already emits arbitrary boolean `And` + `Terminator::If`
  chains. Relaxing the gate alone (rebuilt seed, `guard_repro.spl`) produced a
  binary matching JIT/interpreter output exactly: `big-ok:42 / small-ok:3 /
  err:boom / PASS` (the "small" `Ok(3)` value proves the guard's `v > 10`
  falls through to the next arm rather than always/never firing).
- **Nested destructuring**: `bind_subpattern`
  (`hir/lower/stmt_lowering.rs:1710`) already recurses into `Pattern::Tuple` /
  `Pattern::Array` (via `bind_sequence`) and `Pattern::Struct` (via
  `bind_struct_fields`) for ANY sub-pattern position, including one sitting
  inside an enum payload slot (`bind_nested_payload` at line 1675 calls
  `bind_subpattern` per payload element) — this walk is the single owner of
  binder emission for tuple/array/struct positions everywhere, not something
  added for enum payloads specifically. Native codegen's struct-field and
  tuple-element loads (`codegen/instr/closures_structs.rs`) are the same ops
  already exercised for top-level `case (a, b):` and `case Point { x, y }:`.
  Fully relaxing the gate (rebuilt seed) and compiling `Pair.Two((a, b))` and
  `Shape2.Dot(Point { x: a, y: b })` fixtures produced correct output on the
  first try — `two:3,40 / none / PASS` and `dot:7,9 / nowhere / PASS`.

**Conclusion: both remaining gaps were gate-only, same shape as the first
landing.** No new MIR instruction or codegen lowering was needed for either.
This was verified by attempting compilation with the gate fully relaxed
BEFORE writing the scoped fix below, per the residual-scope instruction to
read the real failure rather than assume.

## Root cause

`src/compiler_rust/compiler/src/compilability.rs::is_native_payload_free_enum_match`
(~line 255, used at both `Node::Match` and `Expr::Match` sites) had two
remaining over-approximations after the first landing:

1. `if arm.guard.is_some() { return false; }` unconditionally rejected any
   guarded arm, even though the guard is lowered to a plain boolean `And`
   that native isel already handles.
2. The payload sub-pattern check accepted only
   `Identifier`/`MutIdentifier`/`Wildcard` — `Tuple`/`Array`/`Struct`
   sub-patterns were rejected outright even when every element/field inside
   them was itself a plain binding, despite `bind_subpattern` already
   emitting correct binders for exactly that shape.

A secondary, previously-latent gap: neither `Node::Match` nor `Expr::Match`
ever walked `arm.guard` through `analyze_expr`, so accepting guards
unconditionally (without this fix) would have let a guard containing a
genuinely unsupported construct (a closure call, GC allocation in a nogc
context, etc.) slip through unflagged. Fixed in the same change — see below.

## Fix

`compilability.rs`:

- Dropped the blanket `arm.guard.is_some()` rejection. `lower_match_guard`
  folds the guard into the same condition used for the (already-accepted)
  bare pattern test, so it needs no separate gate.
- Added `is_native_safe_binding_pattern` (~line 300): a recursive predicate —
  `Identifier`/`MutIdentifier`/`Wildcard` are safe leaves;
  `Tuple`/`Array`/`Struct` are safe iff every element/field they contain is
  also safe (recursively). `is_native_payload_free_enum_match`'s payload loop
  now calls this instead of matching only the three leaf variants directly.
  Anything that isn't a safe leaf or a safe container of safe leaves (a
  literal, an `Or`/`Range` sub-pattern, ...) still rejects, unchanged.
- Added `analyze_expr(guard, ...)` calls for `arm.guard` at both the
  `Node::Match` and `Expr::Match` sites, so a guard's own body is still
  checked against every other AOT-native compilability rule (this was a gap
  even before this change — previously moot because guards were always
  rejected outright).

## 3-lane truth table (rebuilt seed, `/mnt/data/cargo-target-match2/release/simple`)

| Fixture | JIT (`simple run`) | Interpreter (`SIMPLE_FORCE_INTERPRETER=1 simple run`) | Native AOT (`simple compile --native`) |
|---|---|---|---|
| `native_enum_match_payload/payload_free.spl` (control) | `kind-A/kind-B/kind-C` | `kind-A/kind-B/kind-C` | `kind-A/kind-B/kind-C` (pre-existing, unaffected) |
| `native_enum_match_payload/main.spl` (identifier payload, pre-existing fix) | `kind-A/kind-B/kind-C/circle:2.5/rect:3.0x4.0/point` | same | same |
| `native_match_enum_payload/repro.spl` (`Ok(v)`/`Err(msg)`, pre-existing fix) | `ok:42/err:boom/PASS` | same | same |
| `native_match_enum_payload/guard_repro.spl` (**new**, `case ... if v > 10:`) | `big-ok:42/small-ok:3/err:boom/PASS` | same | same — **was `[PatternMatch]` refusal before this fix** |
| `native_match_enum_payload/nested_repro.spl` (**new**, `Pair.Two((a, b))`) | `two:3,40/none/PASS` | same | same — **was `[PatternMatch]` refusal before this fix** |
| `native_match_enum_payload/nested_struct_repro.spl` (**new**, `Shape2.Dot(Point { x: a, y: b })`) | `dot:7,9/nowhere/PASS` | same | same — **was `[PatternMatch]` refusal before this fix** |

`SIMPLE_EXECUTION_MODE=interpret` is NOT honored by this seed's `run`
subcommand (produces `0 examples, 0 failures` / `nil` output — a harness
quirk unrelated to this fix); `SIMPLE_FORCE_INTERPRETER=1` is the flag that
actually routes through the tree-walk interpreter and was used for the
interpreter column above.

## Red → green

- RED: both new fixtures (`guard_repro.spl`, `nested_repro.spl`) fail to
  compile under `--native` with a real rebuilt seed on origin-tip
  `compilability.rs`, `[PatternMatch]` diagnostic, exit non-zero. Confirmed
  directly (not inferred) by rebuilding the seed with the pre-fix gate.
- GREEN: same seed rebuilt with only the `compilability.rs` change above
  compiles all three new fixtures to real ELF binaries and their stdout
  matches JIT/interpreter exactly (see truth table).
- **Negative controls** (each baked into the fixture's own PASS/FAIL check,
  not just informal inspection):
  - `guard_repro.spl`: `Ok(3)` (guard `v > 10` is FALSE) must fall through to
    the un-guarded `Ok(v)` arm and print `small-ok:3`, not `big-ok:3` — proves
    the guard is actually evaluated per-call, not always-true/always-false.
    `Err("boom")` must never match either `Ok` arm.
  - `nested_repro.spl`: `Pair.Two((3, 40))` must print `two:3,40` (not
    `two:3,3` or `two:40,40`) — proves the tuple's two elements are bound from
    distinct slots, not both reading the same one. `Pair.None_` must reach the
    payload-free arm.
  - `nested_struct_repro.spl`: same shape for a struct payload
    (`x: 7, y: 9` → `dot:7,9`), plus the payload-free `Nowhere` arm.
- Pre-existing fixtures (`repro.spl`, `main.spl`, `payload_free.spl`) re-run
  and still pass unchanged — no regression from the gate widening.

## Filed remainder (not silently narrowed)

Native AOT still cannot compile enum-match arms whose payload contains a
literal test (`Const(Str(x), _)`), an `Or`/`Range`/`Typed`/`Rest`
sub-pattern anywhere, or a top-level (non-payload)
`Struct`/`Tuple`/`Array` `case` pattern — none of these were probed or
verified in this landing, and `is_native_safe_binding_pattern` explicitly
falls through to `false` for all of them. This is a real, deliberate scope
boundary, not an oversight: closing it needs its own probe-then-fix pass the
same way this one was done, because "the gate was gate-only twice in a row"
is evidence about pattern *shapes already checked*, not a general license to
assume every remaining shape is gate-only too.

## Regression gate

`scripts/check/check-native-enum-match-payload.shs` — extended this landing
from 2 hard-asserted fixtures to 6: payload-free, identifier-payload (two
fixtures), guarded-arm, nested-tuple-payload, nested-struct-payload. Each
check compiles the fixture under `--native`, runs the resulting binary, and
byte-compares stdout against the expected sequence (fail-closed: a compile
failure OR wrong output is a hard `FAIL`, not a soft NOTE). Verdict
convention: `PASS — <n> checked` (n=6) exit 0 / `FAIL — ...` exit 1 / missing
`bin/simple` binary asserts (`test -x`) before any check runs. Run:

```
SIMPLE_BINARY=/path/to/simple sh scripts/check/check-native-enum-match-payload.shs
```
