# `--native` enum match with payload binding — FIXED for simple bindings, nested destructuring still open (2026-08-11)

- **ID:** BUG-2026-08-11-native-match-enum-payload-binding
- **Supersedes:** narrows the open gap in
  `doc/08_tracking/bug/match_on_enum_native_lowering_status_2026-08-07.md`
  (payload-bearing enum match refused under `--native`).
- **Status:** FIXED for the common shape — `match`/`case` arms whose enum
  payload sub-patterns are plain identifiers/`mut` identifiers/wildcards
  (`Result.Ok(v)`, `Result.Err(msg)`, `Shape.Circle(r)`) now compile and run
  correctly under `simple compile --native`. Arms with nested destructuring in
  the payload (tuple/array/struct/literal sub-patterns) or a `case ... if
  guard:` remain refused fail-closed with the same `[PatternMatch]`
  diagnostic — this is a real, filed remainder, not silently dropped.

## Repro (before the fix)

```
$ bin/simple compile test/fixtures/native_match_enum_payload/repro.spl --native -o out
error: semantic: cannot compile to standalone native binary: 1 function(s) contain constructs that require the interpreter:
  - classify: [PatternMatch]
```

`test/fixtures/native_enum_match_payload/main.spl` (pre-existing fixture,
`describe_shape` with `Shape.Circle(r)` / `Shape.Rect(w, h)` / `Shape.Point`)
reproduces the same failure.

## 3-lane truth table (fresh Rust-seed build, `/mnt/data/cargo-target-match/release/simple`)

| Lane | Command | Payload-free enum match | Payload-bearing enum match (simple bindings) | Payload-bearing + guard |
|---|---|---|---|---|
| JIT (default) | `simple run f.spl` | correct | correct | correct |
| Interpreter | `SIMPLE_EXECUTION_MODE=interpret simple run f.spl` | correct | correct | correct |
| Native AOT (`--native`) | `simple compile f.spl --native -o out` | correct (pre-existing) | **correct (this fix)** | refused fail-closed (`[PatternMatch]`, unchanged, out of scope) |

## Root cause

`src/compiler_rust/compiler/src/compilability.rs` decides, for AOT-native
mode only, whether a `match`'s arms are "native-compilable" via
`is_native_payload_free_enum_match` (used at both `Node::Match` line ~333 and
`Expr::Match` line ~578). Despite its name, the function was stricter than
necessary: it rejected *any* arm whose `Pattern::Enum { payload: Some(p), .. }`
had a non-empty payload — even when every payload sub-pattern was a plain
identifier binding. But the actual codegen surface already supports exactly
that:

- HIR lowering (`hir/lower/stmt_lowering.rs::build_pattern_binding_stmts`)
  already emits `EnumPayload`-based extraction `Let` statements for
  identifier-bound enum payloads (this path is shared with the JIT/interp
  lanes and was not itself broken).
- Native codegen already implements the MIR instruction end-to-end:
  `MirInst::EnumPayload` is dispatched in
  `codegen/instr/mod.rs:992` to `compile_enum_payload`, implemented in
  `codegen/instr/enum_union.rs` (calls runtime `rt_enum_payload`, which
  `codegen/instr/result.rs` and `codegen/instr/pattern.rs` also rely on).

So the AOT path was refusing a construct its own backend already knew how to
emit — the gate was over-conservative, not the codegen.

## Fix

`compilability.rs::is_native_payload_free_enum_match` (~line 255): instead of
rejecting any arm with a non-empty payload outright, it now inspects each
payload sub-pattern and only rejects when a sub-pattern is something other
than `Pattern::Identifier` / `Pattern::MutIdentifier` / `Pattern::Wildcard`
(tuple/array/struct/literal/range/or sub-patterns still reject, same as
before). Guards (`arm.guard.is_some()`) were already rejected and remain so.

## Red → green

- RED (pre-fix, confirmed by reverting the gate change locally): `simple
  compile test/fixtures/native_enum_match_payload/main.spl --native -o out`
  fails with `cannot compile to standalone native binary: ... [PatternMatch]`.
- GREEN (post-fix): compiles to a real ELF (215 `FUNC` symbols via `readelf
  -sW`, `file` reports a real dynamically-linked PIE executable, not
  stripped-to-nothing), runs, prints `kind-A/kind-B/kind-C/circle:2.5/rect:3.0x4.0/point`
  — matches the JIT/interpreter lanes exactly.
- Negative control: `test/fixtures/native_match_enum_payload/repro.spl`
  (`Result.Ok(v)` / `Result.Err(msg)`) — the `Err` arm is exercised and
  returns `-1` (not the `Ok` arm's value), proving real per-variant dispatch,
  not "always take the first arm". Output: `ok:42`, `err:boom`, `PASS`.
- Guard/nested-destructuring case (ad hoc fixture, `Shape.Rect(w, h) if w ==
  h: ... case Shape.Rect(w, h): ...`) still correctly refused with the same
  `[PatternMatch]` diagnostic — confirms no over-widening.

## Filed remainder (not silently narrowed)

Native AOT still cannot compile enum-match arms whose payload contains nested
destructuring (`Shape.Rect((a, b))`-style, struct-field sub-patterns inside a
payload, literal payload tests) or a `case ... if guard:`. Closing that
requires either lowering `MirPattern`/`compile_pattern_test`
(`codegen/instr/pattern.rs`, currently only reachable from `x is
Enum.Variant` expressions per its own doc comment) into the `match`-statement
HIR→MIR path, or extending `build_pattern_binding_stmts`'s tuple/array/struct
binding emission plus a matching `is_native_payload_free_enum_match` relaxation
for those pattern shapes. Left open as a separate task.

## Regression gate

`scripts/check/check-native-enum-match-payload.shs` — updated 2026-08-11 to
hard-assert the payload-bearing fixture's runtime output (previously it only
NOTE'd if the gap ever closed). Verdict convention: `PASS — <n> checked` (n=2)
exit 0 / `FAIL — ...` exit 1 / missing `bin/simple` binary asserts (`test -x`)
before any check runs. Run:

```
SIMPLE_BINARY=/path/to/simple sh scripts/check/check-native-enum-match-payload.shs
```
