# ANY-typed slots hold RAW untagged scalars (JIT) — 2026-08-05

**Status:** Rust seed FIXED. Pure-Simple self-hosted compiler STILL OPEN (parity gap, below).

## Symptom

Under the Cranelift JIT, a scalar stored into an `Any`-typed slot was stored
RAW (untagged). Every consumer that assumes a tagged `RuntimeValue` then
misread the low 3 bits as tag bits:

```
val ab: Any = true    ab.to_text()  ->  "nil"           (raw 1  -> SPECIAL_NIL)
val ai: Any = 42      ai.to_text()  ->  denormal float  (raw 42 -> TAG_FLOAT)
val af: Any = 10.0    af.to_text()  ->  "0"
val at: Any = "hi"    at.to_text()  ->  "hi"            (heap ptr already tagged — fine)
```

This is the `<value:0x6>` / denormal-float artifact family. `<value:0x{:x}>` at
`src/compiler_rust/runtime/src/value/sffi/io_print.rs:464` is the faithful
REPORTER of an untagged value, not the bug.

**Not only cosmetic.** Measured by value, not by rendering:

```
OLD JIT:  ai == 42    -> false        af == 10.0 -> false
NEW JIT:  ai == 42    -> true         af == 10.0 -> true
```

An earlier reading that "the value is intact, only `to_text` is wrong" holds
for *pattern bindings* (a different path) but NOT for a local `Any` declaration,
where the comparison is wrong too.

## Engine divergence — why the suite was blind

| | local `Any` bool / i64 / f64 |
|---|---|
| JIT (`simple run`) | BROKEN (before this fix) |
| interpreter (`simple test`) | correct, always |

The spec suite hard-defaults to the interpreter, so no spec could observe this.
Reproduce only via `bin/simple run`, never via `bin/simple test`.

## Root cause

There is no single widen/box site. Boxing is per-consumer, and two consumers
were missing it:

1. `mir/lower/lowering_expr_call.rs` `box_arg_for_any_param` — matched
   `I8..U64` -> `BoxInt` and `F32/F64` -> `BoxFloat`, but `TypeId::BOOL`
   appeared nowhere, so a bool argument reached an `Any` parameter raw.
   (The sibling `box_enum_payload_if_needed` in the same file DOES list BOOL.)
2. `mir/lower/lowering_stmt.rs` `HirStmt::Let` — stored the initializer with no
   box at all, for every scalar type.

The correct block already existed ~700 lines away in the same file, in the
`HirExprKind::Global` assign arm: it gates on `target_is_any` and does all
three (`rt_value_bool` / `BoxInt` / `BoxFloat`). `HirStmt::Let` was simply
missing it. Both fixes copy that proven block.

**Bool must use `rt_value_bool`, never `BoxInt`.** Bool is `TAG_SPECIAL`
(`0b011`) with `SPECIAL_TRUE=1`/`SPECIAL_FALSE=2` (`runtime/src/value/tags.rs`),
i.e. raw 11/19. `BoxInt` yields a tagged INT 1 and renders `"1"` instead of
`"true"` — verified by deliberate sabotage, see the fix commit. There is no
`MirInst::BoxBool`; that asymmetry is what left this gap open, and adding one
would remove the whole class.

## OPEN — pure-Simple parity gap

`src/compiler/` has the same gap, and it must be closed before the pure-Simple
binary becomes the default tool (`.claude/rules/bootstrap.md`).

- A correct, complete tagger already exists — `box_runtime_value`
  (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`), bool included —
  but it is called only from container/literal sites (dict keys, array
  elements, `literals.spl:79,108,163,174`). **No call site is driven by a
  declared `Any` type.**
- Local `Let`: `src/compiler/50.mir/mir_lowering_stmts.spl` — no box
  (`Any` lowers to `MirType.i64()` at
  `src/compiler/50.mir/_MirLowering/function_lowering.spl`).
- Call args: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
  — the `declared_param_type` match has arms for `Optional`, `Int` and `_`
  only; there is **no `Any` arm**, so nothing boxes there, not even i64/f64.

Pure-Simple surfaces the same defect with a different rendering:
`.to_text()` on an `Any` routes to `rt_raw_i64_to_string`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`), so it
prints `"1"` rather than `<value:0x..>` — quieter, same underlying bug.

Fix shape: give the pure-Simple `Let` lowering and the `declared_param_type`
match an `Any` arm that calls the existing `box_runtime_value`.

## Related, still open

- `box_enum_payload_if_needed` (`lowering_expr_call.rs`) routes `TypeId::BOOL`
  through `BoxInt`, which by the tag argument above produces a tagged int, not
  a bool. An enum payload holding a bool should render `"true"`, not `"1"`.
  Not fixed here — it needs its own repro and arm.
