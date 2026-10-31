# Erased `T` value passed to a declared scalar parameter keeps its tag (Rust seed, 2026-10-31)

**Found by:** multi-file native-build repro (`Box<i64>` field read passed to
`fn double_it(x: i64)`), Rust seed at `6f174e52eda` and release/1.0.0 head
`1e5e681d869` (identical `mir/lower` code; `SIMPLE_NATIVE_BUILD_RUST=1`,
`--backend llvm`, aarch64-apple-darwin).
**Status:** FIXED in `coerce_args_for_param_slots`
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs`).

## Reproduce (smallest)
```simple
struct Box<T>:
    value: T
fn double_it(x: i64) -> i64:
    x * 2
fn main():
    val a: Box<i64> = Box(value: 21)
    print "doubled={double_it(a.value)}"   # 336 pre-fix, 42 expected
    print "box_i64={a.value}"              # 21 (print is an ANY consumer)
    print "literal={double_it(21)}"        # 42 (raw literal)
```
Variants (pre-fix seed, same mechanism): `val y = a.value; double_it(y)` ->
336; `double_it(id(7))` with `fn id<T>(x: T) -> T` -> 112; `val x: i64 =
a.value; double_it(x)` -> 42 (the typed `val` boundary already decoded).

## Root cause
A generic type parameter erases to `TypeId::ANY` (hir/lower/type_resolver.rs),
so `a.value` has static type ANY and the field slot stores a TAGGED word
(`box_scalar_for_tagged_slot` at struct init). Every other typed boundary
already mirrors that: `val`/`var` bind (lowering_stmt.rs), `return`, and `if`
merges call `unbox_scalar_for_raw_slot`. The call-argument boundary did not:
`box_args_for_any_params` only ran raw->tagged (`box_arg_for_any_param`) for
ANY parameters and left a tagged argument bound to a raw `i64`/`f64`/`u64`
parameter untouched, so the callee computed on `21 << 3`. `print` untags, which
is why the field read "looked" right and only the call was wrong.

The sibling `bool` boundary had its own defect: `coerce_args_for_bool_params`
decoded a dynamic argument with `rt_is_some` alone, so a tagged `false`
(present, non-nil) read as `true`. The interpreter rule
(`present_value_as_bool_arg`) keeps a real bool and applies presence to the
rest.

## Fix
- `coerce_args_for_param_slots` (lowering_expr_call.rs): one pass over the
  declared parameter list that boxes raw->tagged (as before) AND unboxes
  tagged->raw through `unbox_scalar_for_raw_slot` (int/float/u64), skipping
  ANY-typed raw literals. Used by direct calls (`box_args_for_any_params`),
  method calls (`box_method_args_for_any_params`) and callable fields.
- `present_any_as_bool_arg`: `rt_value_is_bool(v) ? rt_value_truthy(v) :
  rt_is_some(v)` for a dynamic argument bound to `bool`.
- Not touched: HIR typing of erased field reads (the slot stores tagged by
  design) and `FieldGet` codegen.

## Not covered here
- The bare `IndirectCall` path (closure value with no signature) runs neither
  direction; it has no declared parameter list to coerce against.
- The self-hosted compiler (`src/compiler/50.mir`) has a sibling gap: the
  direct-call unbox gate in `_MirLoweringExpr/switch_operators_calls.spl`
  (`hir_type_is_plain_scalar` arm) only fires for locals with a recorded
  `Any` HIR type that are marked runtime values, which an erased field read
  never meets, and `lower_method_call_arg` (mir_lowering_stmts.spl) has no
  unbox at all. Not fixed in this change; untested because the stage2 Simple
  binary refuses non-bootstrap entries in the available environment.

## Regression cover
- `src/compiler_rust/compiler/src/mir/lower/tests/erased_arg_scalar_param_tests.rs`
- `test/fixtures/jit_differential/erased_arg_scalar_param.spl` +
  `scripts/check/check_jit_interpreter_differential.spl` entry
- `test/01_unit/compiler/jit_erased_arg_scalar_param_spec.spl` (authored;
  unexecuted until run)
