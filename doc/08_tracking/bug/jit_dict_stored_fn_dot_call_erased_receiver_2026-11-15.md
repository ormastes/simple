# JIT: `d.name(args)` on a dict-stored function — typed case fixed, erased receiver still aborts (2026-11-15)

Status: PARTLY FIXED 2026-11-15. Typed receiver fixed; erased/global receiver OPEN.

## Symptom

In compiled code (`simple run` of a file with `fn main`), calling a function
stored in a dict by dot syntax aborted:

```simple
fn always(x: text) -> bool: true
fn main():
    val table = {"q": always}
    print table.q("x")        # Function 'Dict.q' not found
```

The interpreter already called the stored function.

## Fixed: statically typed receiver

`try_lower_dict_stored_fn_call`
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`) rewrites
`d.name(args)` to `d["name"](args)` when the receiver's static type is a `Dict`
whose value type is a function (or `any`) and `name` is not a built-in method.
The result is boxed when the surrounding expression expects a different type.

Witness: `test/01_unit/bugs/dict_of_functions_dot_call_spec.spl` runs
`test/fixtures/dict_fn_dot_call/main.spl` through `simple run`: 0/2 before,
2/2 after.

## Still open: receiver type not known at compile time

Both shapes still abort (`Function 'n' not found` / `'q' not found`):

1. A dict holding functions of different signatures —
   `{"q": always, "n": inc}` — its value type is erased, so the rewrite cannot
   prove the member is a stored function rather than a method.
2. A module-level `val ns = {...}` — the global's HIR type is `any`.

A compile-time rewrite cannot cover these. They need a runtime fallback in
method dispatch: when the receiver is a dict, the name is not a built-in, and
the key holds a callable, call it. Workaround: `ns["q"](args)`.
