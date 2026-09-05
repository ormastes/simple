# Placeholder-lambda (`_1`) scoping breaks for an ordinary call nested inside another call's argument

Status: OPEN (parser bug in the Rust seed, `src/compiler_rust`)
Filed: 2026-08-31
Discovered while: getting `test/01_unit/lib/std/common/text_helpers_spec.spl` test-clean on Windows (bin/simple.exe seed, 28,291,570 bytes, 2026-08-24)

## Symptom

```simple
expect(index_of_func("hello", _1 == "l")).to_equal(2)
```

fails with `expected <lambda> to equal 2` — `expect()`'s argument evaluates to
a **lambda object**, not the `i64?` that `index_of_func` returns. The bug
disappears when the placeholder expression is hoisted to its own statement:

```simple
val pred = _1 == "l"
expect(index_of_func("hello", pred)).to_equal(2)   # passes: actual = 2
```

or when an explicit lambda is used inline:

```simple
expect(index_of_func("hello", \c: c == "l")).to_equal(2)   # passes
```

Reproduced standalone (not test-runner-specific) with a minimal repro file
and also with `fields_func("a  b", _1 == " ")` used inline inside
`expect(...).len()` — same failure, so this is general, not specific to
`index_of_func`.

## Root cause

`src/compiler_rust/parser/src/expressions/postfix.rs`,
`transform_placeholder_args_for_call` (called once per call's argument list,
right after its arguments are parsed):

```rust
fn transform_placeholder_args_for_call(&self, callee: &Expr, args: &mut [Argument]) {
    if Self::expr_is_higher_order_callee(callee) {
        // force_transform_placeholder_lambda on each arg, immediately
        return;
    }
    if self.call_arg_depth > 0 {
        return;   // <-- defers to whichever call finishes parsing its
                  //     argument next, regardless of what that call is
    }
    // transform_placeholder_lambda on each arg
}
```

`name_is_higher_order_callback_callee` (same file, ~line 71) is a hardcoded
name list (`map`, `filter`, `reduce`, `fold`, `each`, ... plus `_map`/
`_filter`/`_any`/`_all`/`_each` suffixes). `index_of_func`, `last_index_of_func`
and `fields_func` (`src/lib/common/text_advanced.spl:1185,1199,1217`) are
ordinary free functions that take a `pred: fn(text) -> bool` parameter — they
are exactly the kind of call a placeholder argument should bind to, but their
names don't match the list (no `_func`-suffix rule exists), so they fall into
the `call_arg_depth > 0` branch.

`call_arg_depth` is a **plain nesting counter**, incremented while parsing
*any* argument's value expression
(`src/compiler_rust/parser/src/expressions/helpers.rs:577-579`), not a stack
that records *which* enclosing call is higher-order. So when
`index_of_func(...)` is itself an argument being parsed for `expect(...)`,
`call_arg_depth` is `> 0` at the point `index_of_func`'s own args finish
parsing, and its placeholder-consumption is skipped — deferred to whatever
call is currently mid-argument-parse. That happens to be `expect(...)`, whose
own argument-transform step (`transform_placeholder_lambda`, since `expect`
is also not higher-order but runs at depth 0 once `index_of_func`'s call
returns) then sees the leftover placeholder and wraps the **entire**
`index_of_func("hello", _1 == "l")` argument into a lambda — which is why
`expect()` receives `<lambda>` instead of a value.

The bubble-up-to-the-outer-call design is deliberate for genuine higher-order
nesting, e.g. `xs.map(int(_1) + 5)` (comment at
`placeholder.rs:43-46`: "ordinary calls like `int(_1)` keep `_1` available
for the enclosing placeholder expression"). The bug is that the deferral
condition (`call_arg_depth > 0`) does not distinguish "nested inside a
higher-order call's argument, so keep bubbling" from "nested inside an
ordinary call's argument (`expect`, a `val` RHS, etc.), so this is not a
lambda context at all" — it treats every enclosing call the same.

Same failure mode independently confirmed via `var_decl.rs:369,397`
(`force_transform_placeholder_lambda` applied to a whole `val`/`var` RHS): a
top-level `val r = index_of_func("hello", _1 == "l")` also turns the entire
RHS into a lambda rather than calling `index_of_func` — `r` never becomes an
`i64?`. Same root cause (placeholder search does not stop at the syntactic
call whose parameter is actually a callback), reached from a different call
site.

## Suggested fix (not applied — Rust-seed change, out of scope for this pass)

Add `index_of_func`, `last_index_of_func`, `fields_func` (the only 3 free
functions under `src/lib` with a `pred: fn(...) -> bool` parameter as of this
writing, per `grep -rn 'fn [a-zA-Z_]*_func(' src/lib`) to
`name_is_higher_order_callback_callee`, or add a general suffix rule. A
suffix rule (e.g. `name.ends_with("_func")`) is broader and would also match
unrelated names such as `parse_hsl_func`, `canvas_webgl_depth_func`,
`webgl_valid_stencil_func` (GL enum setters, not callback consumers) — safe in
practice since `force_transform_placeholder_lambda` is a no-op on an argument
with no placeholder, but an explicit name list is more precise. This requires
a Rust-seed rebuild + redeploy (`cd src/compiler_rust && cargo build --release
--bin simple`), which was not done here — see `.claude/rules/bootstrap.md`
"Seed-sibling refresh" for the deploy protocol.

## Workaround applied

`test/01_unit/lib/std/common/text_helpers_spec.spl`'s `index_of_func` /
`last_index_of_func` describe-blocks now use explicit lambda syntax
(`\c: c == "l"`) instead of the inline placeholder form. This is not a test
correctness fix (the placeholder form was not testing the wrong thing) — it
sidesteps a real parser limitation using a syntax form already used
elsewhere in the same file (including `index_of_func`'s own `sdoctest`) and
already known to work.
