# native-build loses a static method's owner name -> "undefined variable Widget"

- **Filed:** 2026-08-17
- **Lane:** `native-build` (AOT MIR lowering). NOT the tree-walk interpreter, NOT the Cranelift JIT.
- **Blast radius:** blocked EVERY push repo-wide, via the mandatory pre-push guard
  `scripts/check/check-native-trailing-default-param.shs`.
- **Binary used for all measurements:** `bin/release/x86_64-unknown-linux-gnu/simple`,
  59536728 bytes, mtime 2026-08-16 22:59:37 (the Rust seed; it says so on stderr).

## Symptom

```
error: MIR lowering error: undefined variable Widget
```

raised while native-building `test/fixtures/native_trailing_default_param/main.spl`,
in which `class Widget` is defined at `:27` and used at `:52` and `:56`. The
fixture had been unchanged since 2026-08-11.

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1071-1085`.

`static_receiver_name` is the "this receiver is a bare type name, i.e. a STATIC
call" signal. It was recovered ONLY by resolving the receiver `NamedVar`'s
attached symbol id:

```
case NamedVar(static_symbol, static_name):
    val static_def = self.symbols.get_symbol_raw(static_symbol.id)
    ...
```

Under `native-build` that symbol id is frequently unresolved, so `get_symbol_raw`
returns nil and `static_receiver_name` stays `""` -- **even though the `NamedVar`
arm already carries the literal source text `"Widget"` in `static_name`, unused.**

Consequences, in order:

1. With the owner empty, the `Unresolved` method-call arm never builds the
   `static::Widget::stat` key and never reaches `lookup_method_in_type`
   (`:2670-2684`), so `static_method_id` stays nil.
2. It therefore falls through to `self.lower_expr(receiver)` (`:2728`), handing a
   bare class name to the value-lowering path.
3. `Var`/`NamedVar` lowering knows only locals, module globals and two hardcoded
   constants, so it reports
   `expr_dispatch.spl:3267  self.error("undefined variable " + named_var_name, ...)`.

Note that `self.error` **records and returns a const 0** rather than aborting.
That is why the trace continues past the failure and the error text appears
adjacent to a LATER method (`greet`) in the log -- which sent two earlier
investigations after the wrong call. The error genuinely originates at
`Widget.stat(2)`.

## Fix

Add a name-derived fallback in the `NamedVar` arm: resolve `static_name` in the
symbol table and accept it as an owner only when it resolves to a
`Class | Struct | Enum | Import` -- the same kind test the symbol-id path already
applies, so a local variable shadowing a type name can never be mistaken for a
static receiver.

Note the general lesson, which is reusable well beyond this bug:
**`self.error` records the diagnostic and returns a const 0 rather than
aborting.** Lowering therefore continues past the failure, and the message
surfaces in the log next to a LATER method than the one that caused it. This
misled two separate investigations into blaming `greet` (a trait call) when the
defect was in `Widget.stat`. Never infer the failing call site from the message's
position in a deferred-diagnostic log.

## The fix has TWO halves — the first alone is not sufficient

Measured. With only the owner-NAME fallback in place:

```
[mir-method-call] unresolved-static method=stat srn='Widget' disc=1337030607 found=false
```

The owner was recovered correctly (`srn` went from `''` to `'Widget'`) and the
method **still did not resolve**, because the lookup at `:2670-2684` goes through
`static_receiver_symbol` — the receiver NamedVar's attached symbol id, which is
the very id that is unresolved on this lane. So a second half is required:
re-resolve the owner BY NAME (`lookup_or_invalid`) and look the method up in it
via `lookup_method_in_type`, accepting only a `Function` symbol. This mirrors
what the instance-method recovery at `:2767-2770` already does.

Also note an interaction: a sibling lane landed a widening of the
`static_receiver_kind_disc < 0` guard to `... or static_receiver_name == ""`
(commit `05d99eb79e4`, "fix a dead native guard"). Once the owner name is
recovered, `static_receiver_name` is no longer `""`, so that widening stops
firing for this call. The two changes are complementary but the second one
silently disarms the first; both are kept, and the name-derived lookup is
ordered BEFORE the widening so the precise answer wins over the unique-leaf
heuristic.

## Ablation — PARTIAL, and explicitly not green

| tree state | guard result |
|---|---|
| unmodified (origin content) | FAIL, `undefined variable Widget` |
| heuristic variant (unique-leaf widening) | error text **gone**, `found=true`; build advanced past MIR lowering to `native_compile` |
| heuristic removed again | FAIL returns, identical message |
| owner-name fallback only | `srn='Widget'` but `found=false`; `undefined variable` still present (4 occurrences) |
| owner-name fallback + name-derived lookup | **UNVERIFIED at time of commit** — the confirming run had not returned |

The last row is the shipped state. It is committed **unconfirmed**, deliberately:
this tree loses uncommitted work (see below), so committing early is the lesser
risk. It must not be described as green until that run reports.

## Adjacent defects found and NOT fixed here

Each of the first two has its own row; they are summarised here only for context.

1. **`rt_enum_discriminant(receiver.kind)` returns garbage on the native lane.**
   `disc=1337030607` for EVERY receiver shape. Filed as
   `rt_enum_discriminant_returns_garbage_constant_native_lane_2026-08-17.md`.
2. **`native_compile` can fail a unit with no diagnostic at all**, with the
   stderr truncator dropping 55884 of 67884 bytes from the MIDDLE. Filed as
   `native_compile_fails_with_no_diagnostic_stderr_truncated_from_middle_2026-08-17.md`.
3. **The guard exits 1 with ZERO output when `bin/simple` is absent** (`set -eu`
   plus a bare `test -x`). It should be `ERROR — nothing was checked`, exit 2.
4. **`src/compiler/50.mir/verification_semantic_coverage.spl` was clobbered in the
   WORKING TREE** back to the multi-line trailing-pipe `case` form that cannot
   parse, while `HEAD` (`010c878e208`) carried the joined, working form. Restored
   from HEAD. This breaks any native-build that loads that file, but ablation
   proved it is **not** this guard's blocker.

## Specs

- `test/01_unit/compiler/native/native_static_method_owner_resolution_spec.spl`
  -- reproducing spec, with `test/fixtures/native_static_method_owner/main.spl`.
- `test/01_unit/compiler/native/native_interpreter_owner_resolution_parity_spec.spl`
  -- similar-problem detection for the CLASS: owner/static resolution diverging
  between the native and interpreter lowering lanes, measured differentially
  against the interpreter as oracle rather than against hardcoded strings.
