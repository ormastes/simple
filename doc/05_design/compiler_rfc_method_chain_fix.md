# Compiler RFC: Fix Chained Method Calls

**Status:** Proposed (bugfix)
**Created:** 2026-04-17
**Track:** Phase 9 — Compiler RFC Track
**Related:** `doc/05_design/ui_typed_core_rfc.md` §4.1, §6, §7, §9
**See also:** `doc/05_design/compiler_rfc_ufcs.md`, `doc/05_design/compiler_rfc_bare_enum_literals.md`
**Constraint source:** `.claude/rules/language.md` — "Chained methods broken — use intermediate `var`"

---

## 1. Problem Statement

Method chaining is broken in Simple today. The workaround documented in `.claude/rules/language.md`:

```simple
# Required today
var btn = Button("save", "Save")
btn = btn.width(120)
btn = btn.height(40)
btn = btn.accent(Accent.Primary)
```

The natural form fails to compile:

```simple
# Does not compile
val btn = Button("save", "Save").width(120).height(40).accent(Accent.Primary)
```

Phase 3 of the UI migration added 26 fluent modifier methods on `WidgetNode`, each with signature `fn method(self: WidgetNode, ...) -> WidgetNode`. They are individually callable. Chaining is not. This RFC is the bug ticket; no prior tracker entry exists.

---

## 2. Minimal Reproducer

The implementer should begin with this reproducer to isolate the layer:

```simple
class Box:
    val x: Int

me wrap(self: Box) -> Box:
    Box(x: self.x + 1)

me double(self: Box) -> Box:
    Box(x: self.x * 2)

val result = Box(x: 1).wrap().double()
# Expected: Box(x: 4)  — wrap gives x=2, double gives x=4
```

This is the simplest possible chain: two methods, both `fn(Self) -> Self`, no generics, no traits. If this fails, the bug is in the fundamental expression-evaluation path.

---

## 3. Root Cause Investigation

The implementer must determine **which layer** drops the chain. Three hypotheses:

### Hypothesis A — Parser (most likely)

The grammar may not admit `.method()` after a call expression. The production for `postfix_expr` may only allow one level of method application before requiring a statement boundary. If `a.b().c()` fails at parse time, the AST for `.c()` is never built.

**Check:** Does the parser produce any AST node for the chain, or does it stop after `.b()`? Inspect `src/compiler/10.frontend/parser/` — the postfix/primary expression rules in the parser source.

### Hypothesis B — Typechecker (possible)

The parser succeeds but the typechecker fails to propagate the return type of `.b()` as the receiver type of `.c()`. This would manifest as "method not found on unknown/unit type" for the second link.

**Check:** Does the typechecker error occur on the second call or does it succeed but produce a wrong type?

### Hypothesis C — Codegen / IR lowering (less likely)

The chain parses and typechecks but the backend fails to allocate a temporary for the intermediate result of `.b()`.

**Check:** Does a desugared `val _tmp = a.b(); _tmp.c()` compile and run correctly? If yes, the bug is upstream of codegen.

---

## 4. Proposed Fix (per hypothesis)

### If Hypothesis A (parser)

Extend the postfix-expression grammar to allow recursive chaining. In `src/compiler/10.frontend/parser/`, the primary/postfix rule likely needs a `*` or recursive production on method-call:

```
postfix_expr := primary_expr postfix_op*
postfix_op   := '.' IDENT '(' args ')'
              | '.' IDENT
              | '[' expr ']'
              | '?'
```

The fix is ensuring `postfix_op*` (zero or more) is the grammar, not `postfix_op?` (zero or one). This is the most common cause of this class of bug.

**Backward-compat check:** Verify that no existing grammar construct is ambiguous with a chain. Attribute access (`obj.field`) already uses `.IDENT` without `()` — the distinction is the presence of `(args)`, which is unambiguous.

### If Hypothesis B (typechecker)

Ensure the return type of a `MethodCall` node is correctly threaded as the receiver type of the next `MethodCall` in the chain. In `src/compiler/30.types/bidirectional_checking.spl`, the infer-expression path for `MethodCall` must synthesize the return type and make it available to the parent postfix expression.

### If Hypothesis C (codegen)

Emit an explicit temporary `let _t = ...` for each intermediate call result in a chain before lowering to the backend IR. Location: `src/compiler/50.mir/` or `src/compiler/60.mir_opt/`.

---

## 5. Risk

**Grammar ambiguity.** If `.method()` parses identically to attribute access followed by a call in some positions, a grammar fix may require backward-compat checks on existing `.field` usages. Expected to be low risk since `(args)` is a syntactic discriminant.

**Interaction with UFCS.** UFCS resolution is per-call-site and fires after the chain is parsed. A chain parse fix does not affect UFCS. However, once both land, `a.b().c()` where `b` and `c` are free functions will work end-to-end.

---

## 6. Acceptance Criteria

- `Box(x: 1).wrap().double()` (the minimal reproducer) compiles, runs, and returns the expected value.
- `Button("save", "Save").width(120).height(40).accent(Accent.Primary)` compiles and is runtime-equivalent to the intermediate-`var` form.
- Chains of length 5+ work (no off-by-one in the recursive grammar rule).
- No existing single-method-call test regresses.

---

### Root cause (Phase 9 investigation 2026-04-17)

#### 1. Minimal reproducer

```simple
class Box:
    val x: i32

fn wrap(self: Box) -> Box:
    Box(x: self.x + 1)

fn double(self: Box) -> Box:
    Box(x: self.x * 2)

fn main():
    val result = Box(x: 1).wrap().double()
    print result.x
```

```
bin/simple run /tmp/chain_repro.spl
# error: semantic: method `wrap` not found on type `Box`
```

The same error fires on a single-link call `Box(x:1).wrap()` — the chain is a
symptom, not the cause. Non-chained `val a = Box(x:1); a.wrap()` works.

#### 2. Layer

**Rust seed interpreter** — not the parser or typechecker. `bin/simple check`
passes; `bin/simple run` fails. The `.spl` Core interpreter is not involved.

#### 3. Specific file:line

`src/compiler_rust/compiler/src/interpreter_method/mod.rs`

- **`evaluate_method_call`** (line 38): dispatches on `Value::Object` at **line 671**.
  After `find_and_exec_method` + `try_method_missing` fail, it calls
  `bail_unknown_method!` at **line 749**. A UFCS fallback (`functions.get(method)`)
  does exist further down at **line 982**, but it is unreachable for `Value::Object`
  because the Object arm exits via `bail_unknown_method!` at line 749 before the
  code reaches line 982.
- **`evaluate_method_call_with_self_update`** (line 1061): **does** have the UFCS
  fallback for `Value::Object` at **line 1105** (`functions.get(method)`).
- The dispatch split is in
  `src/compiler_rust/compiler/src/interpreter/expr/calls.rs` **line 6**:
  if the receiver AST node is `Expr::Identifier`, the `_with_self_update` path
  is taken (UFCS present); any other receiver expression (constructor literal,
  chained call result) falls to plain `evaluate_method_call` (UFCS unreachable
  for `Value::Object`).

#### 4. Fix sketch

In `evaluate_method_call` (`interpreter_method/mod.rs`), add the UFCS fallback
inside the `Value::Object` arm, mirroring the one already in
`evaluate_method_call_with_self_update`:

```rust
// After find_and_exec_method + try_method_missing fail, before bail_unknown_method!:
if let Some(func) = functions.get(method).cloned() {
    let mut arg_values = vec![recv_val.clone()];
    for arg in args {
        let val = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
        arg_values.push(val);
    }
    return exec_function_with_values(&func, &arg_values, env, functions, classes, enums, impl_methods);
}
```

This is ~8 lines duplicated from `_with_self_update`. Alternatively, extract a
shared `try_ufcs_fallback(recv_val, method, ...)` helper and call it from both
functions. Complexity: **small** (single-site Rust change, no grammar or type
system changes needed).

---

## 7. Post-Landing Updates

Once this RFC is implemented and the acceptance criteria pass:

1. Remove "Chained methods broken — use intermediate `var`" from `.claude/rules/language.md`.
2. Update `examples/ui/fluent/method_modifiers_example.spl` to use chain syntax.
3. Update `doc/05_design/ui_typed_core_rfc.md` §4.1 Option B note to say "resolved".
4. Phase 3 examples in `doc/` that show the intermediate-`var` workaround can be updated to chain form.
