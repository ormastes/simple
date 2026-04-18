# Compiler RFC: Context-Inferred Bare Enum Literals

**Status:** Proposed
**Created:** 2026-04-17
**Track:** Phase 9 — Compiler RFC Track
**Related:** `doc/05_design/ui_typed_core_rfc.md` §4.2, §5, §9
**See also:** `doc/05_design/compiler_rfc_ufcs.md`, `doc/05_design/compiler_rfc_method_chain_fix.md`

---

## 1. Motivation

Today every enum literal must be fully qualified:

```simple
Toast(msg, duration, StatusVariant.Success)
node.padding(Spacing.Md)
node.accent(Accent.Primary)
```

When the call site already constrains the type — a typed function parameter, a struct field initializer, a return position, an assignment to a typed variable — the qualifier is redundant. Slint, Kotlin, and Swift all allow context-inferred enum cases; they have not reported user confusion.

For the UI library, every fluent-modifier call involves at least one enum argument. The qualification noise multiplies across Phase 3–6 builder chains:

```simple
# Today (required)
Button("save", "Save").accent(Accent.Primary).padding(Spacing.Md).border(BorderStyleKind.Rounded)

# Goal (with bare literals)
Button("save", "Save").accent(Primary).padding(Md).border(Rounded)
```

---

## 2. Proposed Design

### 2.1 Resolution rule

When the typechecker encounters a **bare identifier** `X` in a position where the expected type is a known enum `E`:

1. Check whether `E` has a case named `X`.
2. If yes, resolve `X` to `E.X` and proceed as if the user wrote the qualified form.
3. If `E` has no case named `X`, fall through to normal name resolution (variable, function, etc.).

### 2.2 Inference positions

Bare literal inference fires in any position where the expected type is known before the expression is typed:

| Position | Example |
|----------|---------|
| Typed function argument | `toast(msg, StatusVariant.Success)` → `toast(msg, Success)` |
| Struct / class field initializer | `MyState(variant: Success)` |
| Return from typed function | `fn get() -> StatusVariant: Success` |
| Assignment to typed `val`/`var` | `val v: StatusVariant = Success` |
| Match arm RHS (expected from branch) | where branch type is pinned |

Positions where the expected type is **not** known (bare expression, polymorphic context) do **not** trigger inference — the identifier resolves normally.

### 2.3 Ambiguity rule

If two or more enums in scope both define a case with the same bare name `X`, and the expected type is unresolved at that position:

- Emit an `ambiguous bare enum literal` diagnostic.
- List all candidate enums and their qualified forms.
- Require either: explicit qualification (`StatusVariant.Success`) or an `as`-cast (`Success as StatusVariant`).

When the expected type **is** resolved unambiguously, no diagnostic is needed even if another enum happens to have the same case name — the expected type wins.

### 2.4 Escape hatch

```simple
Success as StatusVariant   # explicit qualification via cast syntax
```

Useful when ambiguity exists or when the author wants to make the type visible in a long chain.

---

## 3. Compatibility

Strictly additive. All existing qualified literals (`StatusVariant.Success`) continue to work unchanged. Bare forms are opt-in by context. No existing code breaks.

The only semantic change is that a previously-erroneous bare identifier `X` in a typed position now resolves to an enum case rather than emitting "unknown identifier". If a variable named `X` and an enum case `E.X` are both in scope and the expected type is `E`, the enum case wins (the expected type provides the tiebreak). If the variable is genuinely intended, the user writes `(x)` explicitly or assigns to an untyped intermediate.

---

## 4. Implementation Pointer

Target: **`src/compiler/30.types/`** — specifically `bidirectional_checking.spl` and `bidirectional_inferencer.spl`, which already implement check-mode (expected type flows into expression typing per `bidirectional_type_checking_design.md`). Bare enum inference is a natural extension of check-mode: when checking an identifier against an enum expected type, consult the enum's case list before falling through to scope lookup.

Secondary touch: **`src/compiler/35.semantics/`** — name resolution scope walk must expose enum cases as candidates when the expected type is an enum.

No parser changes required. Bare identifiers already parse as `Ident` nodes; the distinction is made entirely at resolution time.

---

## 5. Interaction with Design Tokens

Phase 4 introduced design tokens (`Spacing`, `Radius`, `FontWeight`, etc.) as enums. With bare literal inference:

```simple
node.padding(Md)       # resolves to Spacing.Md  (param type: Spacing)
node.radius(Lg)        # resolves to Radius.Lg   (param type: Radius)
node.weight(Bold)      # resolves to FontWeight.Bold
```

This removes the most verbose part of token-resolution call sites without any library change.

---

## 6. Migration Impact

No required migration. Existing qualified literals keep working. Teams can adopt bare form incrementally, file by file. The linter (Phase 8) may optionally add a `prefer-bare-enum` suggestion rule, but that is out of scope for this RFC.

---

## 7. Acceptance Criteria

- `fn f(v: StatusVariant): ...` compiles when called as `f(Success)`.
- `val x: StatusVariant = Success` compiles.
- Explicit qualification `StatusVariant.Success` still compiles everywhere it does today.
- Ambiguity diagnostic fires when two in-scope enums share a case name and the expected type is unresolved.
- No existing test regresses.
- Bare identifier in an untyped position (no expected type) resolves as before — no silent enum injection.

---

### Audit findings (Phase 9 investigation 2026-04-17)

#### 1. What exists today

**Parser:** No distinction between a bare `Success` reference and `StatusVariant.Success` at parse time.
Both become `Ident("Success")` nodes. The AST node `EnumLit(type_, variant, payload)` only appears
after a pass has already resolved the qualified form; the parser never emits it for bare identifiers.
Confirmed: `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs` and
`src/compiler/35.semantics/resolve.spl:475-490` — `EnumLit` is handled in resolution, not parsing.

**Bidirectional checker (`src/compiler/30.types/type_system/bidirectional.spl`):**
`InferMode` / `check_expr` infrastructure exists (lines ~60-280). `check_expr` propagates expected
types for Integer, Float, Lambda, Call arguments, Tuple, Array, Dict. The `Call` arm (line ~200)
already passes each argument through `check_expr(args[i], param_types[i])` — i.e., expected-type
flow into call arguments is implemented. **However, there is no `case Ident(name):` arm in
`check_expr`.** Bare identifier resolution falls through to the default `case _:` which calls
`synthesize_expr` then unifies — it never checks whether the expected type is an enum and `name`
is one of its cases.

`bidirectional_inferencer.spl:109` has `case Var(_): HirType.Int  # Placeholder` — a placeholder,
not a stubbed-out real implementation.

**`src/compiler/30.types/__init__.spl:6`** exports `TypeInferencer`, so the bidirectional engine
*is* wired into the compiler pipeline (unlike the UFCS `resolve_methods()` stub). But the missing
`Ident` arm means enum inference never fires.

**`src/compiler/35.semantics/resolve.spl:475-490`:** Handles already-qualified `EnumLit` nodes —
resolves payload sub-expressions. Has no logic to rewrite a bare `Ident` into an `EnumLit` when
the expected type is an enum.

**Existing enum tests** (`test/feature/usage/enums_spec.spl`, `test/unit/compiler/mir/mir_enum_access_spec.spl`, etc.):
zero use of bare enum forms — every test uses fully qualified `EnumName.Variant` syntax.

#### 2. Stub vs. fully implemented

This is **not** the UFCS pattern (impl written, entry point stubbed). The bidirectional
infrastructure (InferMode, check_expr dispatch, expected-type propagation through Call args) is
genuinely wired and running. The missing piece is a single rule that was never written: no code
anywhere checks "is this `Ident` in a position where the expected type is an enum, and if so, is
the name one of that enum's cases?" The fix requires new logic, not unstubbing an existing function.

#### 3. Concrete reproducer

```simple
# /tmp/bare_enum_repro3.spl
enum StatusVariant:
    Success
    Warning
    Error

fn show(v: StatusVariant) -> text:
    match v:
        Success: "ok"
        Warning: "warn"
        Error:   "err"

fn test():
    val s = show(Success)
    print s

test()
```

`bin/simple check /tmp/bare_enum_repro3.spl` → **`OK`** (parse-only; the Rust seed `check_file`
at `src/compiler_rust/driver/src/cli/check.rs:137-180` does parse + validate_imports only — no
type checking — so "OK" is not evidence of correctness).

`bin/simple run /tmp/bare_enum_repro3.spl` → **`error: semantic: variable 'Success' not found`**

This is the ground-truth result: bare enum literals fail at interpreter resolution time.

#### 4. Where the fix would go

Primary: `src/compiler/30.types/type_system/bidirectional.spl` — add a `case Ident(name):`
arm to `check_expr`:

```
case Ident(name):
    match expected:
        case Enum(enum_name, cases):
            if cases.contains(name):
                # Rewrite: treat as if user wrote EnumLit(enum_name, name, None)
                Ok(expected)
            else:
                # Fall through to normal synthesis + unify
                val inferred = synthesize_expr(engine, expr, env)?
                engine_unify(engine, inferred, expected)?
                Ok(expected)
        case _:
            val inferred = synthesize_expr(engine, expr, env)?
            engine_unify(engine, inferred, expected)?
            Ok(expected)
```

Secondary: `src/compiler/35.semantics/resolve.spl` — when `check_expr` rewrites an `Ident` to
an `EnumLit` node, the resolver's existing `EnumLit` arm (line 475) handles downstream resolution
already. No parser changes needed (confirmed by this RFC §4).

Size: **small-to-medium** — the bidirectional arm is ~15 lines; the secondary concern is whether
`check_expr` result feeds back into the HIR being lowered (needs verification that the rewritten
node is emitted, not just type-checked against).

#### 5. Status correction

**Recommended status: "Proposed (partial — bidirectional infrastructure exists, enum-literal
inference rule missing)"**

The `InferMode.Check` / `check_expr` machinery is real and wired. Expected-type flow through
`Call` arguments already runs. The single missing piece is the `case Ident` arm in `check_expr`
that recognises an enum context. This is substantively smaller than greenfield but not a one-line
unstub — the rewrite from `Ident` to `EnumLit` in the HIR must be threaded through correctly.

---

## See also

- `doc/05_design/compiler_rfc_ufcs.md` — UFCS dispatch; bare-enum inference
  uses similar bidirectional-checking infrastructure.
- `doc/05_design/compiler_rfc_method_chain_fix.md` — sister Phase 9 item
  for fluent chain syntax.
- `doc/05_design/ui_typed_core_rfc.md` § 4.2 — the original Phase 9
  motivation (UI design tokens, status variants currently require
  qualified form).
