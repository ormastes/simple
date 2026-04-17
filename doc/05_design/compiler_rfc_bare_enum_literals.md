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
