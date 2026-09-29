# A type annotation naming an unimported / dotted-path type silently becomes ANY — no diagnostic, no error

**Date:** 2026-09-25
**Status:** Open — root-caused with a minimal repro, fix proposed, NOT implemented (a bootstrap is running; seed policy change is an owner decision)
**Found while:** fixing stage2 full-CLI build failures (WP-E, `work/stage2-cli-wpe-20260924`) — two rounds of `val x: T = …` annotations silently had no effect because `T` was never imported into the file, and the resulting error ("cannot infer field type … struct 'ANY' field 'x'") gives no hint that the annotation itself is the problem.

## Summary

`val x: T = expr` (also function parameter/return type annotations) is supposed to give the receiver a known static type so later field access can be checked. When `T` cannot be resolved by exact in-scope name lookup — because it was never `use`-imported, or because it is written as a dotted/fully-qualified path — the **Rust seed**, under the `lenient_types` mode that `native-build` always enables, silently falls back to `TypeId::ANY` instead of reporting an error. The annotation is accepted syntactically, produces no warning, and the binding behaves exactly as if it had no annotation at all. The failure only surfaces much later and far away, as a confusing `cannot infer field type … struct 'ANY' field '<f>'` when the erased value's field is finally read — a message that never mentions the annotation or the type name that failed to resolve.

This defect class hid two full rounds of otherwise-correct fixes in the WP-E stage2 package: `val shorthand: BackgroundShorthand = …` and `val c: std.common.color.types.Color = …` were both syntactically valid, semantically exactly what the documented fix technique calls for ("annotate the receiver's binding"), and both silently did nothing.

## Minimal 2-file repro (empirically verified against the deployed Rust seed)

`defs.spl`:
```
class Widget:
    valid: bool
    count: i32

fn make_widget(n: i32) -> Widget:
    Widget(valid: n > 0, count: n)
```

`main.spl` (same directory, **no `use` importing `Widget`** — `make_widget` itself resolves fine via same-project call resolution, exactly like `_parse_background_shorthand` did in the real WP-E file):
```
fn use_widget(n: i32) -> bool:
    val w: Widget = make_widget(n)
    w.valid
```

Command (binary: the Rust seed, `simple.exe`, copied out of a running bootstrap per `.claude/rules/bootstrap.md` guidance — never write inside the live bootstrap tree):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_DEBUG_FIELD_FAIL=1 \
  simple.exe native-build --source . --entry main.spl -o out.exe
```

Observed (verbatim):
```
[FIELD-FAIL] field='valid' struct='ANY' candidates=[] has_known_method=false ambiguous=false

FAILED FILES (1):
  - main.spl => main.spl: main.spl: hir: Unsupported feature: cannot infer field type while lowering use_widget: struct 'ANY' field 'valid'
```

No diagnostic ever names `Widget`, the annotation, or the fact that resolution fell back to ANY. **Fix**: add `use defs.{Widget}` to `main.spl` — the `cannot infer field type` error disappears entirely (compilation proceeds past HIR lowering to the link stage, which is where an unrelated, pre-existing environment gap — this host's `gcc` doesn't accept `--target=x86_64-w64-windows-gnu` — stops it; that is out of scope for this bug and is not evidence against the fix).

**Second variant, same defect, dotted path instead of a missing import** (mirrors `val c: std.common.color.types.Color = …` from the real WP-E fix):
```
fn use_widget(n: i32) -> bool:
    val w: defs.Widget = make_widget(n)
    w.valid
```
Produces the byte-identical `[FIELD-FAIL] field='valid' struct='ANY' …` output. A dotted/qualified type spelling in annotation position never resolves via the exact-name lookup either (see Root Cause), regardless of whether the target is imported.

## Root cause

### Rust seed (`src/compiler_rust`) — CONFIRMED, this is where the repro above runs

1. `native-build` unconditionally puts the lowerer in lenient mode:
   `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:690`
   ```rust
   lowerer.set_lenient_types(true);
   ```
2. A `let`/`val` statement's declared annotation is resolved through `resolve_type` and its result is propagated with `?`:
   `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:378-380`
   ```rust
   let mut ty = if let Some(t) = &let_stmt.ty {
       self.resolve_type(t)?
   ```
   If `resolve_type` returned `Err`, this line would hard-fail the statement with a real diagnostic naming the type. It never does, because of (3).
3. `resolve_type`'s `Type::Simple(name)` arm (`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:248-396`) tries, in order: a type alias, `Self`, exact lookup in `self.module.types` (**this is the only branch that succeeds for an imported name** — confirmed: after adding `use defs.{Widget}` the repro's error disappears), a single-uppercase-letter generic-param shortcut, a whole-program `global_struct_defs`/`duplicate_global_struct_defs` fallback (keyed by **bare** name, so it never matches a dotted path like `defs.Widget` or `std.common.color.types.Color`), and a handful of hardcoded bare keywords (`unit`, `list`, `tuple`, `Dict`, `Option`, `Result`, `usize`, `u128`, …). When **none** of these match, the final branch is:
   ```rust
   if self.lenient_types {
       // In lenient mode, treat unknown types as ANY to allow compilation to proceed
       return Ok(TypeId::ANY);
   }
   let available_types = self.module.types.all_type_names();
   Err(LowerError::UnknownType { type_name: name.to_string(), available_types })
   ```
   (`type_resolver.rs:387-395`). Under `lenient_types` (always true for `native-build`, and therefore true for the stage2 self-compilation build that surfaced this) this is an unconditional, silent `Ok(ANY)` — no warning is emitted, unlike several *other* `lenient_types` fallbacks in this same codebase (e.g. `expr/mod.rs` and `lenient_global_diag.rs` explicitly track and can report names that got the lenient treatment for *identifiers*; no equivalent tracking exists for *type annotations*).
4. The erased `TypeId::ANY` binding later reaches `hir/lower/expr/access.rs`. `get_field_info` fails, `receiver_is_dynamic` is computed as `recv_hir.ty == TypeId::ANY` (`access.rs:288-289`) — true — and, because no whole-program-unambiguous candidate exists for a field named `valid`/`r`/`type_` (many structs share these names), the whole-program candidate search at `access.rs:404-456` also fails, producing the `Unsupported("cannot infer field type while lowering {func}: struct '{struct_name}' field '{field}'")` at `access.rs:447-450` — where `struct_name` at this point is literally the string `"ANY"`. This is the exact message shape (`struct 'ANY' field 'x'`) documented in `doc/08_tracking/bug/` and CLAUDE.md's stage2 fix-package notes.

Net effect: an author who follows the documented fix technique ("annotate the receiver's binding with its known concrete type") gets **no feedback** when the annotation itself fails to resolve — the compiler accepts the annotation, silently discards it, and reports a defect three steps removed from the actual cause, naming neither the annotation nor the type.

### Pure-Simple frontend (`src/compiler/20.hir/hir_lowering/types.spl`) — NOT reproduced the same way; **not independently verified against a running self-hosted binary in this session**

`lower_type`'s `Type::Simple`-equivalent arm (`types.spl:1188-1310`) has a structurally different fallback chain. After the same seed-parity special cases (single-uppercase generic param, bare `tuple`, bare `Map`/`HashMap`/`dict`/`set`, and a documented non-seed-parity capitalized-alias block for `Int`/`Bool`/`Char`), the **final** `else` branch is:
```
else:
    if name == "Any" or (name == "Option" and hir_args.len() == 0):
        self.recovered("unresolved type: {name}", span)
    else:
        ...
        self.error("unresolved type: {name}", span)
    HirTypeKind.Error
```
(`types.spl:1298-1310`) — a genuinely unresolvable name is a **hard error** (`self.error`), not a silent `Any`. There is no `lenient_types`-style unconditional ANY fallback for type annotations in this file.

However, this does **not** by itself prove the pure-Simple frontend is immune to the WP-E symptom, for two reasons this record does not resolve:
- `val symbol_id = self.symbols.lookup_or_invalid(name)` (`types.spl:1189`) is a lookup against `self.symbols` — it is not established here whether that symbol table is scoped per-file (requiring an explicit import, like the seed's `self.module.types.lookup`) or is a whole-program/global table (in which case an unimported same-project type name might resolve correctly with no bug at all, which would make this entirely a seed-only defect). Determining this needs reading the `symbols` construction/population path, which this record did not trace.
- No self-hosted `bin/simple`/`bin/release/<triple>/simple` was available in this session to run the minimal repro above end-to-end on the pure-Simple compiler and observe actual behavior. Everything in this subsection is source-reading, not measurement.

**Whoever picks this up should re-run the exact 2-file repro above through a deployed self-hosted binary before assuming either "also broken" or "already fine."**

## Proposed fix (NOT implemented here — a bootstrap is running; this is a seed-policy change, an owner decision per this repo's bootstrap safety rules)

Do not weaken `lenient_types` globally — it exists to let `native-build` push through legitimate dynamic/erased code paths, and much of the surrounding code (bare `Dict`, `Option`, container fallbacks) depends on it staying permissive for expression-position and inferred typing. The narrower, targeted fix:

1. **Distinguish annotation position from inferred position.** `resolve_type` is called both for explicit, author-written annotations (`let_stmt.ty`, fn parameter/return types) and for internally-synthesized/inferred type queries. Only the former should be strict. Thread a `strict_annotations: bool` (or an explicit `resolve_type_annotation` entry point that never takes the `lenient_types` early-return at `type_resolver.rs:387-389`) so that a `Type::Simple(name)` reaching the final fallback while lowering an EXPLICIT annotation always returns `Err(LowerError::UnknownType { type_name, available_types })`, propagated by the existing `?` at `stmt_lowering.rs:380` (and the equivalent call sites for function signatures) — turning today's silent no-op into the same kind of real, located compile error the pure-Simple frontend already produces for a truly-unresolvable name.
2. **Cheaper, non-breaking first step**, if (1) is judged too risky to land before/near a bootstrap: keep returning `Ok(TypeId::ANY)` under `lenient_types`, but emit a diagnostic (`eprintln!`, mirroring the existing `lenient_global_diag.rs` machinery for identifiers) naming the unresolved annotation type, the file, and the span, every time this fallback fires for an annotation. This changes no pass/fail behavior for any existing green build, so it cannot regress a build that currently depends on the lenient fallback — it only makes the silent case loud enough for a human (or a lint) to catch before it wastes another round of "the fix had no effect."
3. Either way, the fix must special-case the two known-safe uses of this same fallback path that are NOT annotation-shaped and must keep working exactly as today: the bare-keyword arms (`Dict`, `Option`, `Result`, `usize`, `u128`, …) at `type_resolver.rs:319-386`, and the cross-module `global_struct_defs`/`duplicate_global_struct_defs` recoveries at lines 279-317, which are deliberate, working fallbacks for a *different* problem (ambiguous or unimported but real cross-module structs) and must not be turned into hard errors by this change.
4. Apply the pure-Simple twin's existing hard-error behavior (`types.spl:1298-1310`) as the target shape once the symbol-table question above is resolved — if `self.symbols.lookup_or_invalid` turns out to already require an import, the pure-Simple frontend needs no fix at all for the annotation case; if it resolves globally regardless of import, the two compilers disagree structurally on what "resolvable" means, which is a separate finding worth its own bug record.

## Cross-reference

This is the underlying defect explaining the "round 1 fixes had no effect" surprise recorded against `work/stage2-cli-wpe-20260924` (commit `1c44b1b5853`): `BackgroundShorthand`, `GradientStopSpec`, `BoxShadowAgg` (bare, unimported names) and `std.common.color.types.Color` (dotted path) all fell into this exact fallback; adding explicit `use` imports for the bare names, and an `as`-aliased import in place of the dotted path, worked because `self.module.types.lookup(name)` — the ONE branch that returns a real type without going through the lenient fallback — only succeeds for an exact in-scope name.
