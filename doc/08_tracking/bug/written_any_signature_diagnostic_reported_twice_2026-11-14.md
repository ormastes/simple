# Written `Any` in a callable signature is diagnosed twice

- **Status:** FIXED (2026-11-22)
- **Severity:** P3
- **Filed:** 2026-11-14, lane p3-batch-c (Linux aarch64, Rust seed built from
  `release/1.0.0` @ `c541817df822`)
- **Red spec:** `test/01_unit/compiler/30.types/written_any_compile_mode_spec.spl`
  (1 example, fails `assert_equal failed: expected 2, got 4`; it is listed
  without a row in `compiler_unit_sweep_seed_run_open_items_2026-11-12.md`)

## Symptom

`HirLowering` reports `[W-ANY-COMPILE-001]` (lenient) or `[E-ANY-COMPILE-001]`
(strict) **twice** for every `Any` written in a function's parameter or return
type. A local annotation is reported once. Counts from the spec's own
`lowering_diagnostics` harness:

| source | lenient W | strict E |
|---|---|---|
| `fn f(x: Any) -> i64` | 2 | 2 |
| `fn f() -> i64: val v: [Any] = []` (local) | 1 | — |
| `fn f() -> i64: val v: Any = 1` (local) | 1 | — |
| `fn f(a: Any, b: Any) -> i64` | 4 | — |
| `fn f(d: Dict<any, any>) -> i64` | 4 | — |
| `fn f() -> [Any]` | 2 | — |
| `fn f(values: Dict<text, any>) -> [Any]` (the spec's case) | 4 | — |

The rest of the spec (unsafe grant, invalid grant, `__any`, aliases, closure
and block-end scoping, parser fallbacks, generics) passes once this one
assertion is relaxed locally, so the double report is the only defect here.

## Cause

A callable signature is lowered by `lower_type` twice: once to register the
callable's `HirTypeKind.Function` type
(`declared_callable_type` / `declared_surface_callable_type`,
`src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl:473,560`,
called from `module_declarations_bootstrap.spl:301,415,443`,
`trait_impl_lowering.spl:131`, `module_build.spl:563` and
`declaration_lowering.spl:250,252`), and again when the declaration itself is
lowered (`declaration_lowering.spl:410` and the parameter loop). The diagnostic
is raised in `lower_named_kind` (`hir_lowering/types.spl`, `case "Any" | "any"`)
on every lowering.

## Why it was not fixed in this lane

- **Span de-duplication cannot work:** every type node reaching `lower_type`
  carries a zero span (`start=0 end=0 line=0 col=0 file=""`; measured by
  printing the span in the `Any` arm). Distinct occurrences are
  indistinguishable, so de-duplicating would hide real ones.
- **Silencing the registration pass** would only be safe after proving every
  callable it types (externs, trait method signatures, impl statics, imported
  surface callables) is lowered again by declaration lowering. Without that
  proof it would drop the only `Any` diagnostic for some signatures, which is
  widening `Any` acceptance. `Any` stays allowed only inside
  `unsafe(capabilities: [type_erasure])`.

## Acceptance

One diagnostic per written `Any` occurrence at its severity, for signatures as
well as locals, with `fn f(a: Any, b: Any)` and `Dict<any, any>` still
reporting 2. The red spec goes green without changing its assertions. Likely
routes: carry type spans through the flat AST bridge and key the report on
them, or have the registration pass defer `Any` diagnostics to declaration
lowering after proving full coverage.

## Resolution (2026-11-22)

- **Root cause fixed:** Up-front signature/declaration registration (`declared_callable_type`, `declared_surface_callable_type` in `src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl`, and the `module_functions`, `module_constants`, and `module.impls` pre-declaration loops in `src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl`) plus exported-alias private-target re-expansion (`exported_alias_validation_v1` in `src/compiler/20.hir/hir_lowering/types.spl`) now defer `[W-ANY-COMPILE-001]` / `[E-ANY-COMPILE-001]` to each item's authoritative declaration lowerer (`lower_function`, `lower_hir_const_decl`, `lower_trait`, `lower_impl`, `register_type_alias_template`).
- **Coverage:** Every written `Any` / `any` in free `fn`, `extern fn`, `trait` method, `impl` method, module `val`/`var`, `type` / `pub type` alias, and local annotation is diagnosed exactly once per occurrence (`test/01_unit/compiler/30.types/written_any_compile_mode_spec.spl`).
