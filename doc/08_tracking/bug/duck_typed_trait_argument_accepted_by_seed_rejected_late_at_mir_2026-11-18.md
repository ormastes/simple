# Duck-typed trait argument: the seed accepts it, native lowering rejects it only at MIR

- Canonical id: duck_typed_trait_argument_accepted_by_seed_rejected_late_at_mir_2026-11-18
- Date: 2026-11-18
- Status: open. The instances found are fixed. The missing early check is still open.
- Severity: Phase 3 bootstrap blocker class. Each instance stops the Stage 3 closure.
- Related: `compiler_compilation_context_class_header_trait_no_impl_2026_10_20.md`
  (same MIR error, from a class-header spelling),
  `native_with_trait_impl_no_vtable_duck_trap_2026-07-28.md`.

## Symptom

The integ9 Stage 2 compiler native-builds the Stage 3 closure in go-to-end mode, and the build
fails with:

```
[go-to-end] failed stage=mir module=compiler.hir.hir_lowering.required_field_init_v1:
MIR lowering error: missing native trait implementation:
compiler.hir.generated.hir_visit::HirVisitor for
compiler.hir.hir_lowering.required_field_init_v1::RequiredInitCollectorV1
at src/compiler/20.hir/hir_lowering/required_field_init_v1.spl:570:33
```

## Cause

`class RequiredInitCollectorV1` defines `on_expr`, `on_stmt`, `on_type` and `on_pattern` in its
class body. It never declares `impl HirVisitor for RequiredInitCollectorV1`. It is then passed
to `hir_visit_block(node, visitor: HirVisitor)`.

- **Seed (Rust interpreter):** passes the class through and dispatches `visitor.on_expr(...)`
  by method name, which is duck typing. The specs are green.
- **Self-hosted native lowering:** has to build a `(data, vtable)` trait object.
  `native_trait_conversion.spl:138` looks the vtable up in `native_trait_implementations`,
  which holds only explicit `impl Trait for Type` blocks. A matching method set does not
  count, so the build fails.

The program is the same, and the two lanes give different verdicts. The divergence surfaces only
during a native build, at MIR, after HIR and type checking have passed. No seed spec can turn
red for it.

## Instances (2026-11-18 audit)

Found in the compiler closure and fixed in the same change, using the
`impl HirVisitor for X:` shape of `test/01_unit/compiler/hir/hir_generated_optional_child_spec.spl`:

| Type | Passed at | File |
|---|---|---|
| `RequiredInitCollectorV1` | `hir_visit_block(f.body, collector)` | `src/compiler/20.hir/hir_lowering/required_field_init_v1.spl` |
| `InitCapabilityScanV1` | `hir_visit_expr(arg.value, scan)` | same file (the next failure once the first is fixed) |
| `HirAttrSiteCollectorV1` | `hir_visit_block(f.body, collector)` | `src/compiler/20.hir/hir_lowering/attr_access_sites.spl` |

One more instance is latent, with no call site:

- `HirVisitCounter` in the generated `src/compiler/20.hir/generated/hir_visit.spl`, emitted by
  `src/app/compiler_schema/visitor_gen.spl`. It is documented as a "Concrete HirVisitor" but has
  no impl. Nothing passes it to a visitor function today. To fix it, change the generator and
  regenerate.

### Audit method

1. An awk pass over every `src/**.spl` and `test/**.spl` file outside `vendor/` collected:
   - trait method sets;
   - per-type method sets, from class or struct bodies and plain `impl X:`;
   - explicit `impl T for X` pairs.
2. It flagged every type whose methods cover all of a trait's methods (trait with at least 2
   methods) but which has no `impl T for X`. That produced **597 structural matches across about
   40 traits**.
3. Only 5 of those traits appear as a parameter, field or element type in `src/compiler` or
   `src/app/cli`: `HirVisitor`, `AttrOwnerV1`, `VirtualSourceStoreV1`, `MirPass` and `Module`.
   - `MirPass` is never used as a parameter type.
   - `Module` matched an unrelated AST struct.
   - The `AttrOwnerV1` and `VirtualSourceStoreV1` matches are never converted to the trait. The
     real implementers have explicit impls.
   - Only the `HirVisitor` rows above are real conversions.
4. Most of the remaining structural matches (`ExactSizeIterator`, `Len`, `Dataset`, `CellOwner`
   and others) live outside the compiler closure. They are a risk for any future native build of
   those libraries.

## Missing guard (open)

Nothing rejects this before MIR. Rejecting it in the Rust seed was not done here, for two
reasons:

- the seed interpreter relies on duck typing broadly (the 597 matches above);
- the change would need a cargo rebuild and a seed redeploy.

Proposed follow-up: a self-hosted HIR or type-check error at argument coercion. When an
argument's static type is a concrete class or struct, the expected type is a trait, and no
`impl Trait for Concrete` is in scope, report an error at the call-site span. That gives the
interpreter lane and the native lane the same verdict before MIR. It is the same rule
`native_trait_conversion.spl` already enforces, applied earlier and on every lane.
