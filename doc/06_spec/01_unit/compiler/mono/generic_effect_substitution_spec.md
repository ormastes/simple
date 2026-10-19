# Substitute type-bearing effects in generic HIR

Draft executable: `test/01_unit/compiler/mono/generic_effect_substitution_spec.spl`.
Trace: existing `REQ-SSPEC-COMPILER`; original hardening design section 9.4,
M2 type substitution and M3 complete HIR substitution.

**AUTHORED / UNRUN: eight authored scenarios, zero executed.** A production helper now
substitutes type-bearing effects in function types, template canonicalization
and function specialization. This source change is unqualified. No observed RED, compilation,
generated-document receipt, native effect execution or generic effect-argument
propagation is claimed. This manual is hand-maintained; capture is off.

1. **Prepare the production input.** Construct typed function signatures containing
   `Throws<T>`, or parse/lower a generic function and attach a declaration-owned
   thrown type. Include a concrete effect and an unbound parameter as controls.
2. **Exercise the production boundary.** Call existing `substitute_type`,
   `canonicalize_template`, `specialize_function_with_types` or
   `substitute_function` directly.
3. **Inspect the observed result.** Require substituted thrown types, unchanged
   ordering and spans, concrete specialization identity, and preserved template
   metadata on the canonicalized declaration.
4. **Reject the negative control.** Distinguish unchanged generic output from the
   required concrete output; an unbound parameter must not become an invented
   concrete thrown type. The separate failing-harness check remains unexecuted.

| Exact executable scenario | Expected observation |
|---|---|
| should substitute a nested thrown type inside a function type | Nested thrown Optional<T> becomes Optional<i64>; the input remains unchanged. |
| should preserve effect order and source spans while substituting throws | IO, Throws and Custom retain their order and source spans. |
| should retain an unbound thrown parameter instead of inventing a concrete type | An unmapped Outer stays symbolic instead of becoming an invented integer payload. |
| should canonicalize declaration-owned thrown parameters before specialization | A declaration-owned thrown parameter canonicalizes and specializes to marker$i64. |
| should preserve concrete effect payloads when specializing a function body | Concrete thrown types and Async are preserved; absent effect arrays remain absent. |
| should retain every non-type effect and distinguish empty from absent effects | Pure, IO, Async, Mutates, Allocates and Custom remain ordered and unchanged; a custom name equal to a type parameter stays literal. Empty and absent effect lists retain their respective representations. |
| should recurse into thrown function effects and remain idempotent | Types inside a thrown function's own Throws effect become concrete recursively; repeating substitution has no further effect and the original remains generic. |
| should leave a different owner symbol unbound during template specialization | The declaration-owned symbol specializes, while a different nominal symbol is retained unchanged. |

These are HIR substitution API scenarios. Const/effect/capability parameter
transport through parser, request keys, archive records and native emission is
a separate original-plan obligation.

The 2026-10-16 continuation reuses the preserved lane-04 leaf implementation
against `bcb8876fbe3736780ff1abae2c336030bb8b66ea`. It retains the five existing
scenarios and adds three boundary cases; the original unbound and canonical
owner scenarios also gain negative and immutability checks. The shared native
API dependency closure is currently blocked by separate MIR source errors,
so no unchanged build, SSpec run or docgen command was launched for this slice.

<details>
<summary>Current authored executable and helpers — UNRUN, not generated evidence</summary>

```simple
# @req REQ-SSPEC-COMPILER
# Original scope: simple_hardening_plan_2026-08-21.md section 9.4, M2/M3.
# codex-system-test; production HIR API evidence, execution UNRUN.
# Capture off. This does not prove effect-parameter request propagation.
use std.spec
use std.spec.step
use compiler.common.config.Logger
use compiler.common.diagnostics.span.Span
use compiler.frontend.frontend.parse_full_frontend
use compiler.hir.hir_lowering.types.HirLowering
use compiler.hir.hir_lowering.items.*
use compiler.hir.hir_types.{HirType, HirTypeKind, Effect, EffectKind, SymbolId}
use compiler.hir.hir_definitions.{HirFunction, HirTypeParam}
use compiler.monomorphize.type_subst.{TypeSubstitution, substitute_type, substitute_function, canonicalize_template, typesubstitution_empty}
use compiler.monomorphize.engine.specialize_function_with_types

# @inline
fn robust_04_generics_setup_effect_type(kind: HirTypeKind) -> HirType:
    HirType(kind: kind, span: Span.empty())

# @inline
fn robust_04_generics_setup_throwing_template() -> HirFunction:
    val parsed = parse_full_frontend("fn marker<T>() -> i64:\n    19\n", "effects.spl", "effects", Logger(level: 0))
    var lowering = HirLowering.with_filename("effects.spl")
    val module = lowering.lower_module(parsed)
    expect(lowering.errors.len()).to_equal(0)
    expect(module.functions.len()).to_equal(1)
    val keys = module.functions.keys()
    var function: HirFunction = module.functions[keys[0]]
    val parameter: HirTypeParam = function.type_params[0]
    val declared = robust_04_generics_setup_effect_type(HirTypeKind.Named(parameter.symbol, []))
    function.effects = [Effect(kind: EffectKind.Throws(declared), span: Span.new(1, 3, 7, 9))]
    function

describe "generic substitution includes type-bearing effects":
    it "should substitute a nested thrown type inside a function type":
        step("Prepare the production input")
        val parameter = robust_04_generics_setup_effect_type(HirTypeKind.TypeParam("T", []))
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        val nested = robust_04_generics_setup_effect_type(HirTypeKind.Optional(parameter))
        val original = robust_04_generics_setup_effect_type(HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(nested), span: Span.empty())]))
        val substitution = TypeSubstitution(mapping: {"T": integer}, by_symbol: {})
        step("Exercise the production boundary")
        val result = substitute_type(original, substitution)
        step("Inspect the observed result")
        val expected_error = robust_04_generics_setup_effect_type(HirTypeKind.Optional(integer))
        expect(result.kind == HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(expected_error), span: Span.empty())])).to_be(true)
        step("Reject the negative control")
        expect(result.kind == original.kind).to_be(false)
        expect(original.kind == HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(nested), span: Span.empty())])).to_be(true)

    it "should preserve effect order and source spans while substituting throws":
        step("Prepare the production input")
        val parameter = robust_04_generics_setup_effect_type(HirTypeKind.TypeParam("T", []))
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        val location = Span.new(1, 3, 7, 9)
        val effects = [Effect(kind: EffectKind.IO, span: location), Effect(kind: EffectKind.Throws(parameter), span: location), Effect(kind: EffectKind.Custom("audit"), span: location)]
        val original = robust_04_generics_setup_effect_type(HirTypeKind.Function([parameter], parameter, effects))
        step("Exercise the production boundary")
        val result = substitute_type(original, TypeSubstitution(mapping: {"T": integer}, by_symbol: {}))
        step("Inspect the observed result")
        val expected = [effects[0], Effect(kind: EffectKind.Throws(integer), span: location), effects[2]]
        expect(result.kind == HirTypeKind.Function([integer], integer, expected)).to_be(true)
        expect(result.span).to_equal(original.span)

    it "should retain an unbound thrown parameter instead of inventing a concrete type":
        step("Prepare the production input")
        val parameter = robust_04_generics_setup_effect_type(HirTypeKind.TypeParam("Outer", []))
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        val original = robust_04_generics_setup_effect_type(HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(parameter), span: Span.empty())]))
        step("Exercise the production boundary")
        val substitution = TypeSubstitution(mapping: {"T": integer}, by_symbol: {})
        val result = substitute_type(original, substitution)
        step("Inspect the observed result")
        expect(result.kind).to_equal(original.kind)
        expect(substitute_type(original, typesubstitution_empty()).kind).to_equal(original.kind)
        step("Reject the negative control")
        val invented = HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(integer), span: Span.empty())])
        expect(result.kind == invented).to_be(false)

    it "should canonicalize declaration-owned thrown parameters before specialization":
        step("Prepare the production input")
        val original = robust_04_generics_setup_throwing_template()
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        val parameter: HirTypeParam = original.type_params[0]
        val declared = robust_04_generics_setup_effect_type(HirTypeKind.Named(parameter.symbol, []))
        step("Exercise the production boundary")
        val canonical = canonicalize_template(original)
        val result = specialize_function_with_types(canonical, [integer])
        step("Inspect the observed result")
        match canonical.effects[0].kind:
            case EffectKind.Throws(payload):
                val error_type: HirType = payload
                expect(error_type.kind == HirTypeKind.TypeParam("T", [])).to_be(true)
            case _:
                assert(false)
        expect(canonical.type_params.len()).to_equal(1)
        expect(result.effects[0].kind == EffectKind.Throws(integer)).to_be(true)
        expect(result.effects[0].span.line).to_equal(7)
        expect(result.effects[0].span.col).to_equal(9)
        expect(result.type_params.len()).to_equal(0)
        expect(result.is_generic_template).to_be(false)
        expect(result.name).to_equal("marker$i64")
        step("Reject mutation of the original declaration")
        expect(original.effects[0].kind == EffectKind.Throws(declared)).to_be(true)
        expect(original.type_params.len()).to_equal(1)
        expect(original.name).to_equal("marker")
        expect(result.effects == original.effects).to_be(false)

    it "should preserve concrete effect payloads when specializing a function body":
        step("Prepare the production input")
        var original = robust_04_generics_setup_throwing_template()
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        original.effects = [Effect(kind: EffectKind.Throws(integer), span: Span.empty()), Effect(kind: EffectKind.Async, span: Span.empty())]
        step("Exercise the production boundary")
        val result = substitute_function(original, TypeSubstitution(mapping: {"T": integer}, by_symbol: {}), "marker$concrete")
        step("Inspect the observed result")
        expect(result.effects).to_equal(original.effects)
        expect(result.return_type.kind).to_equal(original.return_type.kind)
        expect(result.name).to_equal("marker$concrete")
        var absent = original
        absent.effects = nil
        val absent_result = substitute_function(absent, typesubstitution_empty(), "marker$absent")
        expect(absent_result.effects == nil).to_be(true)

    it "should retain every non-type effect and distinguish empty from absent effects":
        step("Prepare the production input")
        val parameter = robust_04_generics_setup_effect_type(HirTypeKind.TypeParam("T", []))
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        val location = Span.new(4, 11, 3, 5)
        val effects = [Effect(kind: EffectKind.Pure, span: location), Effect(kind: EffectKind.IO, span: location), Effect(kind: EffectKind.Async, span: location), Effect(kind: EffectKind.Mutates, span: location), Effect(kind: EffectKind.Allocates, span: location), Effect(kind: EffectKind.Custom("T"), span: location)]
        val original = robust_04_generics_setup_effect_type(HirTypeKind.Function([parameter], parameter, effects))
        val substitution = TypeSubstitution(mapping: {"T": integer}, by_symbol: {})
        step("Exercise the production boundary")
        val result = substitute_type(original, substitution)
        val empty = substitute_type(robust_04_generics_setup_effect_type(HirTypeKind.Function([], integer, [])), substitution)
        val absent = substitute_type(robust_04_generics_setup_effect_type(HirTypeKind.Function([], integer, nil)), substitution)
        step("Inspect the observed result")
        expect(result.kind == HirTypeKind.Function([integer], integer, effects)).to_be(true)
        expect(empty.kind == HirTypeKind.Function([], integer, [])).to_be(true)
        expect(absent.kind == HirTypeKind.Function([], integer, nil)).to_be(true)
        match empty.kind:
            case HirTypeKind.Function(_, _, empty_effects):
                val observed: [Effect] = empty_effects
                expect(observed == nil).to_be(false)
                expect(observed.len()).to_equal(0)
            case _:
                assert(false)
        match absent.kind:
            case HirTypeKind.Function(_, _, absent_effects):
                expect(absent_effects == nil).to_be(true)
            case _:
                assert(false)
        step("Reject treating a custom effect name as a type parameter")
        val renamed = [effects[0], effects[1], effects[2], effects[3], effects[4], Effect(kind: EffectKind.Custom("i64"), span: location)]
        expect(result.kind == HirTypeKind.Function([integer], integer, renamed)).to_be(false)
        expect(original.kind == HirTypeKind.Function([parameter], parameter, effects)).to_be(true)

    it "should recurse into thrown function effects and remain idempotent":
        step("Prepare the production input")
        val parameter = robust_04_generics_setup_effect_type(HirTypeKind.TypeParam("T", []))
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        val location = Span.new(2, 6, 4, 8)
        val nested = robust_04_generics_setup_effect_type(HirTypeKind.Function([parameter], parameter, [Effect(kind: EffectKind.Throws(parameter), span: location)]))
        val original = robust_04_generics_setup_effect_type(HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(nested), span: location)]))
        val substitution = TypeSubstitution(mapping: {"T": integer}, by_symbol: {})
        step("Exercise the production boundary")
        val result = substitute_type(original, substitution)
        val repeated = substitute_type(result, substitution)
        step("Inspect the observed result")
        val expected_nested = robust_04_generics_setup_effect_type(HirTypeKind.Function([integer], integer, [Effect(kind: EffectKind.Throws(integer), span: location)]))
        expect(result.kind == HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(expected_nested), span: location)])).to_be(true)
        expect(repeated).to_equal(result)
        step("Reject a shallow effect rewrite")
        expect(result.kind == original.kind).to_be(false)
        expect(original.kind == HirTypeKind.Function([], integer, [Effect(kind: EffectKind.Throws(nested), span: location)])).to_be(true)

    it "should leave a different owner symbol unbound during template specialization":
        step("Prepare the production input")
        var original = robust_04_generics_setup_throwing_template()
        val parameter: HirTypeParam = original.type_params[0]
        val unrelated = robust_04_generics_setup_effect_type(HirTypeKind.Named(SymbolId.new(parameter.symbol.id + 1000000), []))
        val integer = robust_04_generics_setup_effect_type(HirTypeKind.Int(64, true))
        val owned_effect = original.effects[0]
        original.effects = [owned_effect, Effect(kind: EffectKind.Throws(unrelated), span: Span.empty())]
        step("Exercise the production boundary")
        val canonical = canonicalize_template(original)
        val result = specialize_function_with_types(canonical, [integer])
        step("Inspect the observed result")
        expect(result.effects[0].kind == EffectKind.Throws(integer)).to_be(true)
        expect(result.effects[1].kind == EffectKind.Throws(unrelated)).to_be(true)
        expect(canonical.effects[1]).to_equal(original.effects[1])
        step("Reject substitution by unrelated nominal identity")
        expect(result.effects[1].kind == EffectKind.Throws(integer)).to_be(false)
        expect(original.effects[0]).to_equal(owned_effect)
```

</details>
