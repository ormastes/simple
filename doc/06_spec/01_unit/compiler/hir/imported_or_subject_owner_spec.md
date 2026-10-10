# Imported enum OR subject ownership

Status: **UNEXECUTED**. This authored companion records the exact executable scenarios and assertions; it is not generated execution evidence or a verify PASS.

Source: `test/01_unit/compiler/hir/imported_or_subject_owner_spec.spl` at `707f68059`.

Four examples check imported bare alternatives without HIR errors, constructed nested OR with exact alias owner IDs and wrapper typing, qualified unit alternatives without HIR errors, and the named diagnostic for genuinely different payload binding sets. The constructed nested AST uses parsed provider declarations and real alias registration. HIR error absence does not establish native dispatch correctness.

Separate native controls using producer SHA `6fd459d383aadc02c1854c99fb1df67e7e891b773d3353021c84ec91dbcb3a8c` remain failing: bare, nested and qualified produced `1/1/1` instead of `1/1/0`; payload transport and mismatch rejection are independently incomplete. Authoritative receipts are under `/mnt/c/Temp/simple-hir-or-9f1c3225-validation-20261010/validation/`. No native PASS is claimed here.

## Exact executable spec

The complete source is reproduced to retain helper setup, environment restoration, real assertions and fail-fast branches.

```simple
# Regression: imported bare enum units must retain the match subject owner
# through OR alternatives before strict binding-set unification.
# Status: UNEXECUTED; native baseline and independent failures are recorded in
# test/fixtures/compiler/hir_or_owner_probe/README.md.
use std.spec.*
use compiler.hir.hir_lowering.types.{HirLowering, hirlowering_for_module}
use compiler.hir.hir_lowering.items.*
use compiler.hir.hir_lowering.module_surface.{ModuleSurfacesByName, module_surfaces_from_modules}
use compiler.frontend.frontend.{parse_full_frontend}
use compiler.frontend.parser_types.{Module}
use compiler.common.driver_core_types.{SourceFile}
use compiler.common.config.{Logger}

use compiler.common.dependency.visibility.Visibility
use compiler.common.diagnostics.span.Span
use compiler.frontend.parser_types_expr.*
use compiler.hir.hir_types.*
use compiler.hir.hir_definitions.*
use compiler.hir.hir_lowering._Expressions.expression_components.*

fn imported_or_leaf_identity(pattern: HirPattern) -> text:
    match pattern.kind:
        case HirPatternKind.Enum(type_, name, _):
            match type_.kind:
                case HirTypeKind.Named(owner, _): "{owner.id}:{name}"
                case _: "wrong-owner-kind"
        case HirPatternKind.Binding(_, _): "binding"
        case _: "wrong-pattern-kind"

fn lower_imported_or_owner(pattern: text, body: text) -> HirLowering:
    val logger = Logger(level: 0)
    val provider_source = "pub enum E:\n    A\n    B\n    P(i64)\n    Q(i64)\n"
    val provider = parse_full_frontend(provider_source, "owner.provider", "owner.provider", logger)
    val consumer_source = "use owner.provider.\{E\}\nfn pick(value: E) -> i64:\n    match value:\n        case {pattern}:\n            {body}\n        case _:\n            0\n"
    val consumer = parse_full_frontend(consumer_source, "owner.consumer", "owner.consumer", logger)
    var modules: Dict<text, Module> = {}
    modules["owner.provider"] = provider
    val sources = [SourceFile(path: "owner/provider.spl", content: provider_source, module_name: "owner.provider")]
    val surfaces = match module_surfaces_from_modules(modules, sources):
        case Ok(value): value
        case Err(error):
            assert(false)
            ModuleSurfacesByName.empty()
    var lowering = hirlowering_for_module("owner.consumer", surfaces)
    lowering.lower_module(consumer)
    lowering

describe "imported enum OR subject ownership":
    it "recognizes bare unit alternatives from their subject owner":
        step("Lower imported A and B as variants, not mismatched bindings")
        val lowering = lower_imported_or_owner("A | B", "1")
        expect(lowering.errors.len()).to_equal(0)

    it "preserves exact alias identity and enum kinds through nested OR":
        step("Lower a nested AST OR using real provider declarations and alias registration")
        val parsed = parse_full_frontend("pub enum Remote:\n    A\n    B\n", "remote", "remote", Logger(level: 0))
        var lowering = HirLowering.with_filename("consumer")
        val span = Span.empty()
        val alias = lowering.symbols.define("LocalAlias", SymbolKind.Enum, nil, span, Visibility.Public, false, nil)
        lowering.register_enum_unit_patterns(parsed.enums["Remote"], "LocalAlias")
        val subject = HirType(kind: HirTypeKind.Named(alias, []), span: span)
        val a = Pattern(kind: PatternKind.Binding("A", false), span: span)
        val b = Pattern(kind: PatternKind.Binding("B", false), span: span)
        val inner = Pattern(kind: PatternKind.Or([a, b]), span: span)
        val outer = Pattern(kind: PatternKind.Or([inner, b]), span: span)
        val lowered = lowering.lower_match_pattern(outer, Some(subject))
        expect(lowering.errors.len()).to_equal(0)
        expect(lowered.has_type_).to_be(false)
        match lowered.kind:
            case HirPatternKind.Or(alternatives):
                expect(alternatives.len()).to_equal(2)
                expect(imported_or_leaf_identity(alternatives[1])).to_equal("{alias.id}:B")
                expect(alternatives[1].has_type_).to_be(true)
                match alternatives[0].kind:
                    case HirPatternKind.Or(nested):
                        expect(nested.len()).to_equal(2)
                        expect(imported_or_leaf_identity(nested[0])).to_equal("{alias.id}:A")
                        expect(imported_or_leaf_identity(nested[1])).to_equal("{alias.id}:B")
                    case _: assert(false)
            case _: assert(false)

    it "keeps qualified unit alternatives valid":
        step("Preserve explicit enum owner resolution")
        val lowering = lower_imported_or_owner("E.A | E.B", "1")
        expect(lowering.errors.len()).to_equal(0)

    it "rejects genuinely different payload binding sets":
        step("Require the named binding-set diagnostic for x versus y")
        val lowering = lower_imported_or_owner("E.P(x) | E.Q(y)", "1")
        var mismatch = false
        for diagnostic in lowering.diagnostic_messages:
            if diagnostic.contains("or-pattern alternatives must bind the same variables"):
                mismatch = true
        expect(mismatch).to_be(true)
```
