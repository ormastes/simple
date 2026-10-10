# Module-owned declared global type inference

Authored companion to permanent fix7fccc15fb with the explicit HIR-clean negative assertion below. **UNEXECUTED**: no generated SPipe output, coverage completeness or qualification claim.

Requirement trace: doc/08_tracking/bug/mono_declared_global_array_inference_2026-10-10.md. No accepted feature REQ ID is invented.

| Structural scenario | Actual assertions |
|---|---|
| Mutable nested-array generic argument | Real source lowering has zero errors and one mutable pool; constants dictionary key deliberately differs from declaration.symbol; recorded element type is Str; actual mono call creates one specialization and zero unresolved calls. |
| Equal numeric IDs in distinct modules | Two source-lowered pools assert equal symbol IDs; module-scoped lookup returns Str vs Int64; unregistered module has no type. |
| Lexical precedence | Actual shadowed source lowers clean; explicit env type retains priority over a global fallback; source generic call specializes without unresolved calls. |
| Uninferable empty argument | Real source lowering must have zero errors; no specialization and one unresolved generic call. Unrelated HIR errors cannot count as success. |

Every fallback assert(false) fails on an unexpected shape; none is a placeholder pass. Exact current authored structural spec:

```simple
# UNEXECUTED: real source lowering and monomorphization assertions.
use std.spec.*
use compiler.common.diagnostics.span.{Span}
use compiler.common.config.{Logger}
use compiler.frontend.frontend.{parse_full_frontend}
use compiler.hir.hir_lowering.types.{HirLowering}
use compiler.hir.hir_lowering.items.*
use compiler.hir.hir_types.*
use compiler.hir.hir_definitions.*
use compiler.hir.hir_definitions.{HirConst}
use compiler.mono.monomorphize_integration.{MonomorphizationPass, run_monomorphization}

fn mono_global_symbol(module: HirModule, name: text) -> SymbolId:
    for key in module.constants.keys():
        val declaration: HirConst = module.constants[key]
        if declaration.name == name: return declaration.symbol
    assert(false)
    SymbolId(id: -1)

fn mono_global_array_element(type_: HirType?) -> HirType:
    if val found = type_:
        match found.kind:
            case HirTypeKind.Array(element, _): return element
            case _: assert(false)
    else: assert(false)
    HirType(kind: HirTypeKind.Error, span: Span.empty())

describe "mono uses module-owned declared globals":
    it "infers a nested array generic argument from a mutable global pool":
        val source = "var pool: [text] = []\nfn take<T>(root: [T]) -> bool:\n    true\nfn main() -> bool:\n    take([pool])\n"
        val parsed = parse_full_frontend(source, "testdata/mono_global_nested.spl", "nested", Logger(level: 0))
        var lowering = HirLowering.with_filename("testdata/mono_global_nested.spl")
        var module = lowering.lower_module(parsed)
        expect(lowering.errors.len()).to_equal(0)
        expect(module.constants.len()).to_equal(1)
        val pool = mono_global_symbol(module, "pool")
        val original_key = module.constants.keys()[0]
        val declaration: HirConst = module.constants[original_key]
        expect(declaration.is_mutable).to_be(true)
        var remapped: Dict<SymbolId, HirConst> = {}
        remapped[SymbolId(id: 999999)] = declaration
        module.constants = remapped
        expect(module.constants.keys()[0].id == pool.id).to_be(false)
        var pass_ = MonomorphizationPass.create()
        pass_.collect_declared_globals(module, "nested")
        pass_.current_module = "nested"
        val element = mono_global_array_element(pass_.declared_global_type(pool))
        expect(element.kind == HirTypeKind.Str).to_be(true)
        var modules: Dict<text, HirModule> = {}
        modules["nested"] = module
        val (_, stats) = run_monomorphization(modules)
        expect(stats.call_sites_found).to_equal(1)
        expect(stats.specializations_created).to_equal(1)
        expect(stats.unresolved_generic_calls).to_equal(0)

    it "keeps equal numeric declaration IDs separated by their modules":
        val source_a = "var pool: [text] = []\nfn main() -> i64:\n    0\n"
        val parsed_a = parse_full_frontend(source_a, "testdata/mono_global_a.spl", "a", Logger(level: 0))
        var lowering_a = HirLowering.with_filename("testdata/mono_global_a.spl")
        val a = lowering_a.lower_module(parsed_a)
        val source_b = "var pool: [i64] = []\nfn main() -> i64:\n    0\n"
        val parsed_b = parse_full_frontend(source_b, "testdata/mono_global_b.spl", "b", Logger(level: 0))
        var lowering_b = HirLowering.with_filename("testdata/mono_global_b.spl")
        val b = lowering_b.lower_module(parsed_b)
        expect(lowering_a.errors.len()).to_equal(0)
        expect(lowering_b.errors.len()).to_equal(0)
        val symbol_a = mono_global_symbol(a, "pool")
        val symbol_b = mono_global_symbol(b, "pool")
        expect(symbol_a.id).to_equal(symbol_b.id)
        var pass_ = MonomorphizationPass.create()
        pass_.collect_declared_globals(a, "a")
        pass_.collect_declared_globals(b, "b")
        pass_.current_module = "a"
        expect(mono_global_array_element(pass_.declared_global_type(symbol_a)).kind == HirTypeKind.Str).to_be(true)
        pass_.current_module = "b"
        expect(mono_global_array_element(pass_.declared_global_type(symbol_b)).kind == HirTypeKind.Int(64, true)).to_be(true)
        pass_.current_module = "unregistered"
        expect(pass_.declared_global_type(symbol_a) == nil).to_be(true)

    it "retains lexical type authority before a declared-global fallback":
        val source = "var pool: [text] = []\nfn take<T>(root: [T]) -> bool:\n    true\nfn main() -> bool:\n    val pool: [i64] = []\n    take([pool])\n"
        val parsed = parse_full_frontend(source, "testdata/mono_global_shadow.spl", "shadow", Logger(level: 0))
        var lowering = HirLowering.with_filename("testdata/mono_global_shadow.spl")
        val module = lowering.lower_module(parsed)
        expect(lowering.errors.len()).to_equal(0)
        var pass_ = MonomorphizationPass.create()
        pass_.collect_declared_globals(module, "shadow")
        pass_.current_module = "shadow"
        val pool = mono_global_symbol(module, "pool")
        val integer = HirType(kind: HirTypeKind.Int(64, true), span: Span.empty())
        val lexical = HirType(kind: HirTypeKind.Array(integer, nil), span: Span.empty())
        pass_.env[pool.id] = lexical
        val reference = HirExpr(kind: HirExprKind.NamedVar(pool, "pool"), has_type_: false, type_: nil, span: Span.empty())
        expect(mono_global_array_element(pass_.infer_expr_type(reference)).kind == integer.kind).to_be(true)
        var modules: Dict<text, HirModule> = {}
        modules["shadow"] = module
        val (_, stats) = run_monomorphization(modules)
        expect(stats.specializations_created).to_equal(1)
        expect(stats.unresolved_generic_calls).to_equal(0)

    it "does not invent a type for an empty uninferable generic argument":
        val source = "fn take<T>(root: [T]) -> bool:\n    true\nfn main() -> bool:\n    take([])\n"
        val parsed = parse_full_frontend(source, "testdata/mono_global_unknown.spl", "unknown", Logger(level: 0))
        var lowering = HirLowering.with_filename("testdata/mono_global_unknown.spl")
        val module = lowering.lower_module(parsed)
        expect(lowering.errors.len()).to_equal(0)
        var modules: Dict<text, HirModule> = {}
        modules["unknown"] = module
        val (_, stats) = run_monomorphization(modules)
        expect(stats.specializations_created).to_equal(0)
        expect(stats.unresolved_generic_calls).to_equal(1)
```

Native controls are separate UNEXECUTED observers. mutable_nested expects stdout B,7,17; lexical_shadow expects23; module_identity expects owned-a,29 (one value per line, exit0, empty stderr). Equal numeric provider IDs still need observed identity evidence; runtime stdout alone cannot establish collision coverage. unknown_empty must fail with named take monomorphization diagnostic after all HIR modules pass and emit no object. Detailed source hashes and criteria: test/fixtures/compiler/mono_declared_global_probe/manifest.json.

Maximum three parent-counted cause cycles; no unchanged retry. Required fresh producer Hello and exact source/runtime/tool hashes precede execution. No compiler/core/lib/MCP/LSP verification, full SPipe or lint PASS is claimed.
