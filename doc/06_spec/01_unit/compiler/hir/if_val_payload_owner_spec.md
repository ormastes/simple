# If-val optional payload ownership

Authored companion for `c9cb4ecbbd82713518a3b7cf0cf0a43f0be824cb`. **UNEXECUTED**: exact source assertions, not generated runner output, completeness, or release admission.

Requirement trace: existing bug `doc/08_tracking/bug/if_val_optional_payload_owner_2026-10-10.md`. No accepted REQ ID is present; none is invented.

| Structural scenario | Actual assertions |
|---|---|
| Parser-generated provenance | Ordinary existence-check initializer flag false; implicit/explicit if-val and cloned flag true; explicit check contains original identifier, not a nested check. |
| Declared receiver payload ownership | Exact canonical HirSymbol record ID in Optional method return; ordinary binding source remains Optional; flagged binding selects payload; lowered binding and field preserve record/enum IDs; ordinary declaration remains Optional. |
| Primitive and unknown inputs | Expression remains Optional integer; flagged binding selects integer; nil and nonoptional expressions have no attached optional type. |

Branch `assert(false)` fails when an actual AST/HIR shape differs; it is not a placeholder pass. Supported pure-Simple SSpec execution is still required.

Exact committed structural source:

```simple
# UNEXECUTED: requires a supported pure-Simple SSpec runtime.
use std.spec.*
use compiler.common.diagnostics.span.{Span}
use compiler.common.dependency.visibility.{Visibility}
use compiler.frontend.parser_types_expr.*
use compiler.frontend._FlatAstBridge.convert_nodes.{convert_flat_stmt}
use compiler.core.ast.{expr_ident, expr_exists_check, stmt_val_decl, stmt_if_val_decl}
use compiler.core.ast_clone.{ast_clone_stmt}
use compiler.hir.hir_types.*
use compiler.hir.hir_definitions.*
use compiler.hir.hir_lowering.types.{HirLowering}
use compiler.hir.hir_lowering.statements.*
use compiler.hir.hir_lowering.expressions.*
use compiler.hir.hir_lowering._Expressions.expression_core.*
use compiler.hir.hir_lowering._Expressions.expression_support.*

fn ifval_test_type(kind: HirTypeKind) -> HirType:
    HirType(kind: kind, span: Span.empty())

fn ifval_test_named_id(type_: HirType) -> i64:
    match type_.kind:
        case HirTypeKind.Named(owner, _): return owner.id
        case _: return -1

fn ifval_test_optional_id(type_: HirType) -> i64:
    match type_.kind:
        case HirTypeKind.Optional(payload): return ifval_test_named_id(payload)
        case _: return -1

fn ifval_test_ident(name: text) -> Expr:
    Expr(kind: ExprKind.Ident(name), span: Span.empty())

describe "if-val preserves optional binding provenance":
    it "marks parser-generated bindings without marking an ordinary existence-check initializer":
        val input = expr_ident("input", 0)
        val checked = expr_exists_check(input, 0)
        val ordinary = convert_flat_stmt(stmt_val_decl("ordinary", 0, checked, 0))
        val implicit_flat = stmt_if_val_decl("implicit", input, 0)
        val implicit = convert_flat_stmt(implicit_flat)
        val copied = convert_flat_stmt(ast_clone_stmt(implicit_flat))
        expect(copied.bind_optional_payload).to_be(true)
        val explicit = convert_flat_stmt(stmt_if_val_decl("explicit", checked, 0))
        expect(ordinary.bind_optional_payload).to_be(false)
        expect(implicit.bind_optional_payload).to_be(true)
        expect(explicit.bind_optional_payload).to_be(true)
        match explicit.kind:
            case StmtKind.Val(_, _, value):
                match value.kind:
                    case ExprKind.ExistsCheck(base):
                        match base.kind:
                            case ExprKind.Ident(name): expect(name).to_equal("input")
                            case _: assert(false)
                    case _: assert(false)
            case _: assert(false)

    it "retains canonical HirSymbol payload ownership from a declared receiver method":
        var hir = HirLowering.new()
        val span = Span.empty()
        val record = hir.symbols.define("HirSymbol", SymbolKind.Struct, nil, span, Visibility.Public, false, Some("compiler.hir.hir_types"))
        val table = hir.symbols.define("SymbolTable", SymbolKind.Class, nil, span, Visibility.Public, false, Some("compiler.hir.hir_types"))
        val kind_owner = hir.symbols.define("SymbolKind", SymbolKind.Enum, nil, span, Visibility.Public, false, Some("compiler.hir.hir_types"))
        val record_type = ifval_test_type(HirTypeKind.Named(record, []))
        val optional = ifval_test_type(HirTypeKind.Optional(record_type))
        val integer = ifval_test_type(HirTypeKind.Int(64, true))
        val signature = ifval_test_type(HirTypeKind.Function([integer], optional, []))
        hir.symbols.define("compiler.hir.hir_types.SymbolTable::get_symbol_raw", SymbolKind.Method, signature, span, Visibility.Public, false, Some("compiler.hir.hir_types"))
        hir.symbols.define("table", SymbolKind.Parameter, ifval_test_type(HirTypeKind.Named(table, [])), span, Visibility.Private, false, nil)
        hir.struct_field_types_by_name["compiler.hir.hir_types.HirSymbol"] = {"kind": ifval_test_type(HirTypeKind.Named(kind_owner, []))}
        val arg = CallArg(has_name: false, name: "", value: Expr(kind: ExprKind.IntLit(7), span: span), span: span)
        val call = Expr(kind: ExprKind.MethodCall(ifval_test_ident("table"), "get_symbol_raw", [arg]), span: span)
        val checked = Expr(kind: ExprKind.ExistsCheck(call), span: span)
        val lowered = hir.lower_hir_expr(checked)
        expect(lowered.has_type_).to_be(true)
        if val lowered_type = lowered.type_:
            expect(ifval_test_optional_id(lowered_type)).to_equal(record.id)
        else: assert(false)
        expect(ifval_test_optional_id(hir.binding_source_type(lowered))).to_equal(record.id)
        expect(ifval_test_named_id(hir.binding_source_type(lowered, true))).to_equal(record.id)
        val bound = hir.lower_hir_stmt(Stmt(kind: StmtKind.Val("symbol", nil, checked), span: span, bind_optional_payload: true))
        match bound.kind:
            case HirStmtKind.Let(symbol, _, _):
                expect(hir.symbols.get_symbol_named_type_raw(symbol.id)).to_equal(record.id)
                expect(ifval_test_named_id(hir.field_type_for_base_raw(symbol.id, "kind"))).to_equal(kind_owner.id)
            case _: assert(false)
        val ordinary = hir.lower_hir_stmt(Stmt(kind: StmtKind.Val("ordinary", nil, checked), span: span))
        match ordinary.kind:
            case HirStmtKind.Let(symbol, _, _):
                if val declared = hir.symbols.get_symbol_type_raw(symbol.id):
                    expect(ifval_test_optional_id(declared)).to_equal(record.id)
                else: assert(false)
            case _: assert(false)

    it "keeps optional primitive expressions optional and fails closed for unknown or nonoptional inputs":
        var hir = HirLowering.new()
        val span = Span.empty()
        val integer = ifval_test_type(HirTypeKind.Int(64, true))
        hir.symbols.define("maybe", SymbolKind.Parameter, ifval_test_type(HirTypeKind.Optional(integer)), span, Visibility.Private, false, nil)
        val checked = hir.lower_hir_expr(Expr(kind: ExprKind.ExistsCheck(ifval_test_ident("maybe")), span: span))
        if val checked_type = checked.type_:
            match checked_type.kind:
                case HirTypeKind.Optional(inner): expect(inner.kind == integer.kind).to_be(true)
                case _: assert(false)
        else: assert(false)
        expect(hir.binding_source_type(checked, true).kind == integer.kind).to_be(true)
        val absent = hir.lower_hir_expr(Expr(kind: ExprKind.ExistsCheck(Expr(kind: ExprKind.NilLit, span: span)), span: span))
        expect(absent.has_type_).to_be(false)
        hir.symbols.define("plain", SymbolKind.Parameter, integer, span, Visibility.Private, false, nil)
        val plain = hir.lower_hir_expr(Expr(kind: ExprKind.ExistsCheck(ifval_test_ident("plain")), span: span))
        expect(plain.has_type_).to_be(false)
```

Native primitive observer

`test/fixtures/compiler/if_val_payload_owner_probe/main.spl`: expected exit 0, empty stderr, exact stdout:

```text
7
0
2
7
2
7
1
```

Present/absent optional primitives, explicit existence check without double evaluation, while-val reevaluation, and ordinary optional declaration consumed by later if-val are observed. Stdout alone cannot prove the ordinary declaration's Optional type; structural assertions own that contract. Native expectations remain **UNEXECUTED**.

Exact committed native source:

```simple
class Probe:
    calls: i64

    me next() -> i64?:
        self.calls = self.calls + 1
        if self.calls == 1:
            return Some(7)
        return nil

fn main() -> i64:
    var probe = Probe(calls: 0)
    if val value = probe.next():
        print value
    else:
        return 1
    if val absent = probe.next().?:
        return 2
    else:
        print 0
    print probe.calls
    var looping = Probe(calls: 0)
    while val item = looping.next():
        print item
    print looping.calls
    var ordinary_probe = Probe(calls: 0)
    val ordinary = ordinary_probe.next().?
    if val preserved = ordinary:
        print preserved
    else:
        return 3
    print ordinary_probe.calls
    return 0
```

The real HirSymbol? receiver gate remains hir_symbol_table_methods.spl / lookup_exact_type via real_hir_owner_probe/object_record: actual dependency HIR acceptance and retained object body under the fresh producer are required. Primitive success cannot replace it. No SPipe/core/lib/MCP/LSP PASS or qualification is claimed.
