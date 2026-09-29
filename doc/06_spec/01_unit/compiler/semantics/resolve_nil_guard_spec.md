# Resolve Nil Guard Specification

> Tests covering MethodResolver nil guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resolve Nil Guard Specification

## Scenarios

### MethodResolver nil guards

#### keeps module resolution methods owned by MethodResolver

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps module resolution methods owned by MethodResolver
   - Expected: owner >= 0 is true
   - Expected: method > owner is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps module resolution methods owned by MethodResolver")
val source = file_read("src/compiler/35.semantics/resolve.spl")
val owner = source.find("impl MethodResolver:")
val method = source.find("    me resolve_module(module: HirModule) -> HirModule:")

expect(owner >= 0).to_equal(true)
expect(method > owner).to_equal(true)
```

</details>

#### preserves named call arguments through resolution

- preserves named call arguments through resolution
   - Expected: resolved.len() equals `1`
   - Expected: resolved[0].name equals `value`
   - Expected: text_value equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves named call arguments through resolution")
val text_type = HirType(kind: HirTypeKind.Str, span: Span.empty())
val value = HirExpr(
    kind: HirExprKind.StringLit("simple", nil),
    has_type_: true,
    type_: text_type,
    span: Span.empty()
)
val arg = HirCallArg(
    has_name: true,
    name: "value",
    value: value,
    span: Span.empty()
)
var resolver = MethodResolver.new(SymbolTable.new())

val resolved = resolver.resolve_call_args([arg])

expect(resolved.len()).to_equal(1)
expect(resolved[0].has_name).to_be(true)
expect(resolved[0].name).to_equal("value")
match resolved[0].value.kind:
    case HirExprKind.StringLit(text_value, _):
        expect(text_value).to_equal("simple")
    case _:
        expect(false).to_be(true)
```

</details>

#### keeps UFCS working when current_fn_sym is Some(nil)

- keeps UFCS working when current_fn_sym is Some(nil)
   - Expected: result != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps UFCS working when current_fn_sym is Some(nil)")
var symbols = SymbolTable.new()
val i64_type = HirType.named("i64")
val ping_type = HirType(
    # The second parameter models a trailing default. UFCS resolution
    # sees only this callable shape and must leave missing args to the
    # normal default-argument path.
    kind: HirTypeKind.Function([i64_type, i64_type], i64_type, []),
    span: Span.empty()
)
symbols.define(
    "ping",
    SymbolKind.Function,
    Some(ping_type),
    Span.empty(),
    Visibility.Public,
    false,
    nil
)

var resolver = MethodResolver.new(symbols)
resolver.current_fn_sym = Some(nil)

val args: [HirCallArg] = []
val result = resolver.try_ufcs(i64_type, "ping", args)

expect(result != nil).to_equal(true)
```

</details>

#### rejects a same-named UFCS function with the wrong arity

- rejects a same-named UFCS function with the wrong arity
   - Expected: resolver.try_ufcs(array_type, "join", args) != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a same-named UFCS function with the wrong arity")
var symbols = SymbolTable.new()
val text_type = HirType(kind: HirTypeKind.Str, span: Span.empty())
val array_type = HirType(kind: HirTypeKind.Array(text_type, nil), span: Span.empty())
val join_type = HirType(
    kind: HirTypeKind.Function([array_type], text_type, []),
    span: Span.empty()
)
symbols.define(
    "join",
    SymbolKind.Function,
    Some(join_type),
    Span.empty(),
    Visibility.Public,
    false,
    nil
)

val separator = HirExpr(
    kind: HirExprKind.StringLit("/", nil),
    has_type_: true,
    type_: text_type,
    span: Span.empty()
)
val args = [HirCallArg(has_name: false, name: "", value: separator, span: Span.empty())]
var resolver = MethodResolver.new(symbols)

expect(resolver.try_ufcs(array_type, "join", args) != nil).to_equal(false)
```

</details>

#### keeps array join owned by the collection builtin

- keeps array join owned by the collection builtin
   - Expected: resolver.try_ufcs(array_type, "join", args) != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps array join owned by the collection builtin")
var symbols = SymbolTable.new()
val text_type = HirType(kind: HirTypeKind.Str, span: Span.empty())
val array_type = HirType(kind: HirTypeKind.Array(text_type, nil), span: Span.empty())
val colliding_join_type = HirType(
    kind: HirTypeKind.Function([array_type, text_type], text_type, []),
    span: Span.empty()
)
symbols.define(
    "join",
    SymbolKind.Function,
    Some(colliding_join_type),
    Span.empty(),
    Visibility.Public,
    false,
    nil
)

val separator = HirExpr(
    kind: HirExprKind.StringLit("", nil),
    has_type_: true,
    type_: text_type,
    span: Span.empty()
)
val args = [HirCallArg(has_name: false, name: "", value: separator, span: Span.empty())]
var resolver = MethodResolver.new(symbols)

expect(resolver.try_ufcs(array_type, "join", args) != nil).to_equal(false)
```

</details>

#### keeps UFCS optional bindings visible to HIR lowering

- keeps UFCS optional bindings visible to HIR lowering
   - Expected: source does not contain `if val resolved_lookup_id = func_sym_id`
   - Expected: source does not contain `if val type_id = type_sym_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps UFCS optional bindings visible to HIR lowering")
val source = file_read("src/compiler/35.semantics/resolve_strategies.spl")

expect(source.contains("if val resolved_lookup_id = func_sym_id")).to_equal(false)
expect(source).to_contain("val resolved_lookup_id = func_sym_id")
expect(source.contains("if val type_id = type_sym_id")).to_equal(false)
expect(source).to_contain("val type_id = type_sym_id")
```

</details>

#### selects the receiver owner when unrelated types share a method name

- selects the receiver owner when unrelated types share a method name
   - Expected: lowering.errors.len() equals `0`
   - Expected: resolved != nil is true
   - Expected: owner.id equals `codegen_owner.id`
   - Expected: method.id equals `codegen_cleanup.id`
   - Expected: false is true
   - Expected: false is true
   - Expected: resolve_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects the receiver owner when unrelated types share a method name")
val source = "struct CodegenCompiledModule:\n    handle: i64\n" +
    "impl CodegenCompiledModule:\n    fn cleanup(self) -> i64: 17\n    static fn code() -> i64: 18\n" +
    "struct TieredJitManager:\n    handle: i64\n" +
    "impl TieredJitManager:\n    fn cleanup(self) -> i64: 99\n    static fn code() -> i64: 100\n" +
    "fn call_codegen(value: CodegenCompiledModule) -> i64: value.cleanup()\n" +
    "fn call_jit(value: TieredJitManager) -> i64: value.cleanup()\n" +
    "fn static_codegen() -> i64: CodegenCompiledModule.code()\n" +
    "fn static_jit() -> i64: TieredJitManager.code()\n" +
    "trait DefaultCleanup:\n    fn cleanup(self) -> i64: 55\n" +
    "struct DefaultCleanupA:\n    handle: i64\n" +
    "struct DefaultCleanupB:\n    handle: i64\n" +
    "impl DefaultCleanup for DefaultCleanupA:\n    pass_dn\n" +
    "impl DefaultCleanup for DefaultCleanupB:\n    pass_dn\n" +
    "fn call_default_a(value: DefaultCleanupA) -> i64: value.cleanup()\n" +
    "fn call_default_b(value: DefaultCleanupB) -> i64: value.cleanup()\n"
val parsed = parse_full_frontend(source, "method_owner", "method_owner", Logger(level: 0))
var lowering = HirLowering.with_filename("method_owner.spl")
val hir = lowering.lower_module(parsed)
expect(lowering.errors.len()).to_equal(0)
val codegen_owner = hir.symbols.lookup("CodegenCompiledModule").unwrap()
val jit_owner = hir.symbols.lookup("TieredJitManager").unwrap()
val codegen_cleanup = hir.symbols.lookup("method_owner.CodegenCompiledModule::cleanup").unwrap()
val jit_cleanup = hir.symbols.lookup("method_owner.TieredJitManager::cleanup").unwrap()
val codegen_type = HirType(
    kind: HirTypeKind.Named(codegen_owner, []),
    span: Span.empty()
)
var resolver = MethodResolver.new(hir.symbols)

val resolved = resolver.try_instance_method(codegen_type, "cleanup")
expect(resolved != nil).to_equal(true)
if resolved.?:
    match resolved.unwrap():
        case MethodResolution.InstanceMethod(owner, method):
            expect(owner.id).to_equal(codegen_owner.id)
            expect(method.id).to_equal(codegen_cleanup.id)
            assert_not_equal(method.id, jit_cleanup.id)
            assert_not_equal(owner.id, jit_owner.id)
        case _:
            expect(false).to_equal(true)
else:
    expect(false).to_equal(true)

val (resolved_hir, resolve_errors) = resolve_methods(hir)
expect(resolve_errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(resolved_hir.symbols)
val mir = mir_lowering.lower_module(resolved_hir)
var mir_names: [text] = []
for function in mir.functions.values():
    mir_names = mir_names.push(function.name)
val call_names = mir_call_names(mir)
expect(mir_names).to_contain("method_owner.CodegenCompiledModule.cleanup")
expect(mir_names).to_contain("method_owner.TieredJitManager.cleanup")
expect(mir_names).to_contain("method_owner.DefaultCleanupA.cleanup")
expect(mir_names).to_contain("method_owner.DefaultCleanupB.cleanup")
expect(call_names).to_contain("method_owner.CodegenCompiledModule.cleanup")
expect(call_names).to_contain("method_owner.TieredJitManager.cleanup")
expect(call_names).to_contain("method_owner.DefaultCleanupA.cleanup")
expect(call_names).to_contain("method_owner.DefaultCleanupB.cleanup")
expect(call_names).to_contain("method_owner.CodegenCompiledModule.code")
expect(call_names).to_contain("method_owner.TieredJitManager.code")
```

</details>

#### predeclares local instance and static text method signatures

- predeclares local instance and static text method signatures
   - Expected: lowering.errors.len() equals `0`
   - Expected: symbol_is_text_callable(hir.symbols, instance_id, 1, owner.id) is true
   - Expected: symbol_is_text_callable(hir.symbols, static_id, 0, -1) is true
   - Expected: symbol_is_text_callable(hir.symbols, inherited_id, 1, owner.id) is true
   - Expected: resolve_errors.len() equals `0`
   - Expected: mir_call_has_text_return(mir, "method_text.Widget.describe") is true
   - Expected: mir_call_has_text_return(mir, "method_text.Widget.category") is true
   - Expected: mir_call_has_text_return(mir, "method_text.Widget.inherited") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("predeclares local instance and static text method signatures")
val source = "trait DefaultDescribe:\n    fn inherited(self) -> text: \"default\"\n" +
    "struct Widget:\n    name: text\n" +
    "impl Widget:\n    fn describe() -> text: \"widget:\"\n    static fn category() -> text: \"static\"\n" +
    "impl DefaultDescribe for Widget:\n    pass_dn\n" +
    "fn call_describe(value: Widget) -> text: value.describe()\n" +
    "fn call_category() -> text: Widget.category()\n" +
    "fn call_inherited(value: Widget) -> text: value.inherited()\n"
val parsed = parse_full_frontend(source, "method_text", "method_text", Logger(level: 0))
var lowering = HirLowering.with_filename("method_text.spl")
val hir = lowering.lower_module(parsed)
expect(lowering.errors.len()).to_equal(0)
val owner = hir.symbols.lookup("Widget").unwrap()
val instance_id = hir.symbols.lookup("method_text.Widget::describe").unwrap()
val static_id = hir.symbols.lookup("method_text.Widget::category").unwrap()
val inherited_id = hir.symbols.lookup("method_text.Widget::inherited").unwrap()
expect(symbol_is_text_callable(hir.symbols, instance_id, 1, owner.id)).to_equal(true)
expect(symbol_is_text_callable(hir.symbols, static_id, 0, -1)).to_equal(true)
expect(symbol_is_text_callable(hir.symbols, inherited_id, 1, owner.id)).to_equal(true)

val (resolved_hir, resolve_errors) = resolve_methods(hir)
expect(resolve_errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(resolved_hir.symbols)
val mir = mir_lowering.lower_module(resolved_hir)
expect(mir_call_has_text_return(mir, "method_text.Widget.describe")).to_equal(true)
expect(mir_call_has_text_return(mir, "method_text.Widget.category")).to_equal(true)
expect(mir_call_has_text_return(mir, "method_text.Widget.inherited")).to_equal(true)
```

</details>

#### keeps imported same-named method owners module-qualified

- keeps imported same-named method owners module-qualified
   - Expected: consumer_lowering.errors.len() equals `0`
   - Expected: consumer_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps imported same-named method owners module-qualified")
val owner_source = "struct Shared:\n    handle: i64\n" +
    "impl Shared:\n    fn cleanup(self) -> i64: 17\n"
val owner_a = parse_full_frontend(owner_source, "owner_a", "owner_a", Logger(level: 0))
val owner_b = parse_full_frontend(owner_source.replace("17", "99"), "owner_b", "owner_b", Logger(level: 0))
val consumer_source = "use owner_a.{Shared as CodegenOwner}\n" +
    "use owner_b.{Shared as JitOwner}\n" +
    "fn call_a(value: CodegenOwner) -> i64: value.cleanup()\n" +
    "fn call_b(value: JitOwner) -> i64: value.cleanup()\n"
val consumer = parse_full_frontend(consumer_source, "consumer", "consumer", Logger(level: 0))
var modules: Dict<text, any> = {}
modules["owner_a"] = owner_a
modules["owner_b"] = owner_b
var consumer_lowering = HirLowering.with_filename("consumer.spl")
consumer_lowering.modules_by_name = modules
val consumer_hir = consumer_lowering.lower_module(consumer)
expect(consumer_lowering.errors.len()).to_equal(0)
val (resolved_consumer, consumer_errors) = resolve_methods(consumer_hir)
expect(consumer_errors.len()).to_equal(0)
var consumer_mir_lowering = MirLowering.new(resolved_consumer.symbols)
val consumer_mir = consumer_mir_lowering.lower_module(resolved_consumer)
val imported_calls = mir_call_names(consumer_mir)
expect(imported_calls).to_contain("owner_a.Shared.cleanup")
expect(imported_calls).to_contain("owner_b.Shared.cleanup")
```

</details>

#### predeclares imported aliased instance and static text method signatures

- predeclares imported aliased instance and static text method signatures
   - Expected: lowering.errors.len() equals `0`
   - Expected: symbol_is_text_callable(hir.symbols, instance_id, 1, alias_owner.id) is true
   - Expected: symbol_is_text_callable(hir.symbols, static_id, 0, -1) is true
   - Expected: symbol_is_text_callable(hir.symbols, inherited_id, 1, alias_owner.id) is true
   - Expected: resolve_errors.len() equals `0`
   - Expected: mir_call_has_text_return(mir, "owner_text.Shared.describe") is true
   - Expected: mir_call_has_text_return(mir, "owner_text.Shared.category") is true
   - Expected: mir_call_has_text_return(mir, "owner_text.Shared.inherited") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("predeclares imported aliased instance and static text method signatures")
val owner_source = "trait DefaultDescribe:\n    fn inherited(self) -> text: \"default\"\n" +
    "struct Shared:\n    handle: i64\n" +
    "impl Shared:\n    fn describe(self) -> text: \"owner\"\n    static fn category() -> text: \"static\"\n" +
    "impl DefaultDescribe for Shared:\n    pass_dn\n"
val owner_module = parse_full_frontend(owner_source, "owner_text", "owner_text", Logger(level: 0))
val consumer_source = "use owner_text.{Shared as Alias}\n" +
    "fn call_instance(value: Alias) -> text: value.describe()\n" +
    "fn call_static() -> text: Alias.category()\n" +
    "fn call_inherited(value: Alias) -> text: value.inherited()\n"
val consumer = parse_full_frontend(consumer_source, "consumer_text", "consumer_text", Logger(level: 0))
var modules: Dict<text, any> = {}
modules["owner_text"] = owner_module
var lowering = HirLowering.with_filename("consumer_text.spl")
lowering.modules_by_name = modules
val hir = lowering.lower_module(consumer)
expect(lowering.errors.len()).to_equal(0)
val alias_owner = hir.symbols.lookup("Alias").unwrap()
val instance_id = hir.symbols.lookup("owner_text.Shared::describe").unwrap()
val static_id = hir.symbols.lookup("owner_text.Shared::category").unwrap()
val inherited_id = hir.symbols.lookup("owner_text.Shared::inherited").unwrap()
expect(symbol_is_text_callable(hir.symbols, instance_id, 1, alias_owner.id)).to_equal(true)
expect(symbol_is_text_callable(hir.symbols, static_id, 0, -1)).to_equal(true)
expect(symbol_is_text_callable(hir.symbols, inherited_id, 1, alias_owner.id)).to_equal(true)

val (resolved_hir, resolve_errors) = resolve_methods(hir)
expect(resolve_errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(resolved_hir.symbols)
val mir = mir_lowering.lower_module(resolved_hir)
expect(mir_call_has_text_return(mir, "owner_text.Shared.describe")).to_equal(true)
expect(mir_call_has_text_return(mir, "owner_text.Shared.category")).to_equal(true)
expect(mir_call_has_text_return(mir, "owner_text.Shared.inherited")).to_equal(true)
```

</details>

#### runs module method resolution against owned symbols

- runs module method resolution against owned symbols
   - Expected: source does not contain `val symbols = SymbolTable.new()\n    val resolver = create_method_resolver(sy... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("runs module method resolution against owned symbols")
val source = file_read("src/compiler/35.semantics/resolve.spl")
val lowering_source = file_read("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
val module_source = file_read("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val bootstrap_mir_source = file_read("src/compiler/50.mir/_MirLowering/bootstrap_globals.spl")
expect(source).to_contain("create_method_resolver(module.symbols)")
expect(source.contains("val symbols = SymbolTable.new()\n    val resolver = create_method_resolver(symbols)")).to_equal(false)
expect(lowering_source).to_contain("== \"1\" and not fn_.is_method")
expect(module_source).to_contain("impls: impls")
expect(bootstrap_mir_source).to_contain("bootstrap_hir_function_symbol_name")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MethodResolver nil guards.
- MethodResolver nil guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `258aa381c79ba4e09fe977e50673ce59778bdec07f2ad7e79037acd109a3d829`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `258aa381c79ba4e09fe977e50673ce59778bdec07f2ad7e79037acd109a3d829`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `258aa381c79ba4e09fe977e50673ce59778bdec07f2ad7e79037acd109a3d829`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/resolve_nil_guard_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/semantics/resolve_nil_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/resolve_nil_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps module resolution methods owned by MethodResolver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves named call arguments through resolution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps UFCS working when current_fn_sym is Some(nil)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
