# Mir Lowering New Specification

> Tests covering Mir Lowering New.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Lowering New Specification

## Scenarios

### Mir Lowering New

#### keeps MirLowering state shape available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps MirLowering state shape available


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MirLowering state shape available")
val source = read_mir_source("src/compiler/50.mir/mir_lowering_types.spl")

expect(source).to_contain("struct MirLowering")
expect(source).to_contain("builder: MirBuilder")
expect(source).to_contain("symbols: SymbolTable")
expect(source).to_contain("struct_method_ambiguous: Dict<text, bool>")
```

</details>

#### keeps MirLowering constructor wired to HIR symbols

- keeps MirLowering constructor wired to HIR symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MirLowering constructor wired to HIR symbols")
val source = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")

expect(source).to_contain("static fn new(symbols: SymbolTable) -> MirLowering")
expect(source).to_contain("symbols: symbols")
```

</details>

#### resets method lookup state at every module boundary

- resets method lookup state at every module boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resets method lookup state at every module boundary")
val source = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")

expect(source).to_contain("self.struct_method_syms = {}")
expect(source).to_contain("self.struct_method_ambiguous = {}")
expect(source).to_contain("self.struct_method_return_names = {}")
expect(source).to_contain("self.struct_method_return_is_array = {}")
```

</details>

#### classifies runtime Dict locals by discriminant

- classifies runtime Dict locals by discriminant
   - Expected: parts.len() equals `2`
   - Expected: helper does not contain `case MirTypeKind.Dict(_, _): true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies runtime Dict locals by discriminant")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val parts = source.split("fn local_is_runtime_dict(local: LocalId) -> bool:")
expect(parts.len()).to_equal(2)
val helper = parts[1].split("me remember_field_projection_provenance")[0]

expect(helper).to_contain("rt_enum_discriminant(type_.kind) == rt_enum_discriminant(MirTypeKind.Dict(MirType.i64(), MirType.i64()))")
expect(helper.contains("case MirTypeKind.Dict(_, _): true")).to_equal(false)
```

</details>

#### keeps chr text tagged until length-bearing runtime calls

- keeps chr text tagged until length-bearing runtime calls
   - Expected: source does not contain `return self.decode_runtime_value(chr_local, chr_text_type)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps chr text tagged until length-bearing runtime calls")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
val dispatch = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(source).to_contain("self.runtime_value_locals.contains(value_local.id) and self.local_is_str(value_local)")
expect(source).to_contain("len_symbol = \"rt_string_len\"")
expect(source).to_contain("self.runtime_value_locals[chr_text.id] = true")
expect(source).to_contain("self.local_hir_types[chr_text.id] = HirType(kind: HirTypeKind.Str, span: receiver.span)")
expect(source.contains("return self.decode_runtime_value(chr_local, chr_text_type)")).to_equal(false)
expect(dispatch).to_contain("var len_func_name = \"rt_string_len\"")
expect(dispatch).to_contain("var fa_len_func_name = \"rt_string_len\"")
```

</details>

#### initializes runtime tracking maps in manual MirLowering constructors

- initializes runtime tracking maps in manual MirLowering constructors
   - Expected: direct_parts.len() equals `2`
   - Expected: fallback_parts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("initializes runtime tracking maps in manual MirLowering constructors")
val source = read_mir_source(
    "src/compiler/80.driver/driver_pipeline_lowering.spl")

val direct_parts = source.split("var direct_lowering = MirLowering(")
expect(direct_parts.len()).to_equal(2)
val direct_body = direct_parts[1].split("current_has_vhdl_metadata: false")[0]
expect(direct_body).to_contain("runtime_value_locals: {},")
expect(direct_body).to_contain("local_hir_types: {},")
expect(direct_body).to_contain("nil_locals: {},")
expect(direct_body).to_contain("struct_method_ambiguous: {},")
val fallback_parts = source.split("var lowering = MirLowering(")
expect(fallback_parts.len()).to_equal(2)
val fallback_body = fallback_parts[1].split("current_has_vhdl_metadata: false")[0]
expect(fallback_body).to_contain("runtime_value_locals: {},")
expect(fallback_body).to_contain("local_hir_types: {},")
expect(fallback_body).to_contain("nil_locals: {},")
expect(fallback_body).to_contain("struct_method_ambiguous: {},")
```

</details>

#### keeps named bootstrap calls from becoming unknown symbol calls

- keeps named bootstrap calls from becoming unknown symbol calls
   - Expected: source does not contain `[dbg-namedvar]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps named bootstrap calls from becoming unknown symbol calls")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
val dispatch_source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val hir_source = read_mir_source("src/compiler/20.hir/hir_lowering/expressions.spl")

expect(source).to_contain("case NamedVar(symbol, callee_name):")
expect(source).to_contain("MirConstValue.Str(callee_name)")
expect(source).to_contain("case Var(symbol):")
expect(source).to_contain("me bootstrap_resolved_call_name(symbol: SymbolId) -> text:")
expect(source).to_contain("if val found_sym = sym:")
expect(source).to_contain("var call_name = \"\"")
expect(source).to_contain("call_name = self.bootstrap_resolved_call_name(symbol)")
expect(source).to_contain("MirConstValue.Str(call_name)")
expect(source).to_contain("MirSignature(params: [], return_type: return_type, is_variadic: false)")
expect(source).to_contain("me bootstrap_call_return_type(name: text) -> MirType:")
expect(source).to_contain("name == \"get_args\" or name == \"get_cli_args\"")
expect(source).to_contain("return MirType.ptr(self.bootstrap_text_array_type(), false)")
expect(source).to_contain("name == \"bootstrap_version\"")
expect(source).to_contain("return self.bootstrap_text_type()")
expect(source).to_contain("name == \"bootstrap_output_from_args\"")
expect(source).to_contain("return MirType.ptr(self.bootstrap_text_type(), false)")
expect(source).to_contain("name == \"eprint\"")
expect(source).to_contain("return MirType.unit()")
expect(source).to_contain("self.bootstrap_resolved_call_return_type(symbol, call_name)")
expect(source).to_contain("self.bootstrap_resolved_call_return_type(symbol, callee_name)")
expect(source).to_contain("if resolved_symbol != nil and resolved_symbol.type_ != nil:")
expect(source).to_contain("match self.local_mir_type_of(arg_local):")
expect(source).to_contain("case Some(arg_ty):")
expect(dispatch_source).to_contain("if sym != nil and sym.type_ != nil:")
expect(source.contains("[dbg-namedvar]")).to_equal(false)
expect(hir_source).to_contain("fn is_bootstrap_builtin_fn(name: text) -> bool:")
expect(hir_source).to_contain("name == \"get_args\"")
expect(hir_source).to_contain("name == \"eprint\"")
expect(hir_source).to_contain("name == \"get_cli_args\"")
expect(hir_source).to_contain("name == \"run_native_build_bootstrap\"")
expect(hir_source).to_contain("fn bootstrap_builtin_signature(name: text, span: Span) -> HirType:")
expect(hir_source).to_contain("HirTypeKind.Function([], bootstrap_builtin_return_type(name, span), [])")
expect(hir_source).to_contain("is_bootstrap_builtin_fn(name)")
```

</details>

#### keeps indirect call result metadata on the function return type

- keeps indirect call result metadata on the function return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps indirect call result metadata on the function return type")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")

expect(source).to_contain("if val callee_type = callee.type_:")
expect(source).to_contain("ret_type = self.lower_type(callee_type)")
```

</details>

#### keeps MIR type lowering from reading kind on nil

- keeps MIR type lowering from reading kind on nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MIR type lowering from reading kind on nil")
val source = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")

expect(source).to_contain("if type_ == nil:")
expect(source).to_contain("missing HIR type during MIR lowering")
expect(source).to_contain("return MirType(kind: MirTypeKind.I64)")
expect(source).to_contain("match type_.kind:")
```

</details>

#### keeps HIR parameters fully initialized and non-optional in MIR

- keeps HIR parameters fully initialized and non-optional in MIR
   - Expected: hir_source does not contain `if p.default.?:`
   - Expected: mir_source does not contain `if val found_symbol = param.symbol:`
   - Expected: interpreter_source does not contain `param.default.?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps HIR parameters fully initialized and non-optional in MIR")
val hir_source = read_mir_source("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
val mir_source = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val interpreter_source = read_mir_source("src/compiler/70.backend/backend/interpreter_calls.spl")

expect(hir_source).to_contain("if p.has_default:")
expect(hir_source).to_contain("has_default: p.has_default")
expect(hir_source).to_contain("kind: HirExprKind.NilLit")
expect(hir_source.contains("if p.default.?:")).to_equal(false)
expect(mir_source).to_contain("val param_symbol_id = param.symbol.id")
expect(mir_source).to_contain("self.bind_local(param_symbol_id, local)")
expect(mir_source.contains("if val found_symbol = param.symbol:")).to_equal(false)
expect(interpreter_source).to_contain("elif param.has_default:")
expect(interpreter_source).to_contain("self.eval_expr(param.default, ctx)?")
expect(interpreter_source.contains("param.default.?")).to_equal(false)
```

</details>

#### keeps named array parameter provenance for indexed field mutation

- keeps named array parameter provenance for indexed field mutation
   - Expected: array_param_parts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps named array parameter provenance for indexed field mutation")
val params = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val index = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val fixture = read_mir_source("test/fixtures/compiler/native_class_array_param_field_mutation.spl")
val harness = read_mir_source("scripts/check/check-native-seed-parity.shs")
val array_param_parts = params.split("case Array(element_type, _):")

expect(array_param_parts.len()).to_equal(2)
val array_param = array_param_parts[1].split("case Named(type_symbol, _):")[0]
expect(array_param).to_contain("self.runtime_array_locals[local.id] = true")
expect(array_param).to_contain("case Named(element_symbol, _):")
expect(array_param).to_contain("self.symbols.get_symbol(element_symbol)")
expect(array_param).to_contain("self.array_element_struct_syms[local.id] = element.name")
expect(index).to_contain("self.array_element_struct_syms.get(base_local.id)")
expect(index).to_contain("self.struct_value_syms[decoded_elem.id] = esn")
expect(fixture).to_contain("fn mutate_first(counters: [Counter]):")
expect(fixture).to_contain("counters[0].value = counters[0].value + 1")
expect(harness).to_contain("run_strict_dual_backend_case class_array_param_field_mutation test/fixtures/compiler/native_class_array_param_field_mutation.spl \"1\"")
```

</details>

#### keeps MIR expression lowering from passing nil HIR types to lower_type

- keeps MIR expression lowering from passing nil HIR types to lower_type


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MIR expression lowering from passing nil HIR types to lower_type")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")

expect(source).to_contain("val maybe_receiver_type_for_call = receiver.type_")
expect(source).to_contain("if found_receiver_type != nil:")
expect(source).to_contain("receiver_type = self.lower_type(found_receiver_type)")
expect(source).to_contain("len_symbol = self.len_runtime_symbol_for_hir_type(found_receiver_type)")
expect(source).to_contain("if type_ == nil:")
expect(source).to_contain("return \"\"")
expect(source).to_contain("val maybe_elem_type = elem.type_")
expect(source).to_contain("if elem_type != nil:")
expect(source).to_contain("elem_ty = self.lower_type(elem_type)")
```

</details>

#### keeps MIR expression lowering from matching kind on nil input

- keeps MIR expression lowering from matching kind on nil input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MIR expression lowering from matching kind on nil input")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(source).to_contain("var expr_value = nil_expr")
expect(source).to_contain("if expr != nil:")
expect(source).to_contain("expr_value = expr")
expect(source).to_contain("match expr_value.kind:")
```

</details>

#### preserves enum payload positions across wildcard patterns

- preserves enum payload positions across wildcard patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves enum payload positions across wildcard patterns")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")

expect(source).to_contain("out.push(SymbolId.new(-1))")
expect(source).to_contain("if bind_syms[0].id >= 0:")
expect(source).to_contain("if bind_syms[fi].id >= 0:")
expect(source).to_contain("rt_tuple_get")
```

</details>

#### uses native-safe indexed scans for MIR locals and enum constructors

- uses native-safe indexed scans for MIR locals and enum constructors
   - Expected: stmt_source does not contain `for item in self.builder.locals:`
   - Expected: dispatch_source does not contain `for item in self.builder.locals:`
   - Expected: method_source does not contain `for vn in self.enum_variant_index[recv_enum_name]:`
   - Expected: call_source does not contain `for ename in enum_names:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses native-safe indexed scans for MIR locals and enum constructors")
val stmt_source = read_mir_source("src/compiler/50.mir/mir_lowering_stmts.spl")
val dispatch_source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val method_source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
val call_source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")

expect(stmt_source.contains("for item in self.builder.locals:")).to_equal(false)
expect(dispatch_source.contains("for item in self.builder.locals:")).to_equal(false)
expect(dispatch_source).to_contain("val named_var_payload = rt_enum_payload(expr_value.kind)")
expect(dispatch_source).to_contain("val named_var_symbol: SymbolId = rt_tuple_get(named_var_payload, 0)")
expect(dispatch_source).to_contain("val raw_named_local = self.find_local(named_var_symbol_id)")
expect(method_source).to_contain("val receiver_disc = rt_enum_discriminant(receiver_kind)")
expect(method_source).to_contain("val named_receiver_payload = rt_enum_payload(receiver_kind)")
expect(method_source).to_contain("recv_enum_name = rt_array_get_text(named_receiver_payload, 1)")
expect(method_source).to_contain("val variant_names = self.enum_variant_index[recv_enum_name]")
expect(method_source).to_contain("while variant_i < variant_names.len():")
expect(method_source.contains("for vn in self.enum_variant_index[recv_enum_name]:")).to_equal(false)
expect(call_source).to_contain("case HirExprKind.NamedVar(symbol, name):")
expect(call_source).to_contain("if not is_direct:")
expect(call_source).to_contain("val named_callee_payload = rt_enum_payload(callee.kind)")
expect(call_source).to_contain("val named_callee_symbol: SymbolId = rt_tuple_get(named_callee_payload, 0)")
expect(call_source).to_contain("direct_name = rt_array_get_text(named_callee_payload, 1)")
expect(call_source).to_contain("self.find_local(direct_symbol.id).id >= 0")
expect(call_source).to_contain("val arm_pattern_payload = rt_enum_payload(arm_pattern_kind)")
expect(call_source).to_contain("val etype: HirType = rt_tuple_get(arm_pattern_payload, 0)")
expect(call_source).to_contain("val epayload: HirPatternPayload? = rt_tuple_get(arm_pattern_payload, 2)")
expect(call_source).to_contain("val binding_symbol: SymbolId = rt_tuple_get(binding_payload, 0)")
expect(call_source).to_contain("while enum_i < enum_names.len():")
expect(call_source.contains("for ename in enum_names:")).to_equal(false)
```

</details>

#### keeps MIR diagnostics independent of malformed native span payloads

- keeps MIR diagnostics independent of malformed native span payloads
   - Expected: source does not contain `err.span.unwrap()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps MIR diagnostics independent of malformed native span payloads")
val source = read_mir_source(
    "src/compiler/80.driver/driver_pipeline_lowering.spl")

expect(source).to_contain('"MIR lowering error: {err.message}"')
expect(source.contains("err.span.unwrap()")).to_equal(false)
expect(source).to_contain('message.starts_with("undefined variable")')
```

</details>

#### reads required MIR identifier wrappers without native destructuring

- reads required MIR identifier wrappers without native destructuring
   - Expected: named_var_arm does not contain `self.symbols.lookup(name)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads required MIR identifier wrappers without native destructuring")
val dispatch = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val statements = read_mir_source("src/compiler/50.mir/mir_lowering_stmts.spl")
val module = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")
val json = read_mir_source("src/compiler/50.mir/mir_json.spl")

expect(dispatch).to_contain("fn mir_expr_symbol_id_value(symbol: SymbolId) -> i64:\n    symbol.id")
val named_var_arm = dispatch.split("case NamedVar(symbol, name):")[1].split("case Binary(op, left, right):")[0]
expect(named_var_arm).to_contain("val symbol_id = mir_expr_symbol_id_value(symbol)")
expect(named_var_arm.contains("self.symbols.lookup(name)")).to_equal(false)
expect(statements).to_contain("fn mir_stmt_symbol_id_value(symbol: SymbolId) -> i64:\n    symbol.id")
expect(statements).to_contain("fn mir_stmt_local_id_value(local: LocalId) -> i64:\n    local.id")
expect(module).to_contain("fn symbol_id_value(symbol: SymbolId) -> i64:\n        symbol.id")
expect(json).to_contain("fn block_id_value(block: BlockId) -> i64:\n    block.id")
```

</details>

#### persists MIR local bindings through the MirLowering owner

- persists MIR local bindings through the MirLowering owner
   - Expected: statements does not contain `self.local_map[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("persists MIR local bindings through the MirLowering owner")
val types = read_mir_source("src/compiler/50.mir/mir_lowering_types.spl")
val functions = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val statements = read_mir_source("src/compiler/50.mir/mir_lowering_stmts.spl")
val calls = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")

expect(types).to_contain("me bind_local(symbol_id: i64, local: LocalId):")
expect(types).to_contain("local_symbol_ids: [i64]")
expect(types).to_contain("local_symbol_values: [LocalId]")
expect(types).to_contain("fn find_local(symbol_id: i64) -> LocalId:")
expect(functions).to_contain("self.bind_local(param_symbol_id, local)")
expect(statements.contains("self.local_map[")).to_equal(false)
expect(calls).to_contain("self.bind_local(bind_syms[fi].id, gl)")
```

</details>

#### predispatches match expressions before native pattern extraction

- predispatches match expressions before native pattern extraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("predispatches match expressions before native pattern extraction")
val source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(source).to_contain("val match_case_pre_disc = rt_enum_discriminant(HirExprKind.MatchCase(nil_expr, []))")
expect(source).to_contain("return self.lower_match_case(match_scrutinee, match_arms)")
```

</details>

#### defines match bindings before lowering arm bodies

- defines match bindings before lowering arm bodies


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("defines match bindings before lowering arm bodies")
val source = read_mir_source("src/compiler/20.hir/hir_lowering/expressions.spl")

expect(source).to_contain("val hir_pattern = self.lower_pattern(typed_arm.pattern)")
expect(source).to_contain("val hir_guard = self.lower_hir_expr(typed_arm.guard)")
expect(source).to_contain("val hir_body = self.lower_hir_block(typed_arm.body)")
expect(source).to_contain("pattern: hir_pattern")
expect(source).to_contain("body: hir_body")
```

</details>

#### bootstraps enum and binding patterns without self-host match extraction

- bootstraps enum and binding patterns without self-host match extraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bootstraps enum and binding patterns without self-host match extraction")
val source = read_mir_source("src/compiler/20.hir/hir_lowering/expressions.spl")
val bridge = read_mir_source("src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl")

expect(source).to_contain("val pattern_disc = hir_pattern_kind_disc(pattern_kind_value)")
expect(source).to_contain("val binding_name = rt_array_get_text(raw_payload, 0)")
expect(source).to_contain("val payload_slot = rt_tuple_get(raw_payload, 2)")
expect(source).to_contain("if not rt_is_none(payload_slot):")
expect(source).to_contain("var payload_value = payload_slot")
expect(source).to_contain("if payload_disc != tuple_disc and payload_disc != struct_disc:")
expect(source).to_contain("payload_value = rt_unwrap_or_self(payload_slot)")
expect(source).to_contain("var payload_disc = rt_enum_discriminant(payload_value)")
expect(source).to_contain("rt_enum_payload(payload_value) as [Pattern]")
expect(source).to_contain("rt_enum_payload(payload_value) as [(text, Pattern)]")
expect(source).to_contain("return HirPattern(kind: HirPatternKind.Enum(enum_type, variant_name, hir_payload)")
expect(bridge).to_contain("mc_sub.push(convert_flat_pattern(a_eid))")
expect(bridge).to_contain("sub.push(convert_flat_pattern(a_eid))")
expect(bridge).to_contain("bsub.push(convert_flat_pattern(b_eid))")
```

</details>

#### routes HIR module dictionary views through explicit runtime owners

- routes HIR module dictionary views through explicit runtime owners
   - Expected: source does not contain `module.functions.values()`
   - Expected: source does not contain `impl_def.methods.keys()`
   - Expected: source does not contain `self.enum_variant_index.has("Result")`
   - Expected: source does not contain `struct_method_first_owner.get(impl_method_name)`
   - Expected: source does not contain `free_function_names.has(impl_method_name)`
   - Expected: dispatch_source does not contain `match arms[scan_i].pattern.kind:`
   - Expected: function_source does not contain `self.struct_value_syms.get(base_local.id)`
   - Expected: switch_source does not contain `self.enum_variant_index.keys()`
   - Expected: method_source does not contain `self.struct_value_syms.get(unresolved_receiver_local.id)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes HIR module dictionary views through explicit runtime owners")
val source = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")
val function_source = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val switch_source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
val dispatch_source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val method_source = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
val sffi_source = read_mir_source("src/compiler_rust/lib/std/src/alloc/sffi.spl")

expect(source).to_contain("use std.alloc.sffi.{rt_dict_contains, rt_dict_keys, rt_dict_values}")
expect(source).to_contain("rt_dict_values(module.functions)")
expect(source).to_contain("rt_dict_keys(impl_def.methods)")
expect(source).to_contain("rt_dict_contains(self.enum_variant_index, \"Result\")")
expect(source).to_contain("rt_dict_contains(struct_method_first_owner, impl_method_name)")
expect(source).to_contain("rt_dict_contains(free_function_names, impl_method_name)")
expect(source.contains("module.functions.values()")).to_equal(false)
expect(source.contains("impl_def.methods.keys()")).to_equal(false)
expect(source.contains("self.enum_variant_index.has(\"Result\")")).to_equal(false)
expect(source.contains("struct_method_first_owner.get(impl_method_name)")).to_equal(false)
expect(source.contains("free_function_names.has(impl_method_name)")).to_equal(false)
expect(sffi_source).to_contain("rt_dict_contains(dict: i64, key: Any)")
expect(function_source).to_contain("rt_dict_contains(arg_locals, pli)")
expect(switch_source).to_contain("rt_dict_contains(self.enum_variant_index, enum_name)")
expect(dispatch_source).to_contain("self.find_local(symbol_id).id >= 0")
expect(dispatch_source).to_contain("val enum_pattern_disc = rt_enum_discriminant(HirPatternKind.Enum(")
expect(dispatch_source).to_contain("return self.lower_enum_match(scrutinee, arms)")
expect(dispatch_source.contains("match arms[scan_i].pattern.kind:")).to_equal(false)
expect(method_source).to_contain("rt_dict_contains(self.struct_method_syms, unresolved_method_key)")
expect(method_source).to_contain("receiver_is_dict or self.local_is_runtime_dict(receiver_local)")
expect(method_source).to_contain("elif has_prelowered_method_receiver:")
expect(function_source.contains("self.struct_value_syms.get(base_local.id)")).to_equal(false)
expect(switch_source.contains("self.enum_variant_index.keys()")).to_equal(false)
expect(method_source.contains("self.struct_value_syms.get(unresolved_receiver_local.id)")).to_equal(false)
```

</details>

#### walks parent scopes without native Option pattern destructuring

- walks parent scopes without native Option pattern destructuring
   - Expected: source does not contain `match scope.parent:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("walks parent scopes without native Option pattern destructuring")
val source = read_mir_source("src/compiler/20.hir/hir_types.spl")

expect(source).to_contain("if scope.parent.?:")
expect(source).to_contain("scope_id = scope.parent.unwrap()")
expect(source).to_contain("self.current_scope = scope.parent.unwrap()")
expect(source.contains("match scope.parent:")).to_equal(false)
```

</details>

#### keeps bootstrap diagnostics contextual and opt-in

- keeps bootstrap diagnostics contextual and opt-in


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps bootstrap diagnostics contextual and opt-in")
val driver_log = read_mir_source("src/compiler/80.driver/driver_log_helpers.spl")
val driver_pipeline = read_mir_source(
    "src/compiler/80.driver/driver_pipeline_lowering.spl")
val hir_module = read_mir_source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val hir_decl = read_mir_source("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
val mir_module = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")
val mir_function = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val rust_state = read_mir_source("src/compiler_rust/compiler/src/interpreter_state.rs")
val rust_calls = read_mir_source("src/compiler_rust/compiler/src/interpreter/expr/calls.rs")

expect(driver_log).to_contain("SIMPLE_COMPILER_PHASE_PROFILE")
expect(driver_pipeline).to_contain("MIR lowering missing HIR module for {name_direct} ({src_direct.path})")
expect(driver_pipeline).to_contain("aot:lower_to_mir:module:start idx={direct_idx} module={name_direct} path={src_direct.path}")
expect(hir_module).to_contain("fn hir_module_diag_enabled() -> bool:")
expect(hir_module).to_contain("lower_module:start module={module.name} path={module.path}")
expect(hir_decl).to_contain("fn hir_lower_diag_enabled() -> bool:")
expect(mir_module).to_contain("lower_module:start module={module.name} functions={module.functions.len()}")
expect(mir_function).to_contain("SIMPLE_BOOTSTRAP_DIAG")
expect(rust_state).to_contain("OnceLock<bool>")
expect(rust_state).to_contain("fn field_access_debug_enabled() -> bool")
expect(rust_calls).to_contain("field_access_debug_enabled()")
expect(rust_calls).to_contain("hint=set SIMPLE_BOOTSTRAP_DIAG=1 or SIMPLE_DEBUG_FIELD_ACCESS=1")
```

</details>

#### keeps let statement payload extraction single-assignment

- keeps let statement payload extraction single-assignment
   - Expected: source does not contain `var let_symbol: SymbolId? = nil`
   - Expected: source does not contain `var let_type: HirType? = nil`
   - Expected: source does not contain `var let_init = HirExpr`
   - Expected: source does not contain `if val symbol_value = let_symbol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps let statement payload extraction single-assignment")
val source = read_mir_source("src/compiler/50.mir/mir_lowering_stmts.spl")

expect(source.contains("var let_symbol: SymbolId? = nil")).to_equal(false)
expect(source.contains("var let_type: HirType? = nil")).to_equal(false)
expect(source.contains("var let_init = HirExpr")).to_equal(false)
expect(source.contains("if val symbol_value = let_symbol")).to_equal(false)
expect(source).to_contain("val let_symbol = match stmt_kind_value")
expect(source).to_contain("val let_type = match stmt_kind_value")
expect(source).to_contain("val let_init = match stmt_kind_value")
```

</details>

#### keeps LLVM indirect call return and argument types explicit

- keeps LLVM indirect call return and argument types explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps LLVM indirect call return and argument types explicit")
val source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl")

expect(source).to_contain("case Some(dest_local): self.valid_llvm_type(self.get_local_type(self.local_id_value(dest_local)))")
expect(source).to_contain("if sig.return_type == nil: \"void\" else: self.valid_llvm_type(self.llvm_type_text(sig.return_type))")
expect(source).to_contain("if arg_i < sig.params.len():")
expect(source).to_contain("arg_ty = self.valid_llvm_type(self.llvm_type_text(param_ty))")
expect(source).to_contain('arg_vals = arg_vals.push("{arg_ty} {self.translate_operand(arg)}")')
```

</details>

#### keeps native entry parse tracing and missing-entry diagnostics

- keeps native entry parse tracing and missing-entry diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps native entry parse tracing and missing-entry diagnostics")
val source = read_mir_source("src/compiler/80.driver/driver.spl")

expect(source).to_contain("phase2:parse:entry")
expect(source).to_contain("phase2:parse:entry:done")
expect(source).to_contain("native entry source not found")
```

</details>

#### keeps LLVM known call return types aligned with function definitions

- keeps LLVM known call return types aligned with function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps LLVM known call return types aligned with function definitions")
val class_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/class_def.spl")
val codegen_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl")
val split_codegen_source = read_mir_source("src/compiler/70.backend/backend/mir_to_llvm_instructions.spl")
val aggregate_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl")
val asm_source = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl")

expect(class_source).to_contain("function_return_types: Dict<text, text>")
expect(codegen_source).to_contain("me remember_function_return_type(name: text, ret_ty: text):")
expect(codegen_source).to_contain("ret_ty == nil or ret_ty == \"nil\"")
expect(codegen_source).to_contain("self.remember_function_return_type(fn_name, ret_ty)")
expect(codegen_source).to_contain("fn lookup_function_return_type(func_name: text) -> text:")
expect(codegen_source).to_contain("func_name.starts_with(\"@\")")
expect(codegen_source).to_contain("var known_ret_ty = self.lookup_function_return_type(call_func_name)")
expect(codegen_source).to_contain("known_ret_ty != \"nil\"")
expect(codegen_source).to_contain("bare_name_for_call == \"get_args\" or bare_name_for_call == \"get_cli_args\"")
expect(codegen_source).to_contain("@rt_get_args")
expect(codegen_source).to_contain("if signature.return_type != nil:")
expect(codegen_source).to_contain("self.remember_function_return_type(name, self.llvm_type_text(signature.return_type))")
expect(codegen_source).to_contain("case Function(_, ret):")
expect(codegen_source).to_contain("if ret != nil:")
expect(codegen_source).to_contain("self.remember_function_return_type(name, self.llvm_type_text(ret))")
expect(codegen_source).to_contain("me mark_ptr_local(id: i64):")
expect(codegen_source).to_contain("self.local_types[dest_id] = ret_ty")
expect(codegen_source).to_contain("self.ptr_locals[dest_id] = true")
expect(split_codegen_source).to_contain("var known_ret_ty = self.lookup_function_return_type(call_func_name)")
expect(split_codegen_source).to_contain("ret_ty = self.valid_llvm_type(self.get_local_type(dest_id))")
expect(split_codegen_source).to_contain("known_ret_ty != \"nil\"")
expect(split_codegen_source).to_contain("bare_name_for_call == \"get_args\" or bare_name_for_call == \"get_cli_args\"")
expect(split_codegen_source).to_contain("@rt_get_args")
expect(split_codegen_source).to_contain("self.mark_ptr_local(dest_id)")
expect(split_codegen_source).to_contain("GpuSharedAlloc (stub)")
expect(split_codegen_source).to_contain("if sig.return_type == nil: \"void\" else: self.valid_llvm_type(self.type_mapper.map_type(sig.return_type))")
expect(split_codegen_source).to_contain("arg_ty = self.valid_llvm_type(self.type_mapper.map_type(param_ty))")
expect(aggregate_source).to_contain("self.valid_llvm_type(self.get_local_type(dest_id))")
expect(asm_source).to_contain("self.valid_llvm_type(self.get_local_type(dest_id))")
```

</details>

#### keeps bootstrap runtime calls declared and name-mapped

- keeps bootstrap runtime calls declared and name-mapped


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps bootstrap runtime calls declared and name-mapped")
val llvm_backend_source = read_mir_source("src/compiler/70.backend/backend/llvm_backend.spl")
val wasm_decl_source = read_mir_source("src/compiler/70.backend/backend/llvm_backend_tools.spl")
val llvm_lib_expr_source = read_mir_source("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl")
val llvm_lib_decl_source = read_mir_source("src/compiler/70.backend/backend/llvm_lib_translate.spl")

expect(llvm_backend_source).to_contain("declare ptr @rt_get_args()")
expect(llvm_backend_source).to_contain("declare void @rt_eprint(ptr)")
expect(wasm_decl_source).to_contain("declare ptr @rt_get_args()")
expect(wasm_decl_source).to_contain("declare void @rt_eprint(ptr)")
expect(llvm_lib_expr_source).to_contain("name == \"get_args\" or name == \"get_cli_args\"")
expect(llvm_lib_expr_source).to_contain("\"rt_get_args\"")
expect(llvm_lib_decl_source).to_contain("declare_fn(mod_, \"rt_get_args\"")
```

</details>

#### keeps bootstrap flat block tail value state explicit

- keeps bootstrap flat block tail value state explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps bootstrap flat block tail value state explicit")
val source = read_mir_source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")

expect(source).to_contain("var has_value = false")
expect(source).to_contain("has_value = true")
expect(source).to_contain("HirBlock(stmts: stmts, has: has_value, value: value_expr, span: span)")
```

</details>

#### keeps frontend parser bridge trace markers

- keeps frontend parser bridge trace markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps frontend parser bridge trace markers")
val source = read_mir_source("src/compiler/10.frontend/frontend.spl")
val bridge = read_mir_source("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl")
val parser_module = read_mir_source("src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl")
val parser_stmts = read_mir_source("src/compiler/10.frontend/core/parser_stmts.spl")
val parser_expr = read_mir_source("src/compiler/10.frontend/core/parser_expr.spl")
val parser_primary = read_mir_source("src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl")
val ast_expr = read_mir_source("src/compiler/10.frontend/core/_AstExpr/nodes.spl")

expect(source).to_contain("[frontend] parse_and_build:start")
expect(source).to_contain("[frontend] parse_and_build:done")
expect(bridge).to_contain("[flat-bridge] path=")
expect(bridge).to_contain("[flat-bridge] bootstrap real entry:start")
expect(bridge).to_contain("[flat-bridge] decl:start")
expect(bridge).to_contain("[flat-bridge] building frontend module")
expect(bridge).to_contain("[flat-bridge] built frontend module")
expect(parser_module).to_contain("[parser-module] decl:start")
expect(parser_stmts).to_contain("[parser-block] stmt:start")
expect(parser_stmts).to_contain("[parser-block] expr-branch:start")
expect(parser_expr).to_contain("[parser-expr] expr:start")
expect(parser_expr).to_contain("parser_expr_trace_step(\"postfix\")")
expect(parser_primary).to_contain("[parser-primary] ident:start")
expect(parser_expr).to_contain("[parser-expr] call:start")
expect(ast_expr).to_contain("[ast-expr] call-alloc:start")
```

</details>

#### keeps integer div rem and right shift signedness aligned across native backends

- keeps integer div rem and right shift signedness aligned across native backends


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps integer div rem and right shift signedness aligned across native backends")
val textual_llvm = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl")
val llvm_api = read_mir_source("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl")
val cranelift = read_mir_source("src/compiler/70.backend/backend/cranelift_codegen_adapter.spl")
val legacy_cranelift = read_mir_source("src/compiler/70.backend/codegen.spl")
val parity = read_mir_source("scripts/check/check-native-seed-parity.shs")

expect(textual_llvm).to_contain("self.builder.emit_udiv(dest_name, ty, left_val, right_val)")
expect(textual_llvm).to_contain("self.builder.emit_div(dest_name, ty, left_val, right_val)")
expect(textual_llvm).to_contain("self.builder.emit_urem(dest_name, ty, left_val, right_val)")
expect(textual_llvm).to_contain("self.builder.emit_rem(dest_name, ty, left_val, right_val)")
expect(textual_llvm).to_contain("if left_unsigned:")
expect(textual_llvm).to_contain("self.builder.emit_lshr(dest_name, ty, left_val, right_val)")
expect(textual_llvm).to_contain("self.builder.emit_ashr(dest_name, ty, left_val, right_val)")

expect(llvm_api).to_contain("elif is_unsigned: llvm_build_udiv(builder, lhs, rhs, \"div\")")
expect(llvm_api).to_contain("else: llvm_build_sdiv(builder, lhs, rhs, \"div\")")
expect(llvm_api).to_contain("elif is_unsigned: llvm_build_urem(builder, lhs, rhs, \"rem\")")
expect(llvm_api).to_contain("else: llvm_build_srem(builder, lhs, rhs, \"rem\")")
expect(llvm_api).to_contain("if left_is_unsigned: llvm_build_lshr(builder, lhs, rhs, \"shr\")")
expect(llvm_api).to_contain("else: llvm_build_ashr(builder, lhs, rhs, \"shr\")")

expect(cranelift).to_contain("elif is_unsigned: cranelift_udiv(ctx, a, b) else: cranelift_sdiv(ctx, a, b)")
expect(cranelift).to_contain("if is_unsigned: cranelift_urem(ctx, a, b) else: cranelift_srem(ctx, a, b)")
expect(cranelift).to_contain("if left_is_unsigned: cranelift_ushr(ctx, a, b) else: cranelift_sshr(ctx, a, b)")
expect(legacy_cranelift).to_contain("if unsigned: cranelift_udiv(self.current_ctx, left, right) else: cranelift_sdiv(self.current_ctx, left, right)")
expect(legacy_cranelift).to_contain("if unsigned: cranelift_urem(self.current_ctx, left, right) else: cranelift_srem(self.current_ctx, left, right)")
expect(legacy_cranelift).to_contain("if left_unsigned: cranelift_ushr(self.current_ctx, left, right) else: cranelift_sshr(self.current_ctx, left, right)")
expect(parity).to_contain("run_strict_dual_backend_case unsigned_div_rem_shift write_case_unsigned_div_rem_shift \"111111\"")
```

</details>

#### keeps unsigned casts and ordered comparisons aligned across native backends

- keeps unsigned casts and ordered comparisons aligned across native backends
   - Expected: textual_llvm does not contain `self.unsigned_locals[dest_id] = self.unsigned_locals.get(src_id) ?? false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps unsigned casts and ordered comparisons aligned across native backends")
val textual_llvm = read_mir_source("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl")
val llvm_module = read_mir_source("src/compiler/70.backend/backend/llvm_lib_translate.spl")
val llvm_api = read_mir_source("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl")
val cranelift = read_mir_source("src/compiler/70.backend/backend/cranelift_codegen_adapter.spl")
val legacy_cranelift = read_mir_source("src/compiler/70.backend/codegen.spl")
val parity = read_mir_source("scripts/check/check-native-seed-parity.shs")

expect(textual_llvm).to_contain("if src_unsigned and cast_inst == \"sitofp\":")
expect(textual_llvm).to_contain("cast_inst = \"uitofp\"")
expect(textual_llvm).to_contain("if not self.unsigned_locals.has(self.local_id_value(dest)):")
expect(textual_llvm).to_contain("if self.unsigned_locals.has(self.local_id_value(src)):")
expect(textual_llvm).to_contain("self.unsigned_locals[self.local_id_value(dest)] = self.unsigned_locals[self.local_id_value(src)]")
expect(textual_llvm.contains("self.unsigned_locals[dest_id] = self.unsigned_locals.get(src_id) ?? false")).to_equal(false)
expect(llvm_module).to_contain("var local_unsigned: {i64: bool} = {}")
expect(llvm_module).to_contain("local_types, local_unsigned, block_map, func_map")
expect(llvm_api).to_contain("val source_unsigned = get_operand_unsigned(operand, local_unsigned)")
expect(llvm_api).to_contain("coerce_llvm_cast_value(builder, op_val, target_ty, source_unsigned)")
expect(llvm_api).to_contain("val is_unsigned = left_is_unsigned or get_operand_unsigned(right, local_unsigned)")
expect(llvm_api).to_contain("llvm_build_ui_to_fp(builder, value, target_ty, \"coerce\")")
expect(llvm_api).to_contain("llvm_build_icmp(builder, LLVM_INT_ULT, lhs, rhs, \"lt\")")
expect(llvm_api).to_contain("llvm_build_icmp(builder, LLVM_INT_ULE, lhs, rhs, \"le\")")
expect(llvm_api).to_contain("llvm_build_icmp(builder, LLVM_INT_UGT, lhs, rhs, \"gt\")")
expect(llvm_api).to_contain("llvm_build_icmp(builder, LLVM_INT_UGE, lhs, rhs, \"ge\")")
expect(cranelift).to_contain("case U8 | U16 | U32 | U64: cranelift_fcvt_from_uint(ctx, to_cl, src_val)")
expect(cranelift).to_contain("elif is_unsigned: cranelift_icmp(ctx, CL_CMP_ULT, a, b)")
expect(cranelift).to_contain("elif is_unsigned: cranelift_icmp(ctx, CL_CMP_ULE, a, b)")
expect(cranelift).to_contain("elif is_unsigned: cranelift_icmp(ctx, CL_CMP_UGT, a, b)")
expect(cranelift).to_contain("elif is_unsigned: cranelift_icmp(ctx, CL_CMP_UGE, a, b)")
expect(legacy_cranelift).to_contain("if unsigned: CL_CMP_ULT else: CL_CMP_SLT")
expect(legacy_cranelift).to_contain("if unsigned: CL_CMP_ULE else: CL_CMP_SLE")
expect(legacy_cranelift).to_contain("if unsigned: CL_CMP_UGT else: CL_CMP_SGT")
expect(legacy_cranelift).to_contain("if unsigned: CL_CMP_UGE else: CL_CMP_SGE")
expect(parity).to_contain("run_strict_dual_backend_case mixed_numeric_comparison write_case_mixed_numeric_comparison")
expect(parity).to_contain("run_strict_dual_backend_case mixed_unsigned_float_comparison write_case_mixed_unsigned_float_comparison")
expect(parity).to_contain("run_strict_dual_backend_case mixed_signed_unsigned_ordering write_case_mixed_signed_unsigned_ordering")

val llvm_wrapper_paths: [text] = [
    "src/lib/nogc_sync_mut/sffi/llvm_codegen.spl",
    "src/lib/nogc_async_mut/sffi/llvm_codegen.spl",
    "src/lib/nogc_sync_mut/ffi/llvm_codegen.spl",
]
for path in llvm_wrapper_paths:
    val wrapper = read_mir_source(path)
    expect(wrapper).to_contain("fn llvm_build_ui_to_fp(b: i64, value: i64, dest_ty: i64, name: text) -> i64:")
    expect(wrapper).to_contain("_lc4(\"LLVMBuildUIToFP\", b, value, dest_ty, name.ptr())")

val llvm_facade_paths: [text] = [
    "src/lib/nogc_sync_mut/sffi/llvm.spl",
    "src/lib/nogc_async_mut/sffi/llvm.spl",
    "src/lib/nogc_sync_mut/ffi/llvm.spl",
]
for path in llvm_facade_paths:
    expect(read_mir_source(path)).to_contain("llvm_build_si_to_fp, llvm_build_ui_to_fp, llvm_build_fp_to_si")

val llvm_export_paths: [text] = [
    "src/lib/nogc_sync_mut/sffi/__init__.spl",
    "src/lib/nogc_async_mut/sffi/__init__.spl",
    "src/lib/nogc_sync_mut/ffi/__init__.spl",
]
for path in llvm_export_paths:
    expect(read_mir_source(path)).to_contain("export llvm_build_si_to_fp, llvm_build_ui_to_fp, llvm_build_fp_to_si")
```

</details>

#### keeps module-qualified named types canonical through MIR lowering

- keeps module-qualified named types canonical through MIR lowering


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps module-qualified named types canonical through MIR lowering")
val state = read_mir_source("src/compiler/50.mir/mir_lowering_types.spl")
val module = read_mir_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")
val function = read_mir_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val calls = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
val methods = read_mir_source("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")

expect(state).to_contain("canonical_type_symbols: Dict<text, i64>")
expect(module).to_contain("self.symbols = module.symbols")
expect(module).to_contain("self.symbols.get_symbol_raw(symbol.id)")
expect(module.contains("self.symbols.get_symbol(symbol)")).to_be(false)
expect(module).to_contain("case Some(info):\n                if info == nil: return symbol\n                val defining_module")
expect(module).to_contain("val key = \"{defining_module}.{info.name}\"")
expect(function).to_contain("self.canonical_mir_type_symbol(symbol)")
expect(calls).to_contain("self.canonical_mir_type_symbol(nested_symbol)")
expect(methods).to_contain("self.canonical_mir_type_symbol(")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_lowering_new_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Mir Lowering New.
- Mir Lowering New

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d506c3f68ed2dbf5fbfd77adfa6f58044bae6f4a7cce318734c104a63b14a0c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d506c3f68ed2dbf5fbfd77adfa6f58044bae6f4a7cce318734c104a63b14a0c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d506c3f68ed2dbf5fbfd77adfa6f58044bae6f4a7cce318734c104a63b14a0c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/mir_lowering_new_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_lowering_new_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/mir_lowering_new_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_lowering_new_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_lowering_new_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/mir_lowering_new_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/mir_lowering_new_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/mir_lowering_new_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps MirLowering state shape available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_lowering_new_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps MirLowering constructor wired to HIR symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_lowering_new_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets method lookup state at every module boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
