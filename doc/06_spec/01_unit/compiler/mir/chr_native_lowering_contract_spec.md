# Chr Native Lowering Contract Specification

> Tests covering native chr lowering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chr Native Lowering Contract Specification

## Scenarios

### native chr lowering

#### routes integer chr through the canonical Unicode runtime ABI

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes integer chr through the canonical Unicode runtime ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes integer chr through the canonical Unicode runtime ABI")
val lowering = file_read("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
expect(lowering).to_contain("(method == \"chr\" or method == \"to_char\") and args.len() == 0")
expect(lowering).to_contain("MirConstValue.Str(\"rt_char_from_code\")")
expect(lowering).to_contain("MirTypeKind.I8 | MirTypeKind.I16 | MirTypeKind.I32 | MirTypeKind.I64 | MirTypeKind.U8 | MirTypeKind.U16 | MirTypeKind.U32 | MirTypeKind.U64")
expect(lowering).to_contain("self.local_mir_type_of(prelowered_method_receiver) ?? chr_runtime_type")
expect(lowering.contains("if val chr_runtime_type = self.local_mir_type_of(prelowered_method_receiver)")).to_be(false)
expect(lowering).to_contain("case Unresolved: resolution_is_unresolved = true")
expect(lowering).to_contain("val chr_primitive_resolution_allowed = resolution_is_unresolved or resolution_is_free_function")
expect(lowering.contains("case Unresolved | FreeFunction(_): true")).to_be(false)
expect(lowering).to_contain("val chr_receiver_type = self.receiver_declared_type(receiver)")
expect(lowering).to_contain("self.struct_value_syms[prelowered_method_receiver.id] = declared_chr_owner")
expect(lowering).to_contain("if chr_method_shape and chr_primitive_resolution_allowed:")
expect(lowering).to_contain("if chr_method_shape and chr_has_custom_owner and free_owner != nil and free_owner != \"\":")
expect(lowering).to_contain("selected_func_id = self.struct_method_syms[owner_method_key]")
expect(lowering).to_contain("chr_primitive_resolution_allowed and not chr_has_custom_owner")
expect(lowering).to_contain("self.local_hir_type_is_int(prelowered_method_receiver)")
expect(lowering).to_contain("(chr_receiver_is_declared_int or chr_receiver_is_runtime_int or chr_receiver_is_local_int)")
expect(lowering.contains("resolution_is_unresolved and chr_receiver_needs_runtime_probe")).to_be(false)
expect(lowering).to_contain("emit_call(chr_op, [mir_operand_copy(chr_receiver)], MirType.i64())")
expect(lowering).to_contain("val chr_text_type = self.bootstrap_text_type()")
expect(lowering).to_contain("val chr_text = b_chr_typed.new_temp(chr_text_type)")
expect(lowering).to_contain("self.mark_runtime_value_local(chr_text.id)")
expect(lowering).to_contain("self.remember_local_hir_type(chr_text.id, HirType(kind: HirTypeKind.Str, span: receiver.span), 2, 0)")
expect(lowering).to_contain("if len_symbol == \"rt_len\" and not self.runtime_array_locals.contains(receiver_local.id)")
expect(lowering).to_contain("len_symbol = \"rt_string_len\"")
expect(lowering).to_contain("(self.is_runtime_value_local(value_local.id) or self.is_tagged_text_local(value_local.id)) and self.local_is_str(value_local)")
expect(lowering.contains("decode_runtime_value(chr_local, chr_text_type)")).to_be(false)
expect(lowering.contains("return_type: chr_text_type")).to_be(false)
expect(lowering.contains("MirConstValue.Str(\"text_dot_from_char_code\")")).to_be(false)
```

</details>

#### keeps pure and hosted runtimes on the raw-i64 Unicode ABI

- keeps pure and hosted runtimes on the raw-i64 Unicode ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps pure and hosted runtimes on the raw-i64 Unicode ABI")
val pure_runtime = file_read("src/runtime/simple_core/core_string.spl")
val hosted_runtime = file_read("src/runtime/runtime_native.c")
val hosted_header = file_read("src/runtime/runtime.h")

expect(pure_runtime).to_contain("pub fn rt_char_from_code(code: i64) -> i64:")
expect(pure_runtime).to_contain("code < 0 or code > 1114111 or (code >= 55296 and code <= 57343)")
expect(pure_runtime).to_contain("if value > 65535:")
expect(pure_runtime).to_contain("return strlen(value)")
expect(hosted_runtime).to_contain("int64_t rt_char_from_code(int64_t code)")
expect(hosted_runtime).to_contain("int64_t text_dot_from_char_code(int64_t code)")
expect(hosted_runtime).to_contain("return rt_char_from_code(code);")
expect(hosted_runtime).to_contain("code < 0 || code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)")
expect(hosted_runtime).to_contain("string >= 0x10000 ? (int64_t)strlen")
expect(hosted_header).to_contain("int64_t  rt_char_from_code(int64_t code);")
expect(hosted_header).to_contain("int64_t  text_dot_from_char_code(int64_t code);")
```

</details>

#### keeps the Rust seed on its existing Unicode helper until migration

- keeps the Rust seed on its existing Unicode helper until migration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the Rust seed on its existing Unicode helper until migration")
val rust_calls = file_read("src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs")
expect(rust_calls).to_contain("if matches!(method, \"chr\" | \"to_char\") && !args.is_empty()")
expect(rust_calls).to_contain("get_function(\"text_dot_from_char_code\")")
```

</details>

#### keeps invalid seed chr results aligned with canonical Simple

- keeps invalid seed chr results aligned with canonical Simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps invalid seed chr results aligned with canonical Simple")
val seed = file_read("src/compiler_rust/compiler/src/interpreter_method/primitives.rs")
val cross = file_read("test/fixtures/native_crossmodule_result_u8/main.spl")
expect(seed).to_contain("if !(0..=0x10FFFF).contains(&n)")
expect(seed).to_contain("None => Value::text(String::new())")
expect(seed.contains("chr() argument out of range")).to_be(false)
expect(seed.contains("invalid Unicode code point")).to_be(false)
expect(cross).to_contain("negative.chr().len() == 0 and surrogate.chr().len() == 0 and above_max.to_char().len() == 0")
```

</details>

#### keeps default struct layout metadata as an explicit desugared pair

- keeps default struct layout metadata as an explicit desugared pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps default struct layout metadata as an explicit desugared pair")
val hir_lowering = file_read("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
expect(hir_lowering).to_contain("val has_layout = layout.layout_kind != TypeLayoutKind.Simple or layout.has_explicit_align or layout.is_packed")
expect(hir_lowering).to_contain("has_layout_attr: has_layout")
expect(hir_lowering).to_contain("layout_attr: layout")
expect(hir_lowering.contains("val layout_opt: LayoutAttr?")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/chr_native_lowering_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native chr lowering.
- native chr lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eb49cee6af716fc11e76fa3d571bf198739304d71c2aa0c45c30501a2b553c0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb49cee6af716fc11e76fa3d571bf198739304d71c2aa0c45c30501a2b553c0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb49cee6af716fc11e76fa3d571bf198739304d71c2aa0c45c30501a2b553c0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/chr_native_lowering_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/chr_native_lowering_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/chr_native_lowering_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/chr_native_lowering_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/chr_native_lowering_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes integer chr through the canonical Unicode runtime ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/chr_native_lowering_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps pure and hosted runtimes on the raw-i64 Unicode ABI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/chr_native_lowering_contract_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the Rust seed on its existing Unicode helper until migration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
