# typed_u8_index_lowering_contract_spec

> Executable MIR contract for layout-neutral checked `[u8]` indexed reads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# typed_u8_index_lowering_contract_spec

Executable MIR contract for layout-neutral checked `[u8]` indexed reads.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executable MIR contract for layout-neutral checked `[u8]` indexed reads.

## Scenarios

### typed u8 indexed-load MIR ownership

#### uses one checked layout-neutral byte read without generic tag decoding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses one checked layout-neutral byte read without generic tag decoding
   - Expected: _direct_call_count(module, "byte_at", "rt_bytes_u8_at") equals `1`
   - Expected: _direct_call_count(module, "byte_at", "rt_array_get") equals `0`
   - Expected: _intrinsic_count(module, "byte_at", "bounds_check") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses one checked layout-neutral byte read without generic tag decoding")
val module = _lower_u8_index_source()
expect(_direct_call_count(module, "byte_at", "rt_bytes_u8_at")).to_equal(1)
expect(_direct_call_count(module, "byte_at", "rt_array_get")).to_equal(0)
expect(_intrinsic_count(module, "byte_at", "bounds_check")).to_equal(0)
```

</details>

#### does not specialize wider element arrays

- does not specialize wider element arrays
   - Expected: _direct_call_count(module, "word_at", "rt_bytes_u8_at") equals `0`
   - Expected: _direct_call_count(module, "word_at", "rt_array_get") equals `1`
   - Expected: _intrinsic_count(module, "word_at", "bounds_check") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not specialize wider element arrays")
val module = _lower_u8_index_source()
expect(_direct_call_count(module, "word_at", "rt_bytes_u8_at")).to_equal(0)
expect(_direct_call_count(module, "word_at", "rt_array_get")).to_equal(1)
expect(_intrinsic_count(module, "word_at", "bounds_check")).to_equal(1)
```

</details>

#### registers the exact runtime ABI and reserves the synthesized name

- registers the exact runtime ABI and reserves the synthesized name


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers the exact runtime ABI and reserves the synthesized name")
val llvm_lib = file_read("src/compiler/70.backend/backend/llvm_lib_translate.spl")
val llvm_owner = file_read("src/compiler/50.mir/mir_call_ownership.spl")
val cranelift = file_read("src/compiler/70.backend/backend/cranelift_codegen_adapter.spl")
val llvm_text = file_read("src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl")
val wasm = file_read("src/compiler/70.backend/backend/wasm/wasm_runtime.spl")
expect(llvm_lib).to_contain(
    'declare_fn(mod_, "rt_bytes_u8_at", llvm_function_type(i64_ty, [ptr_ty, i64_ty], false))')
expect(llvm_text).to_contain('declare i64 @rt_bytes_u8_at(ptr, i64)')
expect(llvm_text).to_contain(
    'self.remember_function_param_types("rt_bytes_u8_at", ["ptr", "i64"])')
expect(llvm_owner).to_contain('name == "rt_bytes_u8_at"')
expect(cranelift).to_contain('name == "rt_bytes_u8_at"')
expect(wasm).to_contain(
    '(import \\"simple\\" \\"rt_bytes_u8_at\\" (func $rt_bytes_u8_at (param i32 i32) (result i32)))')
```

</details>

#### keeps the byte result raw and never routes it through generic decode

- keeps the byte result raw and never routes it through generic decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the byte result raw and never routes it through generic decode")
val source = file_read("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val byte_arm = source.split("if typed_u8_runtime_read:")[1].split(
    "# Bug s54/s54c/s54d:")[0]
expect(byte_arm).to_contain("emit_cast(mir_operand_copy(getter_local), result_type)")
expect(byte_arm.contains("decode_runtime_value")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `edb3eb4eb579e2b0ffb422a4c8b281e8db112c9cb37a898d9858d0b3b14ccf37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edb3eb4eb579e2b0ffb422a4c8b281e8db112c9cb37a898d9858d0b3b14ccf37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edb3eb4eb579e2b0ffb422a4c8b281e8db112c9cb37a898d9858d0b3b14ccf37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one checked layout-neutral byte read without generic tag decoding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not specialize wider element arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/typed_u8_index_lowering_contract_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the exact runtime ABI and reserves the synthesized name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
