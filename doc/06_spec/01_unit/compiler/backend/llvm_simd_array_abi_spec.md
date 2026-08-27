# Contract spec: test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl` and a green Results line.

## Scenarios

### LLVM SIMD row array ABI

#### uses the runtime array ABI for packed pixel rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the runtime array ABI for packed pixel rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the runtime array ABI for packed pixel rows")
val aggregate = file_read("src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl")
val declarations = file_read("src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl")
expect(aggregate).to_contain("call ptr @rt_array_new")
expect(aggregate).to_contain("call i8 @rt_array_push")
expect(declarations).to_contain("declare ptr @rt_engine2d_simd_fill_row_u32(i64, i64)")
expect(declarations).to_contain("declare ptr @rt_engine2d_simd_fill_rows_u32(i64, i64, i64, i64)")
expect(declarations).to_contain("declare ptr @rt_engine2d_simd_copy_row_u32(ptr)")
expect(declarations).to_contain("declare ptr @rt_engine2d_simd_blend_row_u32(ptr, ptr)")
expect(declarations).to_contain("declare i64 @rt_engine2d_simd_row_probe()")
val calls = file_read("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")
expect(calls).to_contain("name == \"rt_engine2d_simd_row_probe\"")
expect(declarations).to_contain("declare i64 @rt_simd_engine2d_neon_hits()")
```

</details>

#### keeps the public Simple wrapper narrow and typed

- keeps the public Simple wrapper narrow and typed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the public Simple wrapper narrow and typed")
val rows = file_read("src/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows.spl")
expect(rows).to_contain("engine2d_simd_fill_row_u32(count: i64, color: u32) -> [u32]")
expect(rows).to_contain("engine2d_simd_copy_row_u32(src: [u32]) -> [u32]")
expect(rows).to_contain("engine2d_simd_blend_row_u32(dst_row: [u32], src_row: [u32]) -> [u32]")
```

</details>

#### selects hosted cross compilers without entering the SimpleOS RV64 path

- selects hosted cross compilers without entering the SimpleOS RV64 path


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects hosted cross compilers without entering the SimpleOS RV64 path")
val runtime = file_read("src/compiler/70.backend/backend/runtime_compiler.spl")
val adapter = file_read("src/compiler/70.backend/backend/llvm_codegen_adapter.spl")
val builder = file_read("src/compiler/70.backend/backend/llvm_ir_builder.spl")
val core = file_read("src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl")
val backend_types = file_read("src/compiler/70.backend/backend/backend_types.spl")
val codegen_types = file_read("src/compiler/70.backend/backend/codegen_types.spl")
val linker_helpers = file_read("src/compiler/70.backend/linker/linker_wrapper_helpers.spl")
val native_runtime = file_read("src/runtime/runtime_native.c")
val native_link = compiler_native_link_source()
val cc_link = file_read("src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl")
expect(runtime).to_contain("target.starts_with(\"aarch64-\")")
expect(runtime).to_contain("target == \"host\" and host_arch() == \"aarch64\"")
expect(runtime).to_contain("comp_args.push(\"-mno-outline-atomics\")")
expect(runtime).to_contain("target.starts_with(\"riscv64-\")")
expect(runtime).to_contain("SIMPLE_RUNTIME_RISCV64_VECTOR")
expect(runtime).to_contain("target.starts_with(\"riscv64\")")
expect(runtime).to_contain("comp_args.push(\"-march=rv64gcv\")")
expect(native_link).to_contain("target == \"riscv64-unknown-none\"")
expect(native_link).to_contain("obj.contains(\"simpleos_riscv64\")")
expect(native_link).to_not_contain("obj.contains(\"riscv64\")")        expect(cc_link).to_contain("val hosted_cross = target.starts_with(\"aarch64-\") or target.starts_with(\"riscv64-\")")
expect(cc_link).to_contain("if not hosted_cross:")
expect(cc_link).to_contain("process_run(cc, args)")
expect(adapter).to_contain("fn llvm_direct_target() -> CodegenTarget:")
expect(adapter).to_contain("LlvmTargetConfig.for_target_portable_numeric(target, nil)")
expect(adapter).to_contain("MirToLlvm.create(module.name, target, nil)")
expect(builder).to_contain("val target = LlvmTargetTriple.from_target(llvm_builder_target())")
expect(builder).to_not_contain("self.target.datalayout()")        expect(core).to_contain("fn local_id_value(local: LocalId) -> i64:\n        local.id")
expect(core).to_contain("fn block_id_value(block: BlockId) -> i64:\n        block.id")
expect(backend_types).to_contain("object_code: [u8]?")
expect(codegen_types).to_contain("object_code: if self.has_object_code: Some(self.object_code) else: nil")
expect(linker_helpers).to_contain("fn write_elf_bytes_to_file(path: text, bytes: [u8])")
expect(native_runtime).to_contain("int64_t rt_file_read_bytes(const uint8_t* path_ptr, uint64_t path_len)")
expect(native_runtime).to_contain("int rt_file_write_bytes(const uint8_t* path_ptr, uint64_t path_len, const uint8_t* data, uint64_t len)")
expect(core).to_contain("val const_disc = rt_enum_discriminant(MirInstKind.Const(")
expect(core).to_contain("val dest: LocalId = rt_tuple_get(payload, 0)")
expect(core).to_not_contain("case MirInstKind.Const(dest, value, ty):")        expect(core).to_not_contain("case Const(dest, _, _) | Copy(dest, _)")        expect(core).to_contain("self.defined_locals[dest_id] = true")
expect(core).to_not_contain("self.ptr_locals.has(id)")        expect(core).to_not_contain("self.bool_locals.has(id)")
```

</details>

#### tracks an exact native-hit probe for every hosted architecture

- tracks an exact native-hit probe for every hosted architecture


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks an exact native-hit probe for every hosted architecture")
val probe = file_read("test/fixtures/compiler/llvm_simd_row_native_probe.spl")
expect(probe).to_contain("rt_engine2d_simd_row_probe()")
val runtime = file_read("src/runtime/runtime_simd_dispatch.c")
expect(runtime).to_contain("rt_engine2d_simd_fill_row_u32(8, color)")
expect(runtime).to_contain("rt_engine2d_simd_copy_row_u32(fill)")
expect(runtime).to_contain("rt_array_get(copy, 3)")
expect(runtime).to_contain("if (rt_simd_engine2d_neon_hits() < 2) abort()")
val wrapper = file_read("scripts/check/check-llvm-simd-row-native-arch.shs")
expect(wrapper).to_contain("vsetvli")
expect(wrapper).to_contain("vse64")
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `561d58c8f3077ac50b1304aa6a16c5c456bf85106d7da4db31ee55d964d5c346`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `561d58c8f3077ac50b1304aa6a16c5c456bf85106d7da4db31ee55d964d5c346`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `561d58c8f3077ac50b1304aa6a16c5c456bf85106d7da4db31ee55d964d5c346`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_simd_array_abi_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the runtime array ABI for packed pixel rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the public Simple wrapper narrow and typed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_simd_array_abi_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects hosted cross compilers without entering the SimpleOS RV64 path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
