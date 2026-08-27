# vulkan_jit_step_budget_loop_lowering_spec

> Asserts that lowering a `while true` loop body to SPIR-V injects a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_jit_step_budget_loop_lowering_spec

Asserts that lowering a `while true` loop body to SPIR-V injects a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Asserts that lowering a `while true` loop body to SPIR-V injects a
    step-budget decrement (OpLoad, OpISub by 1, OpStore) and an
    exhaustion check (OpIEqual against zero) -- the exact instruction
    sequence design §6.3 requires so an emitted loop can never actually
    run unbounded on the device.

## Scenarios

### vulkan_jit lane -- step-budget decrement/exhaustion-check emission (design §6.3)

#### emits OpLoad -> OpISub -> OpStore -> OpIEqual for the budget word, in that order

- emits OpLoad -> OpISub -> OpStore -> OpIEqual for the budget word, in that order
- Build a minimal SPIR-V module and inject the budget-decrement sequence
- Assert the generated assembly contains the decrement+check sequence in order
- Assert the decrement subtracts exactly 1 (a fresh OpConstant ... 1 feeds OpISub)


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits OpLoad -> OpISub -> OpStore -> OpIEqual for the budget word, in that order")
step("Build a minimal SPIR-V module and inject the budget-decrement sequence")
var b = SpirvBuilder.create([1, 0])
val void_t = b.emit_type_void()
val fn_t = b.emit_type_function(void_t, [])
val uint_t = b.emit_type_int(32, false)
val bool_t = b.emit_type_bool()
val budget_ptr_t = b.emit_type_pointer("Function", uint_t)
val budget_ptr = b.emit_variable(budget_ptr_t, "Function")
val _main_id = b.emit_function(void_t, fn_t, "None")
val _entry = b.emit_label()

val ids = emit_step_budget_decrement_check(b, uint_t, bool_t, budget_ptr)
b.emit_return()
b.emit_function_end()

step("Assert the generated assembly contains the decrement+check sequence in order")
val asm = b.build()
val load_idx = asm.find("OpLoad")
val isub_idx = asm.find("OpISub")
val store_idx = asm.find("OpStore")
val iequal_idx = asm.find("OpIEqual")

assert_true(load_idx >= 0)
assert_true(isub_idx >= 0)
assert_true(store_idx >= 0)
assert_true(iequal_idx >= 0)
assert_true(load_idx < isub_idx)
assert_true(isub_idx < store_idx)
assert_true(store_idx < iequal_idx)

step("Assert the decrement subtracts exactly 1 (a fresh OpConstant ... 1 feeds OpISub)")
assert_true(asm.contains("= OpConstant %{uint_t} 1"))
```

</details>

#### the exhaustion check compares the decremented budget against zero, not the pre-decrement value

- the exhaustion check compares the decremented budget against zero, not the pre-decrement value
- The OpIEqual operands must reference the post-decrement id, not the loaded id


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the exhaustion check compares the decremented budget against zero, not the pre-decrement value")
var b = SpirvBuilder.create([1, 0])
val uint_t = b.emit_type_int(32, false)
val bool_t = b.emit_type_bool()
val budget_ptr_t = b.emit_type_pointer("Function", uint_t)
val budget_ptr = b.emit_variable(budget_ptr_t, "Function")

val ids = emit_step_budget_decrement_check(b, uint_t, bool_t, budget_ptr)

val asm = b.build()
val iequal_line_start = asm.find("OpIEqual")
val decremented_ref = "%{ids.decremented_budget}"
step("The OpIEqual operands must reference the post-decrement id, not the loaded id")
assert_true(iequal_line_start >= 0)
val tail = asm[iequal_line_start:asm.len()]
assert_true(tail.contains(decremented_ref))
```

</details>

### vulkan_jit lane -- while-true loop kernel wires the budget check into real control flow (design §6.3)

<details>
<summary>Advanced: contains the budget-decrement sequence AND a conditional branch out of the loop</summary>

#### contains the budget-decrement sequence AND a conditional branch out of the loop

- contains the budget-decrement sequence AND a conditional branch out of the loop
- Budget-decrement sequence present
- Conditional branch-out (never an unconditional OpBranch back into the loop alone)
- The GMB-1 timeout sentinel 0xDEAD0000 is written on the exhausted path


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("contains the budget-decrement sequence AND a conditional branch out of the loop")
val asm = build_while_true_budget_loop_spirv()

step("Budget-decrement sequence present")
assert_true(asm.contains("OpLoad"))
assert_true(asm.contains("OpISub"))
assert_true(asm.contains("OpIEqual"))

step("Conditional branch-out (never an unconditional OpBranch back into the loop alone)")
assert_true(asm.contains("OpBranchConditional"))
assert_true(asm.contains("OpSelectionMerge"))

step("The GMB-1 timeout sentinel 0xDEAD0000 is written on the exhausted path")
assert_true(asm.contains("3735097344"))
```

</details>


</details>

#### assembles cleanly with spirv-as when the tool is present on this host (host-aware optional)

- assembles cleanly with spirv-as when the tool is present on this host (host-aware optional)
- Probe for spirv-as; SKIP the assembly check (not the sequence assertions above) if absent
- skip: spirv-as not found on this host
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assembles cleanly with spirv-as when the tool is present on this host (host-aware optional)")
step("Probe for spirv-as; SKIP the assembly check (not the sequence assertions above) if absent")
val has_tool = shell("command -v spirv-as >/dev/null 2>&1").exit_code == 0
if not has_tool:
    step("skip: spirv-as not found on this host")
    assert_true(true)
else:
    val asm = build_while_true_budget_loop_spirv()
    val asm_path = "build/tmp/vulkan_jit_step_budget_loop_unit_spec.spvasm"
    val bin_path = "build/tmp/vulkan_jit_step_budget_loop_unit_spec.spv"
    assert_true(file_write(asm_path, asm))
    val (stdout, stderr, exit_code) = process_run_bounded(
        "spirv-as", [asm_path, "-o", bin_path], 30000, 65536)
    expect(exit_code).to_equal(0)
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

- Canonical SPipe generation for source `9d9058756a04ae0384fcf641646c5fd1a79d41a9ac1c75ef4af6d2202c05b3dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d9058756a04ae0384fcf641646c5fd1a79d41a9ac1c75ef4af6d2202c05b3dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d9058756a04ae0384fcf641646c5fd1a79d41a9ac1c75ef4af6d2202c05b3dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits OpLoad -> OpISub -> OpStore -> OpIEqual for the budget word, in that order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the exhaustion check compares the decremented budget against zero, not the pre-decrement value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains the budget-decrement sequence AND a conditional branch out of the loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
