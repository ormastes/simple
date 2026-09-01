# riscv_scalar_binding_spec

> Purpose: Prove that RISC-V scalar HWIR resource-binding plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# riscv_scalar_binding_spec

Purpose: Prove that RISC-V scalar HWIR resource-binding plan.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that RISC-V scalar HWIR resource-binding plan.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### RISC-V scalar HWIR resource-binding plan

#### binds Zmmul multiply rows without materializing divide resources

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds Zmmul multiply rows without materializing divide resources
- Verify: binds Zmmul multiply rows without materializing divide resources
   - Expected: plan.diagnostic() equals ``
   - Expected: plan.multiply_operation_count equals `5`
   - Expected: plan.divide_operation_count equals `0`
   - Expected: plan.bindings.len() equals `5`
   - Expected: binding.resource_kind equals `multiply_dsp`
   - Expected: binding.sharing_group equals `multiply_dsp_shared`
   - Expected: binding.latency_contract equals `uncommitted`
   - Expected: binding.latency_cycles equals `-1`
   - Expected: binding.latency_is_committed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds Zmmul multiply rows without materializing divide resources")
step("Verify: binds Zmmul multiply rows without materializing divide resources")
# @req: REQ-COMP-RISC-V-SCALAR-HWIR-RESOURCE-BINDING-PLAN-001
val selection = riscv_scalar_elaborate_provider("rv64i_zmmul", "dsp").unwrap()
val plan = hwir_riscv_scalar_binding_plan(selection, "area").unwrap()
expect(plan.diagnostic()).to_equal("")
expect(plan.multiply_operation_count).to_equal(5)
expect(plan.divide_operation_count).to_equal(0)
expect(plan.bindings.len()).to_equal(5)
for binding in plan.bindings:
    expect(binding.resource_kind).to_equal("multiply_dsp")
    expect(binding.sharing_group).to_equal("multiply_dsp_shared")
    expect(binding.latency_contract).to_equal("uncommitted")
    expect(binding.latency_cycles).to_equal(-1)
    expect(binding.latency_is_committed()).to_equal(false)
```

</details>

#### binds full M divide and remainder rows only under its fixed provider

- binds full M divide and remainder rows only under its fixed provider
- Verify: binds full M divide and remainder rows only under its fixed provider
   - Expected: plan.multiply_operation_count equals `5`
   - Expected: plan.divide_operation_count equals `8`
   - Expected: plan.bindings.len() equals `13`
   - Expected: binding.latency_contract equals `uncommitted`
   - Expected: binding.latency_cycles equals `-1`
   - Expected: has_divw is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds full M divide and remainder rows only under its fixed provider")
step("Verify: binds full M divide and remainder rows only under its fixed provider")
val selection = riscv_scalar_elaborate_provider("rv64im", "iterative").unwrap()
val plan = hwir_riscv_scalar_binding_plan(selection, "balanced").unwrap()
expect(plan.multiply_operation_count).to_equal(5)
expect(plan.divide_operation_count).to_equal(8)
expect(plan.bindings.len()).to_equal(13)
var has_divw = false
for binding in plan.bindings:
    if binding.resource_id == "rv64.m.divw" and binding.resource_kind == "divide_iterative":
        has_divw = true
    expect(binding.latency_contract).to_equal("uncommitted")
    expect(binding.latency_cycles).to_equal(-1)
expect(has_divw).to_equal(true)
```

</details>

#### rejects an unknown target profile before any binding exists

- rejects an unknown target profile before any binding exists
- Verify: rejects an unknown target profile before any binding exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an unknown target profile before any binding exists")
step("Verify: rejects an unknown target profile before any binding exists")
val selection = riscv_scalar_elaborate_provider("rv32i_zmmul", "pipelined").unwrap()
expect(hwir_riscv_scalar_binding_plan(selection, "runtime").unwrap_err()).to_equal(
    "HWIR-E-RISCV-BINDING-PROFILE: scalar binding requires area, balanced, or speed target profile")
```

</details>

#### rejects an estimated latency in the critical scalar binding boundary

- rejects an estimated latency in the critical scalar binding boundary
- Verify: rejects an estimated latency in the critical scalar binding boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an estimated latency in the critical scalar binding boundary")
step("Verify: rejects an estimated latency in the critical scalar binding boundary")
val forged = HwirRiscvScalarBindingPlan(isa_profile: "rv32i_zmmul", xlen: 32,
    target_profile: "speed", bindings: [HwResourceBinding(resource_id: "rv32.m.mul",
    resource_kind: "multiply_pipelined", profile: "speed", sharing_group: "",
    latency_cycles: 1, latency_contract: "estimated")],
    multiply_operation_count: 1, divide_operation_count: 0)
expect(forged.diagnostic()).to_equal(
    "HWIR-E-RISCV-BINDING-IDENTITY: scalar bindings require unique ISA IDs and one target profile")
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
- `REQ-COMP-RISC-V-SCALAR-HWIR-RESOURCE-BINDING-PLAN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e1e76266180491d5aa977fc060151b274d624bba7b17a76895f5b4d40a79b277`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1e76266180491d5aa977fc060151b274d624bba7b17a76895f5b4d40a79b277`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1e76266180491d5aa977fc060151b274d624bba7b17a76895f5b4d40a79b277`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.spl
mirror: doc/06_spec/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds Zmmul multiply rows without materializing divide resources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds full M divide and remainder rows only under its fixed provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/60.mir_opt/riscv_scalar_binding_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown target profile before any binding exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
