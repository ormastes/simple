# Hwir Aspect Manifest Specification

> Tests covering typed Gen2 hardware aspect manifests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Aspect Manifest Specification

## Scenarios

### typed Gen2 hardware aspect manifests

#### should keep a disabled aspect plan structurally zero-cost

- should keep a disabled aspect plan structurally zero-cost
- Construct the canonical absent plan without manifests or applications
   - Expected: plan.is_absent() is true
   - Expected: plan.diagnostic() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should keep a disabled aspect plan structurally zero-cost")
step("Construct the canonical absent plan without manifests or applications")
val plan = hwir_aspect_plan_absent()
expect(plan.is_absent()).to_equal(true)
expect(plan.diagnostic()).to_equal("")
```

</details>

#### should admit a required observational aspect only with a semantic HWIR match

- should admit a required observational aspect only with a semantic HWIR match
- Bind the required manifest to the stable typed commit node
   - Expected: plan.diagnostic() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should admit a required observational aspect only with a semantic HWIR match")
step("Bind the required manifest to the stable typed commit node")
val manifest = aspect_manifest("debug.rvfi", true, [])
val plan = HwAspectPlan(manifests: [manifest], applications: [
    HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [HwNodeId.module_root("commit")], woven_node_count: 1)
])
expect(plan.diagnostic()).to_equal("")
```

</details>

#### should fail closed for missing, zero-match, or conflicting aspect plans

- should fail closed for missing, zero-match, or conflicting aspect plans
- Validate required applications and mutually conflicting manifest declarations
   - Expected: missing.diagnostic() equals `HWIR-E-ASPECT-REQUIRED: required hardware aspect did not produce an application`
   - Expected: zero_match.diagnostic() equals `HWIR-E-ASPECT-NO-MATCH: required hardware aspect did not weave a matched sema... (full value in folded executable source)`
   - Expected: zero_woven.diagnostic() equals `HWIR-E-ASPECT-NO-MATCH: required hardware aspect did not weave a matched sema... (full value in folded executable source)`
   - Expected: conflict.diagnostic() equals `HWIR-E-ASPECT-CONFLICT: conflicting hardware aspects cannot share one plan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed for missing, zero-match, or conflicting aspect plans")
step("Validate required applications and mutually conflicting manifest declarations")
val missing = HwAspectPlan(manifests: [aspect_manifest("debug.rvfi", true, [])], applications: [])
expect(missing.diagnostic()).to_equal("HWIR-E-ASPECT-REQUIRED: required hardware aspect did not produce an application")
val zero_match = HwAspectPlan(manifests: [aspect_manifest("debug.rvfi", true, [])], applications: [
    HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [], woven_node_count: 0)
])
expect(zero_match.diagnostic()).to_equal("HWIR-E-ASPECT-NO-MATCH: required hardware aspect did not weave a matched semantic HWIR node")
val zero_woven = HwAspectPlan(manifests: [aspect_manifest("debug.rvfi", true, [])], applications: [
    HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [HwNodeId.module_root("commit")], woven_node_count: 0)
])
expect(zero_woven.diagnostic()).to_equal("HWIR-E-ASPECT-NO-MATCH: required hardware aspect did not weave a matched semantic HWIR node")
val conflict = HwAspectPlan(manifests: [aspect_manifest("debug.rvfi", false, ["safety.lockstep"]), aspect_manifest("safety.lockstep", false, [])], applications: [])
expect(conflict.diagnostic()).to_equal("HWIR-E-ASPECT-CONFLICT: conflicting hardware aspects cannot share one plan")
```

</details>

#### should reject unsupported textual advice before any weaver can run

- should reject unsupported textual advice before any weaver can run
- Declare a textual VHDL advice kind at the typed manifest boundary
   - Expected: invalid.diagnostic() equals `HWIR-E-ASPECT-ADVICE: hardware aspect advice kind is unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject unsupported textual advice before any weaver can run")
step("Declare a textual VHDL advice kind at the typed manifest boundary")
val invalid = HwAspectManifest(id: "debug.raw_vhdl", version: "1.0.0",
    content_hash: "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    stage: "RTL", advice_kind: "vhdl_text", effect_class: "observational",
    required: false, required_capabilities: [], provided_capabilities: [], conflicts_with: [],
    join_point_selectors: ["commit.retire"], added_port_count: 0, added_state_count: 0,
    latency_contract: "transparent", proof_obligations: ["architectural_noninterference"])
expect(invalid.diagnostic()).to_equal("HWIR-E-ASPECT-ADVICE: hardware aspect advice kind is unsupported")
```

</details>

#### should require the declared proof obligation for each effect class

- should require the declared proof obligation for each effect class
- Validate observational and provider-replacement manifest proof obligations
   - Expected: missing_observational_proof.diagnostic() equals `HWIR-E-ASPECT-PROOF: hardware aspect effect class requires its declared proof... (full value in folded executable source)`
   - Expected: provider.diagnostic() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should require the declared proof obligation for each effect class")
step("Validate observational and provider-replacement manifest proof obligations")
var missing_observational_proof = aspect_manifest("debug.bad_proof", false, [])
missing_observational_proof.proof_obligations = ["cycle_equivalence"]
expect(missing_observational_proof.diagnostic()).to_equal("HWIR-E-ASPECT-PROOF: hardware aspect effect class requires its declared proof obligation")
val provider = HwAspectManifest(id: "provider.mul", version: "1.0.0",
    content_hash: "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    stage: "Elaboration", advice_kind: "replace", effect_class: "provider-replacement",
    required: false, required_capabilities: ["mul"], provided_capabilities: ["mul.fast"],
    conflicts_with: [], join_point_selectors: ["execute.request"],
    added_port_count: 0, added_state_count: 0, latency_contract: "fixed",
    proof_obligations: ["interface_refinement"])
expect(provider.diagnostic()).to_equal("")
```

</details>

#### should weave only a matched transparent observational output into typed HWIR

- should weave only a matched transparent observational output into typed HWIR
- Lower a typed module and attach one declared module-port observation
   - Expected: result.is_ok() is true
   - Expected: woven.route equals `hwir-aspect-observe`
   - Expected: woven.added_port_count equals `1`
   - Expected: woven.module.ports.len() equals `4`
   - Expected: woven.module.port_direction("rvfi_in_a") equals `out`
   - Expected: woven.module.port_width("rvfi_in_a") equals `32`
   - Expected: woven.module.shape_diagnostic() equals ``
   - Expected: woven.module.structural_sha256() == module.structural_sha256() is false
   - Expected: emitted.is_success() is true
   - Expected: emitted.uses_legacy_fallback() is false
   - Expected: emitted.route equals `hwir-strict`
   - Expected: false is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should weave only a matched transparent observational output into typed HWIR")
step("Lower a typed module and attach one declared module-port observation")
val lowered = lower_strict_hwir_and_module(
    HwirLowerInput.hardware("aspect_and", 2, 1, 0, 0), CoreConfig.rv32())
if val module = lowered.module:
    val manifest = observed_port_manifest()
    val plan = HwAspectPlan(manifests: [manifest], applications: [
        HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [module.node_id], woven_node_count: 1)
    ])
    val result = weave_hwir_observational_ports(module, plan, [
        HwAspectProbe(aspect_id: "debug.rvfi", target_node_id: module.node_id,
            source_value: "in_a", output_port: "rvfi_in_a")
    ])
    expect(result.is_ok()).to_equal(true)
    if val woven = result.ok():
        expect(woven.route).to_equal("hwir-aspect-observe")
        expect(woven.added_port_count).to_equal(1)
        expect(woven.module.ports.len()).to_equal(4)
        expect(woven.module.port_direction("rvfi_in_a")).to_equal("out")
        expect(woven.module.port_width("rvfi_in_a")).to_equal(32)
        expect(woven.module.shape_diagnostic()).to_equal("")
        expect(woven.module.structural_sha256() == module.structural_sha256()).to_equal(false)
        val emitted = render_strict_hwir_vhdl(woven.module)
        expect(emitted.is_success()).to_equal(true)
        expect(emitted.uses_legacy_fallback()).to_equal(false)
        expect(emitted.route).to_equal("hwir-strict")
        expect(emitted.vhdl).to_contain("rvfi_in_a : out std_logic_vector(31 downto 0)")
        expect(emitted.vhdl).to_contain("rvfi_in_a <= in_a;")
    else:
        expect(false).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should leave an absent plan unchanged and reject undeclared probes

- should leave an absent plan unchanged and reject undeclared probes
- Apply the absent plan before attempting an undeclared observational probe
   - Expected: absent.is_ok() is true
   - Expected: result.is_unchanged() is true
   - Expected: result.module.structural_sha256() equals `module.structural_sha256()`
   - Expected: false is true
   - Expected: rejected.is_err() is true
   - Expected: rejected.err() equals `HWIR-E-ASPECT-ABSENT: disabled hardware aspect plan cannot receive probes`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should leave an absent plan unchanged and reject undeclared probes")
step("Apply the absent plan before attempting an undeclared observational probe")
val lowered = lower_strict_hwir_and_module(
    HwirLowerInput.hardware("absent_aspect_and", 2, 1, 0, 0), CoreConfig.rv32())
if val module = lowered.module:
    val absent = weave_hwir_observational_ports(module, hwir_aspect_plan_absent(), [])
    expect(absent.is_ok()).to_equal(true)
    if val result = absent.ok():
        expect(result.is_unchanged()).to_equal(true)
        expect(result.module.structural_sha256()).to_equal(module.structural_sha256())
    else:
        expect(false).to_equal(true)
    val rejected = weave_hwir_observational_ports(module, hwir_aspect_plan_absent(), [
        HwAspectProbe(aspect_id: "debug.rvfi", target_node_id: module.node_id,
            source_value: "in_a", output_port: "rvfi_in_a")
    ])
    expect(rejected.is_err()).to_equal(true)
    expect(rejected.err()).to_equal("HWIR-E-ASPECT-ABSENT: disabled hardware aspect plan cannot receive probes")
else:
    expect(false).to_equal(true)
```

</details>

#### should bind weave accounting and scope to the supplied typed module

- should bind weave accounting and scope to the supplied typed module
- Submit mismatched attachment counts and a foreign typed module node
   - Expected: count_result.is_err() is true
   - Expected: count_result.err() equals `HWIR-E-ASPECT-ACCOUNTING: declared weave count must equal typed probe attachm... (full value in folded executable source)`
   - Expected: scope_result.is_err() is true
   - Expected: scope_result.err() equals `HWIR-E-ASPECT-SCOPE: module observational weaving requires every matched node... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should bind weave accounting and scope to the supplied typed module")
step("Submit mismatched attachment counts and a foreign typed module node")
val lowered = lower_strict_hwir_and_module(
    HwirLowerInput.hardware("accounted_aspect_and", 2, 1, 0, 0), CoreConfig.rv32())
if val module = lowered.module:
    val manifest = observed_port_manifest()
    val mismatched_count = HwAspectPlan(manifests: [manifest], applications: [
        HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [module.node_id], woven_node_count: 2)
    ])
    val probe = HwAspectProbe(aspect_id: "debug.rvfi", target_node_id: module.node_id,
        source_value: "in_a", output_port: "rvfi_in_a")
    val count_result = weave_hwir_observational_ports(module, mismatched_count, [probe])
    expect(count_result.is_err()).to_equal(true)
    expect(count_result.err()).to_equal("HWIR-E-ASPECT-ACCOUNTING: declared weave count must equal typed probe attachments")
    val scope_manifest = aspect_manifest("debug.scope", false, [])
    val invalid_scope = HwAspectPlan(manifests: [scope_manifest], applications: [
        HwAspectApplication(aspect_id: "debug.scope", matched_node_ids: [HwNodeId.module_root("other_module")], woven_node_count: 0)
    ])
    val scope_result = weave_hwir_observational_ports(module, invalid_scope, [])
    expect(scope_result.is_err()).to_equal(true)
    expect(scope_result.err()).to_equal("HWIR-E-ASPECT-SCOPE: module observational weaving requires every matched node to be the supplied module node")
else:
    expect(false).to_equal(true)
```

</details>

#### should fail closed when a probe cannot realize its declared semantic join point

- should fail closed when a probe cannot realize its declared semantic join point
- Request module-port weaving through unsupported join-point and stage declarations
   - Expected: wrong_join.is_err() is true
   - Expected: wrong_stage.is_err() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should fail closed when a probe cannot realize its declared semantic join point")
step("Request module-port weaving through unsupported join-point and stage declarations")
val lowered = lower_strict_hwir_and_module(
    HwirLowerInput.hardware("join_scope_aspect_and", 2, 1, 0, 0), CoreConfig.rv32())
if val module = lowered.module:
    var wrong_join_manifest = observed_port_manifest()
    wrong_join_manifest.join_point_selectors = ["commit.retire"]
    val wrong_join_plan = HwAspectPlan(manifests: [wrong_join_manifest], applications: [
        HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [module.node_id], woven_node_count: 1)
    ])
    val probe = HwAspectProbe(aspect_id: "debug.rvfi", target_node_id: module.node_id,
        source_value: "in_a", output_port: "rvfi_in_a")
    val wrong_join = weave_hwir_observational_ports(module, wrong_join_plan, [probe])
    expect(wrong_join.is_err()).to_equal(true)
    expect(wrong_join.err()).to_equal(
        "HWIR-E-ASPECT-JOIN-SCOPE: observational port weaving supports only the RTL module.port join point")

    var wrong_stage_manifest = observed_port_manifest()
    wrong_stage_manifest.stage = "Verification"
    val wrong_stage_plan = HwAspectPlan(manifests: [wrong_stage_manifest], applications: [
        HwAspectApplication(aspect_id: "debug.rvfi", matched_node_ids: [module.node_id], woven_node_count: 1)
    ])
    val wrong_stage = weave_hwir_observational_ports(module, wrong_stage_plan, [probe])
    expect(wrong_stage.is_err()).to_equal(true)
    expect(wrong_stage.err()).to_equal(
        "HWIR-E-ASPECT-JOIN-SCOPE: observational port weaving supports only the RTL module.port join point")
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed Gen2 hardware aspect manifests.
- typed Gen2 hardware aspect manifests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `5bb020ea21428e62423bbacb27f51851a6a9cc4c8e2c97ecbe64ca4eb8649041`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5bb020ea21428e62423bbacb27f51851a6a9cc4c8e2c97ecbe64ca4eb8649041`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5bb020ea21428e62423bbacb27f51851a6a9cc4c8e2c97ecbe64ca4eb8649041`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep a disabled aspect plan structurally zero-cost' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep a disabled aspect plan structurally zero-cost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit a required observational aspect only with a semantic HWIR match' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should admit a required observational aspect only with a semantic HWIR match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed for missing, zero-match, or conflicting aspect plans' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed for missing, zero-match, or conflicting aspect plans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unsupported textual advice before any weaver can run' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require the declared proof obligation for each effect class' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_aspect_manifest_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should weave only a matched transparent observational output into typed HWIR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
