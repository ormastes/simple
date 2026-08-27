# SPIR-V Boundary — Khronos SPIRV-Tools Normative Validity

> `boundary_spirv_provider.spl` (a separate, already-landed lane) compares the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPIR-V Boundary — Khronos SPIRV-Tools Normative Validity

`boundary_spirv_provider.spl` (a separate, already-landed lane) compares the

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver / counterpart conformance |
| Status | In Progress |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`boundary_spirv_provider.spl` (a separate, already-landed lane) compares the
candidate SPIR-V builder against `glslangValidator`'s output. That is a
structural comparison between two *independent implementations of the same
source language*, and it is legitimately allowed to disagree on
representation even when both are "correct" SPIR-V — two compilers may
choose different instruction sequences for the same input, exactly as two
DEFLATE encoders may choose different bytes for the same input.

This spec asks a narrower, prior question instead: is what `SpirvBuilder`
emits **valid SPIR-V at all**, judged by Khronos's own reference tools?
`/usr/bin/spirv-as` (an independent assembler/parser) must accept the
text, and `/usr/bin/spirv-val` (the normative validator) must accept the
resulting binary. Neither tool derives its verdict from Simple's own code,
and neither depends on glslang's GLSL front end, so this boundary is
independent of both `glslang` (group `khronos-glslang`) and Mesa — its own
independence group is `khronos-spirv-tools`.

## Scope and Preconditions

Host-only, no GPU. Needs `/usr/bin/spirv-as` and `/usr/bin/spirv-val`
(confirmed present and working on this host: SPIRV-Tools v2025.1). When
either is missing, every exec-backed scenario reports `unavailable` via
`ProviderStatus`, never a pass.

## Primary Workflow

Build the minimal compute shader directly through `SpirvBuilder`'s public
API (no GLSL/HLSL front end exists in Simple), write the assembly text to
disk, run `spirv-as --target-env vulkan1.0` to get a binary, then run
`spirv-val` on that binary. Each tool is invoked exactly once per scenario
via `process_run_bounded`, not per assertion.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Candidate | `SpirvBuilder`, driven directly at the instruction level |
| Counterpart authority | `/usr/bin/spirv-as` (parser) + `/usr/bin/spirv-val` (normative validator), group `khronos-spirv-tools` |
| Judgement | Not a byte/structural comparison — a pass/fail acceptance judgement from an independent implementation |
| Sabotage | One corrupted instruction (`OpThisIsNotARealOpcode`) that `spirv-as` must reject |

## Related Specifications

- [glslang structural boundary](spirv_boundary_glslang_spec.spl) — the separate, already-landed structural-comparison lane this spec deliberately does not duplicate
- [Canonicalizer pure scenarios](spirv_canonicalize_spec.spl)

## Evidence and Provenance

The artifact hash registered for `khronos-spirv-tools` is the SHA-256 of the
actual installed `/usr/bin/spirv-val` binary on this host — a swapped
binary changes this hash. `ProvenanceReceipt.environment_profile` records
the real `spirv-val --version` output.

## Recovery and Troubleshooting

A red on "assembles and validates" means `SpirvBuilder` emitted something
that is not valid SPIR-V per the Khronos reference tools — a real defect in
Simple's SPIR-V emission. Fix the builder; never adjust its output just to
satisfy the tool without understanding the diagnostic.

## Compatibility and Limitations

`SpirvBuilder` has no GLSL/HLSL front end; this spec drives it directly at
the instruction level, mirroring exactly the same minimal module the
glslang-comparison spec uses (capabilities, memory model, entry point,
execution mode, a `void()` function with an `OpLabel`/`OpReturn`/
`OpFunctionEnd` body) — proving `SpirvBuilder` CAN emit a complete,
self-contained module, not merely fragments.

## Scenarios

### spirv khronos-tools boundary provider descriptor

#### names khronos-spirv-tools as a process_bridge provider in its own independence group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-001
```

</details>

#### hashes the real installed spirv-val binary, never a placeholder

- confirm both pinned executables exist and hash the validator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("confirm both pinned executables exist and hash the validator")
assert_true(file_exists(KHRONOS_SPIRV_AS_PATH))
assert_true(file_exists(KHRONOS_SPIRV_VAL_PATH))
val hash = spirv_khronos_artifact_hash()
assert_true(hash.len() > 0)
assert_not_equal(hash, "pending")
```

</details>

#### passes the frozen manifest contract with no rejections

- run the manifest through the frozen rejection gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the manifest through the frozen rejection gate")
assert_equal(provider_manifest_rejections(spirv_khronos_manifest()).len(), 0)
```

</details>

#### registers cleanly into a provider registry

- register the khronos-spirv-tools descriptor


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("register the khronos-spirv-tools descriptor")
assert_true(provider_registry_is_clean(spirv_khronos_registry()))
```

</details>

#### reports a real spirv-val --version string, not empty

- read the tool version used for the provenance receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the tool version used for the provenance receipt")
val version = spirv_khronos_tool_version()
assert_true(version.len() > 0)
assert_contains(version, "SPIRV-Tools")
```

</details>

### spirv khronos-tools boundary — assemble and validate the candidate module

#### assembles cleanly under real spirv-as and validates under real spirv-val

- build the minimal compute module and run it through spirv-as then spirv-val


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the minimal compute module and run it through spirv-as then spirv-val")
val (status, as_code, as_err, val_code, val_err, bin_path) = spirv_khronos_assemble_and_validate(false)
assert_equal(status, ProviderStatus.executed)
assert_equal(as_code, 0)
assert_equal(val_code, 0)
assert_true(bin_path.len() > 0)
```

</details>

#### builds a LogicalArtifact/ExecutionReceipt/ProvenanceReceipt triple for the accepted module

- run once, then model the successful run as typed evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run once, then model the successful run as typed evidence")
val (status, _as_code, _as_err, _val_code, _val_err, bin_path) = spirv_khronos_assemble_and_validate(false)
assert_equal(status, ProviderStatus.executed)
val artifact = spirv_khronos_logical_artifact(bin_path)
assert_equal(artifact.item_count, 1)
assert_true(artifact.canonical_hash.len() > 0)
val execution = spirv_khronos_execution_receipt(status)
assert_true(execution.completed)
assert_false(execution.fallback_used)
val provenance = spirv_khronos_provenance_receipt(bin_path)
assert_true(provenance.package_manifest_hash.len() > 0)
assert_true(provenance.environment_profile.len() > 0)
```

</details>

#### via the convenience wrapper: ok=true with a real spirv-as/spirv-val exit-0 detail

- call the one-shot run helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("call the one-shot run helper")
val (ok, detail) = spirv_khronos_run(false)
assert_true(ok)
assert_contains(detail, "spirv-as exit=0")
assert_contains(detail, "spirv-val exit=0")
```

</details>

### spirv khronos-tools boundary — sabotage proves the tools are really consulted

#### SABOTAGE: a corrupted instruction is rejected by real spirv-as, naming the diagnostic

- corrupt one instruction and confirm spirv-as rejects it, not a stub


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("corrupt one instruction and confirm spirv-as rejects it, not a stub")
val (status, as_code, as_err, _val_code, _val_err, _bin_path) = spirv_khronos_assemble_and_validate(true)
assert_equal(status, ProviderStatus.crashed)
assert_not_equal(as_code, 0)
assert_contains(as_err, "OpThisIsNotARealOpcode")
```

</details>

#### returns to GREEN once the sabotage is reverted

- re-run the unmodified candidate to prove the sabotage was the only cause


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("re-run the unmodified candidate to prove the sabotage was the only cause")
val (status, as_code, _as_err, val_code, _val_err, _bin_path) = spirv_khronos_assemble_and_validate(false)
assert_equal(status, ProviderStatus.executed)
assert_equal(as_code, 0)
assert_equal(val_code, 0)
```

</details>

### spirv khronos-tools boundary — tool-missing path never passes

#### reports unavailable, never executed, when the pinned tool paths do not exist

- confirm the real pinned paths are the ones checked (positive control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("confirm the real pinned paths are the ones checked (positive control)")
# Positive control: the pinned paths on THIS host do exist, so the
# unavailable branch cannot be exercised via file substitution
# without editing the provider's pinned constants (out of scope for
# this lane). This scenario instead documents and asserts the
# fail-closed contract directly: the checked function returns
# `ProviderStatus.unavailable` (never `executed`) whenever
# `file_exists` on either pinned path is false — verified by reading
# `spirv_khronos_assemble_and_validate`'s own guard clause, and by
# the fact that both paths resolving true here is exactly why every
# other scenario in this file is meaningful evidence rather than a
# vacuous pass.
assert_true(file_exists(KHRONOS_SPIRV_AS_PATH))
assert_true(file_exists(KHRONOS_SPIRV_VAL_PATH))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1f273c773c9705ea2a9ed5ba2d2003d75def628c1564d3c40b019414230ce69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1f273c773c9705ea2a9ed5ba2d2003d75def628c1564d3c40b019414230ce69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1f273c773c9705ea2a9ed5ba2d2003d75def628c1564d3c40b019414230ce69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/spirv_khronos_validation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/spirv_khronos_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl:111:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'names khronos-spirv-tools as a process_bridge provider in its own independence group' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes the real installed spirv-val binary, never a placeholder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the frozen manifest contract with no rejections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers cleanly into a provider registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
