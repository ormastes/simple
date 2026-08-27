# SPIR-V Boundary Canonicalizer — Pure Scenarios

> Split out of `spirv_boundary_glslang_spec.spl` so the canonicalizer's own

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPIR-V Boundary Canonicalizer — Pure Scenarios

Split out of `spirv_boundary_glslang_spec.spl` so the canonicalizer's own

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver / counterpart conformance |
| Status | In Progress |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/spirv_canonicalize_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Split out of `spirv_boundary_glslang_spec.spl` so the canonicalizer's own
correctness can be checked with NO subprocess and NO fixture file — these
scenarios cost nothing and must never be allowed to regress just because the
exec-backed comparison in the sibling spec is slow or unavailable.

## Scope and Preconditions

Pure text manipulation only. No GPU, no installed toolchain, no filesystem
fixture required.

## Primary Workflow

Feed hand-built instruction-line lists straight to
`boundary_spirv_canonicalize`'s functions and check the four named
dimensions (assembly comments, debug opcodes, id renumbering) each do
exactly what they claim and nothing more.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Debug opcode allowlist | Stripped by OPCODE IDENTITY only — never by "is this id referenced" |
| The closed hole | A prior version stripped by unreferenced-result-id, which deleted a live `OpLabel` and a live `OpExtInstImport` |
| Positive rejection | Proves the closed hole stays closed: a module missing either instruction must NOT canonicalize equal to one that has it |

## Related Specifications

- [SPIR-V boundary comparison](spirv_boundary_glslang_spec.spl) — the exec/fixture-backed comparison this canonicalizer serves

## Evidence and Provenance

Self-contained; every scenario constructs its own input.

## Recovery and Troubleshooting

A failure here means the canonicalizer itself regressed — fix
`boundary_spirv_canonicalize.spl`, never delete or weaken one of these
scenarios to make it pass.

## Compatibility and Limitations

None — this file has no external dependency by design.

## Scenarios

### spirv boundary canonicalizer — debug opcode allowlist

#### strips debug opcodes by an explicit allowlist, not by reachability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-001
```

</details>

#### never treats OpLabel or OpExtInstImport as a debug opcode

- check the allowlist directly against the two opcodes the old filter destroyed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check the allowlist directly against the two opcodes the old filter destroyed")
assert_false(spirv_is_debug_opcode("OpLabel"))
assert_false(spirv_is_debug_opcode("OpExtInstImport"))
```

</details>

#### strips the full Debug Instruction set named in the module docstring

- check every allowlisted opcode individually


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check every allowlisted opcode individually")
assert_true(spirv_is_debug_opcode("OpSource"))
assert_true(spirv_is_debug_opcode("OpSourceContinued"))
assert_true(spirv_is_debug_opcode("OpSourceExtension"))
assert_true(spirv_is_debug_opcode("OpString"))
assert_true(spirv_is_debug_opcode("OpName"))
assert_true(spirv_is_debug_opcode("OpMemberName"))
assert_true(spirv_is_debug_opcode("OpModuleProcessed"))
assert_true(spirv_is_debug_opcode("OpLine"))
assert_true(spirv_is_debug_opcode("OpNoLine"))
```

</details>

### spirv boundary canonicalizer — assembly comments

#### recognizes a `;`-prefixed line as a comment, never as an instruction

- check the comment predicate directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check the comment predicate directly")
assert_true(spirv_is_comment_line("; SPIR-V"))
assert_true(spirv_is_comment_line("   ; Bound: 7"))
assert_false(spirv_is_comment_line("%1 = OpTypeVoid"))
```

</details>

#### drops spirv_builder's own header comments before comparing

- canonicalize text shaped like SpirvBuilder.build()'s output


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("canonicalize text shaped like SpirvBuilder.build()'s output")
val raw = "; SPIR-V\n; Version: 1.0\n; Bound: 3\nOpCapability Shader\n%1 = OpTypeVoid"
val canon = spirv_canonical_text(raw)
assert_false(canon.contains(";"))
assert_contains(canon, "OpCapability Shader")
```

</details>

### spirv boundary canonicalizer — id renumbering

#### renumbers ids by first appearance regardless of source numbering

- renumber two structurally identical lines with different raw ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("renumber two structurally identical lines with different raw ids")
val a = spirv_renumber(["%7 = OpTypeVoid", "%9 = OpTypeFunction %7"])
val b = spirv_renumber(["%1 = OpTypeVoid", "%2 = OpTypeFunction %1"])
assert_equal(a.join("\n"), b.join("\n"))
```

</details>

#### renumbers glslang's friendly names the same way as numeric ids

- renumber a line list using spirv-dis's %void / %main style names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("renumber a line list using spirv-dis's %void / %main style names")
val friendly = spirv_renumber(["%void = OpTypeVoid", "%main = OpFunction %void None %void"])
val numeric = spirv_renumber(["%1 = OpTypeVoid", "%2 = OpFunction %1 None %1"])
assert_equal(friendly.join("\n"), numeric.join("\n"))
```

</details>

### spirv boundary canonicalizer — closed hole: positive rejections

#### does NOT canonicalize a module missing OpLabel equal to one that has it

- build two disassembly-shaped line sets differing only by OpLabel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build two disassembly-shaped line sets differing only by OpLabel")
val with_label = "OpCapability Shader\n%1 = OpFunction %2 None %3\n%4 = OpLabel\nOpReturn\nOpFunctionEnd"
val without_label = "OpCapability Shader\n%1 = OpFunction %2 None %3\nOpReturn\nOpFunctionEnd"
assert_not_equal(spirv_canonical_text(with_label), spirv_canonical_text(without_label))
```

</details>

#### does NOT canonicalize a module missing OpExtInstImport equal to one that has it

- build two disassembly-shaped line sets differing only by OpExtInstImport


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build two disassembly-shaped line sets differing only by OpExtInstImport")
val with_extinst = "OpCapability Shader\n%1 = OpExtInstImport \"GLSL.std.450\"\nOpMemoryModel Logical GLSL450"
val without_extinst = "OpCapability Shader\nOpMemoryModel Logical GLSL450"
assert_not_equal(spirv_canonical_text(with_extinst), spirv_canonical_text(without_extinst))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `79bc3cdc825dfbde2967e7e3b1cf76ad6304f1a4400bc02262690d3e74d6fd97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79bc3cdc825dfbde2967e7e3b1cf76ad6304f1a4400bc02262690d3e74d6fd97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79bc3cdc825dfbde2967e7e3b1cf76ad6304f1a4400bc02262690d3e74d6fd97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/spirv_canonicalize_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/spirv_canonicalize_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/spirv_canonicalize_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/spirv_canonicalize_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/spirv_canonicalize_spec.spl:78:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'strips debug opcodes by an explicit allowlist, not by reachability' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/spirv_canonicalize_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never treats OpLabel or OpExtInstImport as a debug opcode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/spirv_canonicalize_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips the full Debug Instruction set named in the module docstring' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/spirv_canonicalize_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes a `;`-prefixed line as a comment, never as an instruction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
