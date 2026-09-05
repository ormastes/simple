# Mir Lowering No Stray Debug Marker Specification

> Tests covering pure-Simple MIR lowering carries no unguarded debug markers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Lowering No Stray Debug Marker Specification

## Scenarios

### pure-Simple MIR lowering carries no unguarded debug markers

#### does not print MARKER_RT_IS_NONE_ARM_REACHED on the nil-comparison path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not print MARKER_RT_IS_NONE_ARM_REACHED on the nil-comparison path
- Scan src/compiler/50.mir for the exact marker left behind by the Option/nil investigation
- The `x == nil` lowering arm is on the hot path of every module, so this marker must not exist at all
   - Expected: hits equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not print MARKER_RT_IS_NONE_ARM_REACHED on the nil-comparison path")
step("Scan src/compiler/50.mir for the exact marker left behind by the Option/nil investigation")
val hits = grep_mir("MARKER_RT_IS_NONE_ARM_REACHED")

step("The `x == nil` lowering arm is on the hot path of every module, so this marker must not exist at all")
expect(hits).to_equal("")
```

</details>

#### has no MARKER_-prefixed probe strings anywhere in MIR lowering

- has no MARKER_-prefixed probe strings anywhere in MIR lowering
- Generalise to the marker spelling this repo actually used for one-off lowering probes
- Any MARKER_ string under 50.mir is an investigation probe that was never cleaned up
   - Expected: hits equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has no MARKER_-prefixed probe strings anywhere in MIR lowering")
step("Generalise to the marker spelling this repo actually used for one-off lowering probes")
val hits = grep_mir("MARKER_")

step("Any MARKER_ string under 50.mir is an investigation probe that was never cleaned up")
expect(hits).to_equal("")
```

</details>

#### has no unguarded eprint of a bare debug-probe literal in MIR lowering

- has no unguarded eprint of a bare debug-probe literal in MIR lowering
- Scan for eprint calls whose argument is a shouty ALL-CAPS probe literal — the shape every such probe has taken here
- Diagnostics must go through the compiler's error/warning reporting, never a raw eprint probe
   - Expected: hits equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has no unguarded eprint of a bare debug-probe literal in MIR lowering")
step("Scan for eprint calls whose argument is a shouty ALL-CAPS probe literal — the shape every such probe has taken here")
val hits = grep_mir("eprint(\"[A-Z_]*MARKER[A-Z_]*\"")

step("Diagnostics must go through the compiler's error/warning reporting, never a raw eprint probe")
expect(hits).to_equal("")
```

</details>

#### proves the scan is live and would actually catch a marker

- proves the scan is live and would actually catch a marker
- Non-vacuity control: the same grep for a string that IS present must find it
- A green suite above is only meaningful if this control is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("proves the scan is live and would actually catch a marker")
step("Non-vacuity control: the same grep for a string that IS present must find it")
# `decode_runtime_value` is a real, load-bearing function in
# _MirLoweringExpr/expr_dispatch.spl. If this comes back empty the scan
# itself is broken (wrong path, grep missing, sandbox cwd wrong) and
# every green above would be meaningless.
val control = grep_mir("decode_runtime_value")

step("A green suite above is only meaningful if this control is non-empty")
expect(control).to_contain("decode_runtime_value")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple MIR lowering carries no unguarded debug markers.
- pure-Simple MIR lowering carries no unguarded debug markers

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

- Canonical SPipe generation for source `199d410be3ccb12d9310366da2056702c09ffe74f96433b9b097665181e6249a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `199d410be3ccb12d9310366da2056702c09ffe74f96433b9b097665181e6249a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `199d410be3ccb12d9310366da2056702c09ffe74f96433b9b097665181e6249a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not print MARKER_RT_IS_NONE_ARM_REACHED on the nil-comparison path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no MARKER_-prefixed probe strings anywhere in MIR lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_lowering_no_stray_debug_marker_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no unguarded eprint of a bare debug-probe literal in MIR lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
