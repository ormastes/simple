# Trace32 Wrapper Specification

> Tests covering Trace32 wrapper portable smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trace32 Wrapper Specification

## Scenarios

### Trace32 wrapper portable smoke

#### records trace32 backend names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records trace32 backend names
   - Expected: native_backend equals `trace32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records trace32 backend names")
val native_backend = "trace32"
val gdb_backend = "trace32-gdb"
expect(native_backend).to_equal("trace32")
expect(gdb_backend).to_contain("gdb")
```

</details>

#### records native feature names

- records native feature names
   - Expected: features.len() equals `3`
   - Expected: features[1] equals `TraceCapture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records native feature names")
val features = ["Halt", "TraceCapture", "CoverageCollect"]
expect(features.len()).to_equal(3)
expect(features[1]).to_equal("TraceCapture")
```

</details>

#### records default adapter settings

- records default adapter settings
   - Expected: default_arch equals `arm`
   - Expected: timeout_ms equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records default adapter settings")
val default_arch = "arm"
val timeout_ms = 30000
expect(default_arch).to_equal("arm")
expect(timeout_ms).to_equal(30000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Trace32 wrapper portable smoke.
- Trace32 wrapper portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2702930f567eb0cfda1cc3c2b96c90486b156505c74d163e480ccba64b07cd41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2702930f567eb0cfda1cc3c2b96c90486b156505c74d163e480ccba64b07cd41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2702930f567eb0cfda1cc3c2b96c90486b156505c74d163e480ccba64b07cd41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl
mirror: doc/06_spec/03_system/hardware/t32_tools/trace32_wrapper_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/t32_tools/trace32_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/t32_tools/trace32_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records trace32 backend names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records native feature names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records default adapter settings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
