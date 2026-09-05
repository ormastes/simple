# Hir Method Call Receiver Payload Specification

> Tests covering HIR method-call receiver payloads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Method Call Receiver Payload Specification

## Scenarios

### HIR method-call receiver payloads

#### resolves a second parameter used as an indexed method receiver

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a second parameter used as an indexed method receiver
   - Expected: lowering.errors.len() equals `0`
   - Expected: indexed_receiver_shape_is_exact(hir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolves a second parameter used as an indexed method receiver")
val source =
    "fn nested(args: [text], i: i64) -> bool:\n" +
    "    args[i].starts_with(\"-o\")\n"
val logger = Logger(level: 0)
val module = parse_full_frontend(source, "hir_method_call_receiver_payload", "hir_method_call_receiver_payload", logger)
var lowering = HirLowering.with_filename("hir_method_call_receiver_payload")
val hir = lowering.lower_module(module)

expect(lowering.errors.len()).to_equal(0)
expect(indexed_receiver_shape_is_exact(hir)).to_equal(true)
```

</details>

#### preserves a typed receiver while lowering a nested argument payload

- preserves a typed receiver while lowering a nested argument payload
   - Expected: lowering.errors.len() equals `0`
   - Expected: typed_nested_receiver_shape_is_exact(hir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves a typed receiver while lowering a nested argument payload")
val source =
    "fn nested_typed(arg: text) -> text:\n" +
    "    i64(7).to_string(arg.starts_with(\"--\"))\n"
val logger = Logger(level: 0)
val module = parse_full_frontend(source, "hir_method_call_typed_receiver", "hir_method_call_typed_receiver", logger)
var lowering = HirLowering.with_filename("hir_method_call_typed_receiver")
val hir = lowering.lower_module(module)

expect(lowering.errors.len()).to_equal(0)
expect(typed_nested_receiver_shape_is_exact(hir)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/hir_method_call_receiver_payload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR method-call receiver payloads.
- HIR method-call receiver payloads

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5f5847fc6d1f48fa6e71a439e93af032f32058ee7156cbb8ea90ca678e80544`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5f5847fc6d1f48fa6e71a439e93af032f32058ee7156cbb8ea90ca678e80544`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5f5847fc6d1f48fa6e71a439e93af032f32058ee7156cbb8ea90ca678e80544`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/compiler/hir_method_call_receiver_payload_spec.spl
mirror: doc/06_spec/02_integration/compiler/hir_method_call_receiver_payload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/hir_method_call_receiver_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/hir_method_call_receiver_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/hir_method_call_receiver_payload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/hir_method_call_receiver_payload_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a second parameter used as an indexed method receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/hir_method_call_receiver_payload_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a typed receiver while lowering a nested argument payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
