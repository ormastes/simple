# vulkan_submit_no_wait_backed_spec

> Proves the non-blocking submit extern is genuinely runtime-backed and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_submit_no_wait_backed_spec

Proves the non-blocking submit extern is genuinely runtime-backed and

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the non-blocking submit extern is genuinely runtime-backed and
    honours its invalid-input contract on a host with no Vulkan device.

## Scenarios

### rt_vulkan_submit_no_wait device-free contract

#### should be a real backed extern returning a concrete failure code for handle 0

- should be a real backed extern returning a concrete failure code for handle 0
- Submit with the null command handle
- A backed extern returns a concrete 0; an unbacked one returns nil
   - Expected: fence equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("should be a real backed extern returning a concrete failure code for handle 0")
step("Submit with the null command handle")
val fence = vulkan_sffi_submit_no_wait(0)

step("A backed extern returns a concrete 0; an unbacked one returns nil")
expect(fence).to_equal(0)
```

</details>

#### should refuse an unknown command handle instead of fabricating a fence

- should refuse an unknown command handle instead of fabricating a fence
- Submit a command handle that was never begun
- No fence is issued
   - Expected: fence equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("should refuse an unknown command handle instead of fabricating a fence")
step("Submit a command handle that was never begun")
val fence = vulkan_sffi_submit_no_wait(0x7FFF0000)

step("No fence is issued")
expect(fence).to_equal(0)
```

</details>

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

- `REQ-SSPEC-GPU`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd4824982c68763b28a3db554cdf5a20228b7a71870e260f98aac2ffd0fc360d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd4824982c68763b28a3db554cdf5a20228b7a71870e260f98aac2ffd0fc360d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd4824982c68763b28a3db554cdf5a20228b7a71870e260f98aac2ffd0fc360d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl
mirror: doc/06_spec/01_unit/gpu/vulkan_submit_no_wait_backed_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/gpu/vulkan_submit_no_wait_backed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/gpu/vulkan_submit_no_wait_backed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should be a real backed extern returning a concrete failure code for handle 0' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should be a real backed extern returning a concrete failure code for handle 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse an unknown command handle instead of fabricating a fence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/gpu/vulkan_submit_no_wait_backed_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should refuse an unknown command handle instead of fabricating a fence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
