# Cpu Simd Session Contract Specification

> Tests covering CpuSimdSession compute contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cpu Simd Session Contract Specification

## Scenarios

### CpuSimdSession compute contract

#### reports CPU SIMD kind availability and safe lifecycle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports CPU SIMD kind availability and safe lifecycle
   - Expected: session.kind().kind equals `ComputeSessionKind.cpu_simd().kind`
   - Expected: session.is_available() is true
   - Expected: session.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports CPU SIMD kind availability and safe lifecycle")
var session = CpuSimdSession.create("auto")

expect(session.kind().kind).to_equal(ComputeSessionKind.cpu_simd().kind)
expect(session.is_available()).to_equal(true)
expect(session.init()).to_be_nil()
expect(session.synchronize()).to_be_nil()
session.shutdown()
expect(session.initialized).to_equal(false)
```

</details>

#### delegates fill copy alpha blit and scroll operations to SIMD kernels

- delegates fill copy alpha blit and scroll operations to SIMD kernels
   - Expected: pixels[0] equals `0xFF010203`
   - Expected: pixels[3] equals `0xFF010203`
   - Expected: pixels[4] equals `0xFF112233`
   - Expected: pixels[7] equals `0xFF112233`
   - Expected: pixels[12] equals `0xFF112233`
   - Expected: pixels[4] equals `0xFF010203`
   - Expected: hits.fill_hits equals `1`
   - Expected: hits.copy_hits equals `1`
   - Expected: hits.alpha_hits equals `1`
   - Expected: hits.blit_hits equals `1`
   - Expected: hits.scroll_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delegates fill copy alpha blit and scroll operations to SIMD kernels")
reset_simd_hits()
var session = CpuSimdSession.create("auto")
expect(session.init()).to_be_nil()

var pixels: [u32] = [0u32; 16]
var src: [u32] = [0xFF112233; 16]
var alpha_src: [u32] = [0x80FF0000; 16]

expect(session.fill(pixels, 0, 4, 0xFF010203)).to_be_nil()
expect(pixels[0]).to_equal(0xFF010203)
expect(pixels[3]).to_equal(0xFF010203)

expect(session.copy(pixels, 4, src, 0, 4)).to_be_nil()
expect(pixels[4]).to_equal(0xFF112233)
expect(pixels[7]).to_equal(0xFF112233)

expect(session.alpha_blend(pixels, alpha_src, 8, 4)).to_be_nil()
expect(pixels[8]).to_be_greater_than(0)

expect(session.blit_rect(pixels, 4, 0, 3, src, 4, 0, 0, 4, 1)).to_be_nil()
expect(pixels[12]).to_equal(0xFF112233)

expect(session.scroll(pixels, 4, 0, 0, 4, 4, 1)).to_be_nil()
expect(pixels[4]).to_equal(0xFF010203)

val hits = session.hit_counts()
expect(hits.fill_hits).to_equal(1)
expect(hits.copy_hits).to_equal(1)
expect(hits.alpha_hits).to_equal(1)
expect(hits.blit_hits).to_equal(1)
expect(hits.scroll_hits).to_equal(1)
```

</details>

#### treats GPU-only module and kernel hooks as CPU no-ops

- treats GPU-only module and kernel hooks as CPU no-ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats GPU-only module and kernel hooks as CPU no-ops")
var session = CpuSimdSession.create("auto")
expect(session.init()).to_be_nil()

expect(session.load_module("unused", "ptx")).to_be_nil()
expect(session.launch_kernel("unused", 1, 1, 1, 1)).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CpuSimdSession compute contract.
- CpuSimdSession compute contract

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eb2a2a162de797f3608d339befc91867a113e90ee7486ac97a01af5d0f76b61c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb2a2a162de797f3608d339befc91867a113e90ee7486ac97a01af5d0f76b61c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb2a2a162de797f3608d339befc91867a113e90ee7486ac97a01af5d0f76b61c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports CPU SIMD kind availability and safe lifecycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delegates fill copy alpha blit and scroll operations to SIMD kernels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/cpu_simd_session_contract_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats GPU-only module and kernel hooks as CPU no-ops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
