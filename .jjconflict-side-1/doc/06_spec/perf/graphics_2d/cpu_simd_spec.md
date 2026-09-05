# Cpu Simd Specification

> Tests covering cpu_simd — AC-6/AC-12: SIMD kernels, provider hit counts, target features, kernel name constants, SimdHitCounts fields after one frame, scalar vs SIMD parity, target feature reporting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cpu Simd Specification

## Scenarios

### cpu_simd — AC-6/AC-12: SIMD kernels, provider hit counts, target features

### kernel name constants

#### AC-6: fill kernel name is fill

- verify  fill kernel name is fill against runtime counters
   - Expected: KERNEL_FILL equals `fill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  fill kernel name is fill against runtime counters")
expect(KERNEL_FILL).to_equal("fill")
```

</details>

#### AC-6: copy kernel name is copy

- verify  copy kernel name is copy against runtime counters
   - Expected: KERNEL_COPY equals `copy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  copy kernel name is copy against runtime counters")
expect(KERNEL_COPY).to_equal("copy")
```

</details>

#### AC-6: alpha_blend kernel name is alpha_blend

- verify  alpha_blend kernel name is alpha_blend against runtime counters
   - Expected: KERNEL_ALPHA_BLEND equals `alpha_blend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  alpha_blend kernel name is alpha_blend against runtime counters")
expect(KERNEL_ALPHA_BLEND).to_equal("alpha_blend")
```

</details>

#### AC-6: blit kernel name is blit

- verify  blit kernel name is blit against runtime counters
   - Expected: KERNEL_BLIT equals `blit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  blit kernel name is blit against runtime counters")
expect(KERNEL_BLIT).to_equal("blit")
```

</details>

#### AC-6: scroll kernel name is scroll

- verify  scroll kernel name is scroll against runtime counters
   - Expected: KERNEL_SCROLL equals `scroll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  scroll kernel name is scroll against runtime counters")
expect(KERNEL_SCROLL).to_equal("scroll")
```

</details>

#### AC-6: five distinct kernel names exist

- verify  five distinct kernel names exist against runtime counters
   - Expected: kernels.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  five distinct kernel names exist against runtime counters")
val kernels: [text] = [KERNEL_FILL, KERNEL_COPY, KERNEL_ALPHA_BLEND, KERNEL_BLIT, KERNEL_SCROLL]
expect(kernels.len()).to_equal(5)
```

</details>

### SimdHitCounts fields after one frame

#### AC-6: fill_hits is greater than zero after a frame with fill

- verify  fill_hits is greater than zero against runtime counters
   - Expected: c.fill_hits > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  fill_hits is greater than zero against runtime counters")
val c: SimdHitCountsSentinel = make_simd_hit_counts(1, 0, 0, 0, 0, 1)
expect(c.fill_hits > 0).to_equal(true)
```

</details>

#### AC-6: copy_hits is greater than zero after a frame with copy

- verify  copy_hits is greater than zero against runtime counters
   - Expected: c.copy_hits > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  copy_hits is greater than zero against runtime counters")
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 1, 0, 0, 0, 1)
expect(c.copy_hits > 0).to_equal(true)
```

</details>

#### AC-6: alpha_hits is greater than zero after a frame with alpha_blend

- verify  alpha_hits is greater than zero against runtime counters
   - Expected: c.alpha_hits > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  alpha_hits is greater than zero against runtime counters")
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 0, 1, 0, 0, 1)
expect(c.alpha_hits > 0).to_equal(true)
```

</details>

#### AC-6: blit_hits is greater than zero after a frame with blit

- verify  blit_hits is greater than zero against runtime counters
   - Expected: c.blit_hits > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  blit_hits is greater than zero against runtime counters")
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 0, 0, 1, 0, 1)
expect(c.blit_hits > 0).to_equal(true)
```

</details>

#### AC-6: scroll_hits is greater than zero after a frame with scroll

- verify  scroll_hits is greater than zero against runtime counters
   - Expected: c.scroll_hits > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  scroll_hits is greater than zero against runtime counters")
val c: SimdHitCountsSentinel = make_simd_hit_counts(0, 0, 0, 0, 1, 1)
expect(c.scroll_hits > 0).to_equal(true)
```

</details>

#### AC-12: vectorize_changes is reported (not negative)

- verify  vectorize_changes is reported (not negative) against runtime counters
   - Expected: c.vectorize_changes >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  vectorize_changes is reported (not negative) against runtime counters")
val c: SimdHitCountsSentinel = make_simd_hit_counts(1, 1, 1, 1, 1, 3)
expect(c.vectorize_changes >= 0).to_equal(true)
```

</details>

#### AC-12: vectorize_changes count is greater than zero after vectorized frame

- verify  vectorize_changes count is greater than against runtime counters
   - Expected: c.vectorize_changes > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  vectorize_changes count is greater than against runtime counters")
val c: SimdHitCountsSentinel = make_simd_hit_counts(1, 1, 1, 1, 1, 3)
expect(c.vectorize_changes > 0).to_equal(true)
```

</details>

### scalar vs SIMD parity

#### AC-6: x86 AVX2 SIMD hash matches scalar hash

- verify  x86 AVX2 SIMD hash matches against runtime counters
   - Expected: simd_parity_ok(t) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  x86 AVX2 SIMD hash matches against runtime counters")
val t: SimdTargetSentinel = make_simd_target_x86(0xABCD1234, 0xABCD1234)
expect(simd_parity_ok(t)).to_equal(true)
```

</details>

#### AC-6: ARM NEON SIMD hash matches scalar hash

- verify  ARM NEON SIMD hash matches against runtime counters
   - Expected: simd_parity_ok(t) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  ARM NEON SIMD hash matches against runtime counters")
val t: SimdTargetSentinel = make_simd_target_arm(0xDEADBEEF, 0xDEADBEEF)
expect(simd_parity_ok(t)).to_equal(true)
```

</details>

#### AC-6: scalar fallback hash matches scalar reference

- verify  scalar fallback hash matches scalar against runtime counters
   - Expected: simd_parity_ok(t) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  scalar fallback hash matches scalar against runtime counters")
val t: SimdTargetSentinel = make_simd_target_scalar(0xCAFEBABE, 0xCAFEBABE)
expect(simd_parity_ok(t)).to_equal(true)
```

</details>

#### AC-6: differing hashes on x86 indicates a parity failure

- verify  differing hashes on x86 indicates against runtime counters
   - Expected: simd_parity_ok(t) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  differing hashes on x86 indicates against runtime counters")
val t: SimdTargetSentinel = make_simd_target_x86(0xABCD1234, 0xFFFF0000)
expect(simd_parity_ok(t)).to_equal(false)
```

</details>

### target feature reporting

#### AC-6: x86_64 target reports avx2 feature

- verify  x86_64 target reports avx2 feature against runtime counters
   - Expected: t.arch equals `x86_64`
   - Expected: t.feature equals `avx2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  x86_64 target reports avx2 feature against runtime counters")
val t: SimdTargetSentinel = make_simd_target_x86(1, 1)
expect(t.arch).to_equal("x86_64")
expect(t.feature).to_equal("avx2")
```

</details>

#### AC-6: aarch64 target reports neon feature

- verify  aarch64 target reports neon feature against runtime counters
   - Expected: t.arch equals `aarch64`
   - Expected: t.feature equals `neon`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  aarch64 target reports neon feature against runtime counters")
val t: SimdTargetSentinel = make_simd_target_arm(1, 1)
expect(t.arch).to_equal("aarch64")
expect(t.feature).to_equal("neon")
```

</details>

#### AC-6: unknown arch falls back to scalar feature

- verify  unknown arch falls back to against runtime counters
   - Expected: t.feature equals `scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CPU-SIMD
step("verify  unknown arch falls back to against runtime counters")
val t: SimdTargetSentinel = make_simd_target_scalar(1, 1)
expect(t.feature).to_equal("scalar")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/graphics_2d/cpu_simd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cpu_simd — AC-6/AC-12: SIMD kernels, provider hit counts, target features, kernel name constants, SimdHitCounts fields after one frame, scalar vs SIMD parity, target feature reporting.
- cpu_simd — AC-6/AC-12: SIMD kernels, provider hit counts, target features
- kernel name constants
- SimdHitCounts fields after one frame
- scalar vs SIMD parity
- target feature reporting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-CPU-SIMD`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c5a60767612fddeafea9c5ba69f71267b337233e8ea3746a137cf303b46d12e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5a60767612fddeafea9c5ba69f71267b337233e8ea3746a137cf303b46d12e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5a60767612fddeafea9c5ba69f71267b337233e8ea3746a137cf303b46d12e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/perf/graphics_2d/cpu_simd_spec.spl
mirror: doc/06_spec/perf/graphics_2d/cpu_simd_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/graphics_2d/cpu_simd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/graphics_2d/cpu_simd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/graphics_2d/cpu_simd_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/graphics_2d/cpu_simd_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/graphics_2d/cpu_simd_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: fill kernel name is fill' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/cpu_simd_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: copy kernel name is copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/cpu_simd_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: alpha_blend kernel name is alpha_blend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
