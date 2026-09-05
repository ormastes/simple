# hir_codec_writer_chunked_cost_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hir_codec_writer_chunked_cost_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### HirCodecWriter chunked accumulation

#### bounds the cloned array: parts never exceeds one chunk, and chunks are really sealed

- Verify: the mutated array is bounded and the bound is reached
   - Expected: w.ok is true
   - Expected: w.parts.len() <= HIR_CODEC_CHUNK_LINES is true
   - Expected: w.chunks.len() > 4 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: the mutated array is bounded and the bound is reached")
val hm = lower(gen(4, 40))
val w = encode_and_inspect(hm)
expect(w.ok).to_equal(true)
# THE invariant: the array the seed deep-clones per push stays small.
# Pre-fix this held every encoded line of the module.
expect(w.parts.len() <= HIR_CODEC_CHUNK_LINES).to_equal(true)
# Not vacuous: this module is big enough to seal many chunks.
expect(w.chunks.len() > 4).to_equal(true)
```

</details>

#### encodes in time linear in module size, not quadratic

- Verify: 4x the module costs far less than the 16x a quadratic writer charges
   - Expected: big_blob.len() > small_blob.len() * 3 is true
   - Expected: big_ms <= floor_ms * 8 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: 4x the module costs far less than the 16x a quadratic writer charges")
val small = lower(gen(2, 20))
val big = lower(gen(8, 20))

val t0 = rt_time_now_monotonic_ms()
val small_blob = hir_module_encode(small)
val small_ms = rt_time_now_monotonic_ms() - t0

val t1 = rt_time_now_monotonic_ms()
val big_blob = hir_module_encode(big)
val big_ms = rt_time_now_monotonic_ms() - t1

# The fixture really is ~4x bigger, so the ratio below means something.
expect(big_blob.len() > small_blob.len() * 3).to_equal(true)

# Linear would be ~4x, quadratic ~16x. 8x separates them with room for
# scheduler noise on a shared box. Guard against a 0ms small case.
val floor_ms = if small_ms < 1: 1 else: small_ms
expect(big_ms <= floor_ms * 8).to_equal(true)
```

</details>

#### chunking is invisible in the output: re-encode is byte-identical

- Verify: the seam between chunks changes no byte
   - Expected: blob != "" is true
   - Expected: decoded != nil is true
   - Expected: again.len() equals `blob.len()`
   - Expected: again == blob is true
   - Expected: decoded.unwrap().functions.len() equals `hm.functions.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: the seam between chunks changes no byte")
val hm = lower(gen(3, 30))
val blob = hir_module_encode(hm)
expect(blob != "").to_equal(true)
val decoded = hir_module_decode(blob)
expect(decoded != nil).to_equal(true)
val again = hir_module_encode(decoded.unwrap())
expect(again.len()).to_equal(blob.len())
expect(again == blob).to_equal(true)
expect(decoded.unwrap().functions.len()).to_equal(hm.functions.len())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e74233d49d6ae4ea46cdd7189a54ec88d4202e1c86e929f70b5895986df0411a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e74233d49d6ae4ea46cdd7189a54ec88d4202e1c86e929f70b5895986df0411a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e74233d49d6ae4ea46cdd7189a54ec88d4202e1c86e929f70b5895986df0411a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds the cloned array: parts never exceeds one chunk, and chunks are really sealed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes in time linear in module size, not quadratic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chunking is invisible in the output: re-encode is byte-identical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/hir/hir_codec_writer_chunked_cost_spec.spl. -->
