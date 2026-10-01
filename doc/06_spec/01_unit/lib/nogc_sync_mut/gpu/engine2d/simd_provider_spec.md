# Simd Provider Specification

> Tests covering simd_provider — registry (absent state, checked before any registration in this process), simd_provider — registry (after registration), simd_provider — hit-count accumulator, simd_provider — SimdProvider trait dispatch (via CpuSimdProvider).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Provider Specification

## Scenarios

### simd_provider — registry (absent state, checked before any registration in this process)

#### no provider registered reports absent with empty name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- no provider registered reports absent with empty name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no provider registered reports absent with empty name")
assert_false(has_registered_provider())
assert_equal(registered_provider_name(), "")
```

</details>

### simd_provider — registry (after registration)

#### register then query returns name and true

- register then query returns name and true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register then query returns name and true")
register_simd_provider("cpu-simd-v1")
assert_true(has_registered_provider())
assert_equal(registered_provider_name(), "cpu-simd-v1")
```

</details>

#### re-registering overwrites the previous name

- re-registering overwrites the previous name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-registering overwrites the previous name")
register_simd_provider("cpu-simd-v2")
assert_true(has_registered_provider())
assert_equal(registered_provider_name(), "cpu-simd-v2")
```

</details>

### simd_provider — hit-count accumulator

#### reset zeroes all counters

- reset zeroes all counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset zeroes all counters")
record_simd_fill_hit()
record_simd_copy_hit()
reset_simd_hits()
val c = simd_hit_counts()
assert_equal(c.fill_hits, 0)
assert_equal(c.copy_hits, 0)
assert_equal(c.alpha_hits, 0)
assert_equal(c.blit_hits, 0)
assert_equal(c.scroll_hits, 0)
assert_equal(c.vectorize_changes, 0)
```

</details>

#### each record_*_hit increments exactly its counter

- each record_*_hit increments exactly its counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each record_*_hit increments exactly its counter")
reset_simd_hits()
record_simd_fill_hit()
val after_fill = simd_hit_counts()
assert_equal(after_fill.fill_hits, 1)
assert_equal(after_fill.copy_hits, 0)
assert_equal(after_fill.alpha_hits, 0)
assert_equal(after_fill.blit_hits, 0)
assert_equal(after_fill.scroll_hits, 0)

record_simd_copy_hit()
val after_copy = simd_hit_counts()
assert_equal(after_copy.fill_hits, 1)
assert_equal(after_copy.copy_hits, 1)
assert_equal(after_copy.alpha_hits, 0)

record_simd_alpha_hit()
val after_alpha = simd_hit_counts()
assert_equal(after_alpha.alpha_hits, 1)
assert_equal(after_alpha.blit_hits, 0)

record_simd_blit_hit()
val after_blit = simd_hit_counts()
assert_equal(after_blit.blit_hits, 1)
assert_equal(after_blit.scroll_hits, 0)

record_simd_scroll_hit()
val after_scroll = simd_hit_counts()
assert_equal(after_scroll.scroll_hits, 1)
# None of the other counters moved from the prior single-hit
# values, confirming no cross-wiring between counters.
assert_equal(after_scroll.fill_hits, 1)
assert_equal(after_scroll.copy_hits, 1)
assert_equal(after_scroll.alpha_hits, 1)
assert_equal(after_scroll.blit_hits, 1)
```

</details>

#### repeated record_simd_fill_hit calls accumulate, not saturate

- repeated record_simd_fill_hit calls accumulate, not saturate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated record_simd_fill_hit calls accumulate, not saturate")
reset_simd_hits()
record_simd_fill_hit()
record_simd_fill_hit()
record_simd_fill_hit()
assert_equal(simd_hit_counts().fill_hits, 3)
```

</details>

#### vectorize_change events are counted separately from hits

- vectorize_change events are counted separately from hits


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vectorize_change events are counted separately from hits")
reset_simd_hits()
record_simd_fill_hit()
record_simd_vectorize_change()
record_simd_vectorize_change()
val c = simd_hit_counts()
assert_equal(c.fill_hits, 1)
assert_equal(c.vectorize_changes, 2)
```

</details>

#### make_simd_hit_counts_zero constructs an all-zero snapshot independent of module state

- make_simd_hit_counts_zero constructs an all-zero snapshot independent of module state


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("make_simd_hit_counts_zero constructs an all-zero snapshot independent of module state")
reset_simd_hits()
record_simd_fill_hit()
record_simd_vectorize_change()
val zero = make_simd_hit_counts_zero()
assert_equal(zero.fill_hits, 0)
assert_equal(zero.copy_hits, 0)
assert_equal(zero.alpha_hits, 0)
assert_equal(zero.blit_hits, 0)
assert_equal(zero.scroll_hits, 0)
assert_equal(zero.vectorize_changes, 0)
# And it did not disturb the live singleton counters.
val live = simd_hit_counts()
assert_equal(live.fill_hits, 1)
assert_equal(live.vectorize_changes, 1)
```

</details>

### simd_provider — SimdProvider trait dispatch (via CpuSimdProvider)

#### target_features() returns a non-empty feature list from the real provider

- target_features() returns a non-empty feature list from the real provider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("target_features() returns a non-empty feature list from the real provider")
val provider = make_cpu_simd_provider()
val feats = provider.target_features()
assert_true(feats.len() > 0)
```

</details>

#### hit_counts() on the trait reflects the same module-level singleton as simd_hit_counts()

- hit_counts() on the trait reflects the same module-level singleton as simd_hit_counts()


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hit_counts() on the trait reflects the same module-level singleton as simd_hit_counts()")
reset_simd_hits()
record_simd_copy_hit()
record_simd_copy_hit()
val provider = make_cpu_simd_provider()
val via_trait = provider.hit_counts()
val via_module = simd_hit_counts()
assert_equal(via_trait.copy_hits, via_module.copy_hits)
assert_equal(via_trait.copy_hits, 2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simd_provider — registry (absent state, checked before any registration in this process), simd_provider — registry (after registration), simd_provider — hit-count accumulator, simd_provider — SimdProvider trait dispatch (via CpuSimdProvider).
- simd_provider — registry (absent state, checked before any registration in this process)
- simd_provider — registry (after registration)
- simd_provider — hit-count accumulator
- simd_provider — SimdProvider trait dispatch (via CpuSimdProvider)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1a5c7e348d190e215175422fc979a9a81cd1fd9e072a4ca6688f44327bb18a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1a5c7e348d190e215175422fc979a9a81cd1fd9e072a4ca6688f44327bb18a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1a5c7e348d190e215175422fc979a9a81cd1fd9e072a4ca6688f44327bb18a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no provider registered reports absent with empty name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'register then query returns name and true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_provider_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-registering overwrites the previous name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
