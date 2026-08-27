# Engine Coverage Closure Specification

> Tests covering engine2d_env_get, engine2d_shutdown_has_typed_route, engine2d_scale_pixel_alpha, engine2d_default_font_config_for.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Coverage Closure Specification

## Scenarios

### engine2d_env_get

#### returns the value of a variable this test process just set

- returns the value of a variable this test process just set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the value of a variable this test process just set")
rt_env_set("ENGINE2D_COV_PROBE", "closure-value")
assert_equal(engine2d_env_get("ENGINE2D_COV_PROBE"), "closure-value")
rt_env_set("ENGINE2D_COV_PROBE", "")
```

</details>

#### returns empty text for a variable that was cleared

- returns empty text for a variable that was cleared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty text for a variable that was cleared")
rt_env_set("ENGINE2D_COV_PROBE_UNSET", "")
assert_equal(engine2d_env_get("ENGINE2D_COV_PROBE_UNSET"), "")
```

</details>

### engine2d_shutdown_has_typed_route

#### is true for every documented typed-route backend name

- is true for every documented typed-route backend name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is true for every documented typed-route backend name")
assert_true(engine2d_shutdown_has_typed_route("vulkan"))
assert_true(engine2d_shutdown_has_typed_route("vulkan-poisoned-software"))
assert_true(engine2d_shutdown_has_typed_route("cuda"))
assert_true(engine2d_shutdown_has_typed_route("metal"))
assert_true(engine2d_shutdown_has_typed_route("opencl"))
assert_true(engine2d_shutdown_has_typed_route("rocm"))
assert_true(engine2d_shutdown_has_typed_route("software"))
```

</details>

#### is false for a name outside the typed-route set

- is false for a name outside the typed-route set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false for a name outside the typed-route set")
assert_false(engine2d_shutdown_has_typed_route("cpu"))
assert_false(engine2d_shutdown_has_typed_route("directx"))
assert_false(engine2d_shutdown_has_typed_route(""))
```

</details>

### engine2d_scale_pixel_alpha

#### halves alpha at opacity_milli=500 and leaves r/g/b untouched

- halves alpha at opacity_milli=500 and leaves r/g/b untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("halves alpha at opacity_milli=500 and leaves r/g/b untouched")
val px = rgba(10, 20, 30, 200)
val out = engine2d_scale_pixel_alpha([px], 500)
assert_equal(out.len(), 1)
assert_equal(color_r(out[0]), 10)
assert_equal(color_g(out[0]), 20)
assert_equal(color_b(out[0]), 30)
assert_equal(color_a(out[0]), 100)
```

</details>

#### is a no-op at opacity_milli=1000 (full opacity)

- is a no-op at opacity_milli=1000 (full opacity)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a no-op at opacity_milli=1000 (full opacity)")
val px = rgba(1, 2, 3, 250)
val out = engine2d_scale_pixel_alpha([px], 1000)
assert_equal(color_a(out[0]), 250)
```

</details>

#### zeroes alpha at opacity_milli=0 across multiple pixels

- zeroes alpha at opacity_milli=0 across multiple pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zeroes alpha at opacity_milli=0 across multiple pixels")
val px_a = rgba(5, 6, 7, 100)
val px_b = rgba(8, 9, 10, 40)
val out = engine2d_scale_pixel_alpha([px_a, px_b], 0)
assert_equal(out.len(), 2)
assert_equal(color_a(out[0]), 0)
assert_equal(color_a(out[1]), 0)
# r/g/b of the second pixel still pass through unchanged.
assert_equal(color_r(out[1]), 8)
assert_equal(color_g(out[1]), 9)
assert_equal(color_b(out[1]), 10)
```

</details>

#### returns an empty array for an empty input

- returns an empty array for an empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty array for an empty input")
val out = engine2d_scale_pixel_alpha([], 500)
assert_equal(out.len(), 0)
```

</details>

### engine2d_default_font_config_for

#### pins execution_target to cpu when force_cpu_target is true

- pins execution_target to cpu when force_cpu_target is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins execution_target to cpu when force_cpu_target is true")
val cfg = engine2d_default_font_config_for(14, true)
assert_equal(cfg.execution_target, "cpu")
assert_equal(cfg.size, 14)
```

</details>

#### leaves execution_target at the base auto value when force_cpu_target is false

- leaves execution_target at the base auto value when force_cpu_target is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves execution_target at the base auto value when force_cpu_target is false")
val cfg = engine2d_default_font_config_for(20, false)
assert_equal(cfg.execution_target, "auto")
assert_equal(cfg.size, 20)
```

</details>

#### preserves every other base field when forcing cpu (only execution_target changes)

- preserves every other base field when forcing cpu (only execution_target changes)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves every other base field when forcing cpu (only execution_target changes)")
val forced = engine2d_default_font_config_for(16, true)
val base = engine2d_default_font_config_for(16, false)
assert_equal(forced.family, base.family)
assert_equal(forced.category, base.category)
assert_equal(forced.language, base.language)
assert_equal(forced.script, base.script)
assert_equal(forced.weight, base.weight)
assert_equal(forced.style, base.style)
assert_equal(forced.hinting, base.hinting)
assert_equal(forced.antialiasing, base.antialiasing)
assert_equal(forced.atlas_policy, base.atlas_policy)
assert_true(forced.execution_target != base.execution_target)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering engine2d_env_get, engine2d_shutdown_has_typed_route, engine2d_scale_pixel_alpha, engine2d_default_font_config_for.
- engine2d_env_get
- engine2d_shutdown_has_typed_route
- engine2d_scale_pixel_alpha
- engine2d_default_font_config_for

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `a5804cd7ba528af35b0003ef206d5ff0bc0e99342cc51ea2c3936a7eca0d0408`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5804cd7ba528af35b0003ef206d5ff0bc0e99342cc51ea2c3936a7eca0d0408`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5804cd7ba528af35b0003ef206d5ff0bc0e99342cc51ea2c3936a7eca0d0408`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the value of a variable this test process just set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty text for a variable that was cleared' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine_coverage_closure_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is true for every documented typed-route backend name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
