# Shadow Mode Specification

> Tests covering cache v2 shadow mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shadow Mode Specification

## Scenarios

### cache v2 shadow mode

#### is off by default with zero side effects

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is off by default with zero side effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is off by default with zero side effects")
rt_env_set("SIMPLE_CACHE_V2_SHADOW", "")
shadow_reset_counters()
val ws = fresh_workspace("off")
val inputs = make_module(ws, "mod_off")
val lookup = shadow_on_compile_start(inputs)
assert_false(shadow_enabled())
assert_false(lookup.enabled)
shadow_on_compile_done(lookup, [make_output(ws, "mod_off", "bytes")])
val counts = shadow_counts()
assert_eq(counts[0], 0)
assert_eq(counts[1], 0)
assert_eq(counts[2], 0)
assert_eq(counts[3], 0)
# No v2 store was created in the workspace.
assert_false(rt_dir_exists("{ws}/.simple/build-cache"))
```

</details>

#### publishes on miss and hits exactly on the second run

- publishes on miss and hits exactly on the second run


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes on miss and hits exactly on the second run")
rt_env_set("SIMPLE_CACHE_V2_SHADOW", "1")
rt_env_set("SIMPLE_CACHE", "")
shadow_reset_counters()
val ws = fresh_workspace("misshit")
val inputs = make_module(ws, "mod_a")
val out = make_output(ws, "mod_a", "compiled-bytes-a")

# First run: miss -> publish.
val first = shadow_on_compile_start(inputs)
assert_true(first.enabled)
assert_false(first.hit)
shadow_on_compile_done(first, [out])
val after_first = shadow_counts()
assert_eq(after_first[1], 1)

# Second run of the SAME action: exact hit with matching bytes.
val second = shadow_on_compile_start(inputs)
assert_true(second.hit)
shadow_on_compile_done(second, [out])
val after_second = shadow_counts()
assert_eq(after_second[0], 1)
assert_eq(after_second[1], 1)
assert_eq(after_second[2], 0)
assert_eq(after_second[3], 0)
```

</details>

#### counts a byte divergence as shadow_mismatch, never obeys the cache

- counts a byte divergence as shadow_mismatch, never obeys the cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts a byte divergence as shadow_mismatch, never obeys the cache")
rt_env_set("SIMPLE_CACHE_V2_SHADOW", "1")
rt_env_set("SIMPLE_CACHE", "")
shadow_reset_counters()
val ws = fresh_workspace("mismatch")
val inputs = make_module(ws, "mod_b")
val out = make_output(ws, "mod_b", "compiled-bytes-b")

val first = shadow_on_compile_start(inputs)
shadow_on_compile_done(first, [out])

# Same key, but the fresh compile now produced DIFFERENT bytes.
val diverged = make_output(ws, "mod_b_div", "compiled-bytes-DIVERGED")
val second = shadow_on_compile_start(inputs)
assert_true(second.hit)
shadow_on_compile_done(second, [diverged])
val counts = shadow_counts()
assert_eq(counts[2], 1)
assert_eq(counts[0], 0)
```

</details>

#### swallows a v2 internal failure without propagating

- swallows a v2 internal failure without propagating


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("swallows a v2 internal failure without propagating")
rt_env_set("SIMPLE_CACHE_V2_SHADOW", "1")
rt_env_set("SIMPLE_CACHE", "")
shadow_reset_counters()
val ws = fresh_workspace("err")
val src = "{ws}/mod_c.spl"
rt_file_write_text(src, "fn main_c(): 1")
# Unwritable workspace root: every CAS write fails inside v2.
val inputs = ShadowActionInputs(
    workspace_root: "/proc/no_such_cache_root",
    source: src, dependencies: [])
val lookup = shadow_on_compile_start(inputs)
shadow_on_compile_done(lookup, [make_output(ws, "mod_c", "bytes-c")])
# Reaching here at all is the point: no failure propagated.
val counts = shadow_counts()
assert_true(counts[3] >= 1)
assert_eq(counts[0], 0)
assert_eq(counts[1], 0)
shadow_report()
rt_env_set("SIMPLE_CACHE_V2_SHADOW", "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache_v2/shadow_mode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cache v2 shadow mode.
- cache v2 shadow mode

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b76f3b3c9bb1f32a1cd86557ba3d3b033281f523177c228e17b76b9f9349efac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b76f3b3c9bb1f32a1cd86557ba3d3b033281f523177c228e17b76b9f9349efac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b76f3b3c9bb1f32a1cd86557ba3d3b033281f523177c228e17b76b9f9349efac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/cache_v2/shadow_mode_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache_v2/shadow_mode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache_v2/shadow_mode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache_v2/shadow_mode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache_v2/shadow_mode_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is off by default with zero side effects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/shadow_mode_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes on miss and hits exactly on the second run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache_v2/shadow_mode_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts a byte divergence as shadow_mismatch, never obeys the cache' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
