# Engine2d Env Backend Select Specification

> Tests covering Engine2D config/environment backend selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Env Backend Select Specification

## Scenarios

### Engine2D config/environment backend selection

#### reads the SIMPLE_2D_BACKEND override

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the SIMPLE_2D_BACKEND override
   - Expected: engine2d_env_backend_override() equals `software`
   - Expected: engine2d_env_backend_override() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads the SIMPLE_2D_BACKEND override")
rt_env_set("SIMPLE_2D_BACKEND", "software")
expect(engine2d_env_backend_override()).to_equal("software")
rt_env_set("SIMPLE_2D_BACKEND", "")
expect(engine2d_env_backend_override()).to_equal("")
```

</details>

#### honors an available override backend (software always initializes)

- honors an available override backend (software always initializes)
   - Expected: Engine2D.detect_best_backend() equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("honors an available override backend (software always initializes)")
rt_env_set("SIMPLE_2D_BACKEND", "software")
expect(Engine2D.detect_best_backend()).to_equal("software")
rt_env_set("SIMPLE_2D_BACKEND", "")
```

</details>

#### falls through to auto-probe when the override is unavailable

- falls through to auto-probe when the override is unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls through to auto-probe when the override is unavailable")
# A GPU lane that cannot init on this host must not be forced — the same
# API gracefully auto-selects an available lane instead of failing.
rt_env_set("SIMPLE_2D_BACKEND", "no_such_backend_xyz")
val selected = Engine2D.detect_best_backend()
expect(selected).to_not_equal("no_such_backend_xyz")
expect(selected.len()).to_be_greater_than(0)
rt_env_set("SIMPLE_2D_BACKEND", "")
```

</details>

#### auto-selects a non-empty backend with no override

- auto-selects a non-empty backend with no override


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-selects a non-empty backend with no override")
rt_env_set("SIMPLE_2D_BACKEND", "")
expect(Engine2D.detect_best_backend().len()).to_be_greater_than(0)
```

</details>

#### requested+honored: SIMPLE_2D_BACKEND=cpu_simd is honored by name (compat) but reports itself honestly as a scalar-CPU alias

- requested+honored: SIMPLE_2D_BACKEND=cpu_simd is honored by name (compat) but reports itself honestly as a scalar-CPU alias
   - Expected: selected equals `cpu_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requested+honored: SIMPLE_2D_BACKEND=cpu_simd is honored by name (compat) but reports itself honestly as a scalar-CPU alias")
rt_env_set("SIMPLE_2D_BACKEND", "cpu_simd")
val selected = Engine2D.detect_best_backend()
# Config compat: the alias name is still accepted and honored.
expect(selected).to_equal("cpu_simd")
val display = backend_display_name(selected)
val gate = feature_gate_description(selected)
# Positive: the report must state there is no live SIMD dispatch.
expect(display).to_contain("no live SIMD dispatch")
expect(gate).to_contain("no live SIMD dispatch")
# Negative: the old dishonest bare claims must be gone.
expect(display).to_not_equal("CPU SIMD")
expect(gate).to_not_contain("uses CPU SIMD when available")
rt_env_set("SIMPLE_2D_BACKEND", "")
```

</details>

#### requested+fallback: an arch-specific SIMD request the engine cannot honor falls back without ever claiming live SIMD

- requested+fallback: an arch-specific SIMD request the engine cannot honor falls back without ever claiming live SIMD


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requested+fallback: an arch-specific SIMD request the engine cannot honor falls back without ever claiming live SIMD")
# "cpu_simd_x86" is not a distinct render backend in Engine2D's own
# create_requested_backend/probe_backend (only backend_probe.spl's
# separate compute-dispatch prober models the arch-specific variants),
# so requesting it here is always unavailable and forces the auto-probe
# fallback path — mirroring the existing "falls through" case above.
rt_env_set("SIMPLE_2D_BACKEND", "cpu_simd_x86")
val selected = Engine2D.detect_best_backend()
expect(selected).to_not_equal("cpu_simd_x86")
expect(selected.len()).to_be_greater_than(0)
# Whatever backend actually wins the fallback, the shared cpu_simd
# descriptor itself (queried directly, so this is host-independent and
# not just an incidental pass) must never claim live SIMD dispatch.
expect(backend_display_name("cpu_simd")).to_contain("no live SIMD dispatch")
expect(feature_gate_description("cpu_simd")).to_contain("no live SIMD dispatch")
expect(backend_display_name("cpu_simd")).to_not_equal("CPU SIMD")
rt_env_set("SIMPLE_2D_BACKEND", "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D config/environment backend selection.
- Engine2D config/environment backend selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `6aa911830516168ed60b2f46e37b66fb0a30db26d836411cc7ff1dbbd90f8822`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6aa911830516168ed60b2f46e37b66fb0a30db26d836411cc7ff1dbbd90f8822`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6aa911830516168ed60b2f46e37b66fb0a30db26d836411cc7ff1dbbd90f8822`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the SIMPLE_2D_BACKEND override' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'honors an available override backend (software always initializes)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_env_backend_select_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls through to auto-probe when the override is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
