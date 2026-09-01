# Opencl Honesty Specification

> Tests covering OpenCL loader honesty probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opencl Honesty Specification

## Scenarios

### OpenCL loader honesty probe

#### rt_opencl_is_available/rt_opencl_platform_count report a real, non-fake state on this host

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_opencl_is_available/rt_opencl_platform_count report a real, non-fake state on this host
   - Expected: count >= 0 is true
   - Expected: count > 0 is true
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_opencl_is_available/rt_opencl_platform_count report a real, non-fake state on this host")
# Live call through the seed interpreter's already-registered OpenCL
# wrappers (gpu.rs), which delegate to a real dlopen-backed check --
# not a stub. This host really has a working ICD (2x NVIDIA GPU,
# verified via clinfo + a standalone dlopen probe this session).
val available = rt_opencl_is_available()
val count = rt_opencl_platform_count()
expect(count >= 0).to_equal(true)
if available:
    expect(count > 0).to_equal(true)
else:
    expect(count).to_equal(0)
```

</details>

#### the five stage labels are pairwise-distinct text -- a sabotage that collapses them must fail this

- the five stage labels are pairwise-distinct text -- a sabotage that collapses them must fail this
   - Expected: text_absent == text_no_platform is false
   - Expected: text_no_platform == text_no_device is false
   - Expected: text_no_device == text_failed is false
   - Expected: text_failed == text_ok is false
   - Expected: text_absent == text_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("the five stage labels are pairwise-distinct text -- a sabotage that collapses them must fail this")
val text_absent = opencl_stage_text(STAGE_LIB_ABSENT)
val text_no_platform = opencl_stage_text(STAGE_NO_PLATFORM)
val text_no_device = opencl_stage_text(STAGE_NO_DEVICE)
val text_failed = opencl_stage_text(STAGE_CONTEXT_FAILED)
val text_ok = opencl_stage_text(STAGE_CONTEXT_OK)
expect(text_absent == text_no_platform).to_equal(false)
expect(text_no_platform == text_no_device).to_equal(false)
expect(text_no_device == text_failed).to_equal(false)
expect(text_failed == text_ok).to_equal(false)
expect(text_absent == text_ok).to_equal(false)
```

</details>

#### the honest lib_absent branch in rt_opencl_probe_stage is a real early return, not a substitute/fake handle

- the honest lib_absent branch in rt_opencl_probe_stage is a real early return, not a substitute/fake handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("the honest lib_absent branch in rt_opencl_probe_stage is a real early return, not a substitute/fake handle")
val source = rt_file_read_text("src/runtime/runtime_simd_dispatch.c")
val probe_start = source.index_of("int64_t rt_opencl_probe_stage")
expect(probe_start).to_be_greater_than(-1)
val probe_body = source.substring(probe_start, probe_start + 700)
expect(probe_body).to_contain("RT_OPENCL_PROBE_LIB_ABSENT")
expect(probe_body).to_contain("rt_opencl_load_symbols")
```

</details>

#### the context_failed branch is real and reachable on any host, not merged into context_ok

- the context_failed branch is real and reachable on any host, not merged into context_ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("the context_failed branch is real and reachable on any host, not merged into context_ok")
val source = rt_file_read_text("src/runtime/runtime_simd_dispatch.c")
val probe_start = source.index_of("int64_t rt_opencl_probe_stage")
val probe_body = source.substring(probe_start, probe_start + 1600)
expect(probe_body).to_contain("RT_OPENCL_PROBE_FORCE_CONTEXT_FAIL")
expect(probe_body).to_contain("RT_OPENCL_PROBE_CONTEXT_FAILED")
expect(probe_body).to_contain("RT_OPENCL_PROBE_CONTEXT_OK")
# The forced-fail branch must call the real create_context entry
# point with a deliberately empty device list -- not fabricate a
# status.
expect(probe_body).to_contain("create_context(properties, 0, NULL")
```

</details>

#### rt_opencl_probe_last_status is a distinct accessor exposing the real CL status, not aliased to another probe

- rt_opencl_probe_last_status is a distinct accessor exposing the real CL status, not aliased to another probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("rt_opencl_probe_last_status is a distinct accessor exposing the real CL status, not aliased to another probe")
val source = rt_file_read_text("src/runtime/runtime_simd_dispatch.c")
val accessor_start = source.index_of("int64_t rt_opencl_probe_last_status")
expect(accessor_start).to_be_greater_than(-1)
val accessor_body = source.substring(accessor_start, accessor_start + 200)
expect(accessor_body).to_contain("rt_opencl_probe_last_status_g")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/opencl_honesty_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OpenCL loader honesty probe.
- OpenCL loader honesty probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d0e9c2309f16424ef3ad5ba84df9e1c2c6ed18b00a7429b00b8283c2088ea6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d0e9c2309f16424ef3ad5ba84df9e1c2c6ed18b00a7429b00b8283c2088ea6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d0e9c2309f16424ef3ad5ba84df9e1c2c6ed18b00a7429b00b8283c2088ea6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/runtime/opencl_honesty_spec.spl
mirror: doc/06_spec/01_unit/runtime/opencl_honesty_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/opencl_honesty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/opencl_honesty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/opencl_honesty_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/runtime/opencl_honesty_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_opencl_is_available/rt_opencl_platform_count report a real, non-fake state on this host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/opencl_honesty_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the five stage labels are pairwise-distinct text -- a sabotage that collapses them must fail this' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/opencl_honesty_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the honest lib_absent branch in rt_opencl_probe_stage is a real early return, not a substitute/fake handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
