# CH32V307 Composite Runner Path Regression

> Verifies that the CH32V307 composite runner no longer short-circuits through the old placeholder path and now routes `jit(remote(baremetal(ch32v307)))` through the real adapter-backed execution flow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CH32V307 Composite Runner Path Regression

Verifies that the CH32V307 composite runner no longer short-circuits through the old placeholder path and now routes `jit(remote(baremetal(ch32v307)))` through the real adapter-backed execution flow.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-013 |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md) |
| Design | [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md) |
| Research | N/A |
| Source | `test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the CH32V307 composite runner no longer short-circuits through
the old placeholder path and now routes `jit(remote(baremetal(ch32v307)))`
through the real adapter-backed execution flow.

This spec is intentionally host-aware:

- if `wlink` or the probe is unavailable, the runner must skip cleanly
- if hardware is available, the composite runner must take the real CH32
  adapter path
- the result must not regress to the old "not implemented" message

This file is the authoritative regression for composite-runner wiring. The
direct `wlink` readiness and SDI-output probe remains covered separately by
`ch32v307_composite_runner_spec.spl`.

## Syntax

```simple
use std.spec.step

val result = run_test_file_jit_ch32v307(
    "test/fixtures/remote_jit/baremetal_lib_workload_main.spl",
    source,
    default_options()
)
```

## Examples

```simple
expect(result.error.contains("not implemented")).to_equal(false)
expect(result.skipped).to_equal(0)
```

## Scenarios

### CH32V307 composite runner path

<details>
<summary>Advanced: does not return the old not-implemented placeholder</summary>

#### does not return the old not-implemented placeholder _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not return the old not-implemented placeholder
   - Expected: result.error does not contain `not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not return the old not-implemented placeholder")
val source = file_read(SHARED_WORKLOAD)
val result = run_test_file_jit_ch32v307(SHARED_WORKLOAD, source, default_options())
expect(result.error.contains("not implemented")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: skips cleanly when wlink or hardware is unavailable</summary>

#### skips cleanly when wlink or hardware is unavailable _(slow)_

- skips cleanly when wlink or hardware is unavailable
   - Expected: result.skipped equals `1`
   - Expected: result.failed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("skips cleanly when wlink or hardware is unavailable")
if wlink_available() and ch32v307_detected():
    print "[skip] live hardware path available on this host"
    return
val source = file_read(SHARED_WORKLOAD)
val result = run_test_file_jit_ch32v307(SHARED_WORKLOAD, source, default_options())
expect(result.skipped).to_equal(1)
expect(result.failed).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: uses the real adapter-backed execution path when hardware is available</summary>

#### uses the real adapter-backed execution path when hardware is available _(slow)_

- uses the real adapter-backed execution path when hardware is available
   - Expected: result.skipped equals `0`
   - Expected: result.error does not contain `not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the real adapter-backed execution path when hardware is available")
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
val source = file_read(SHARED_WORKLOAD)
val result = run_test_file_jit_ch32v307(SHARED_WORKLOAD, source, default_options())
expect(result.skipped).to_equal(0)
expect(result.error.contains("not implemented")).to_equal(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `[doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md)`
- **Design:** `[doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2baaf051c6faebe1b2a48904a219408f72e043bfc2bae16aafc6b583e072e6c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2baaf051c6faebe1b2a48904a219408f72e043bfc2bae16aafc6b583e072e6c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2baaf051c6faebe1b2a48904a219408f72e043bfc2bae16aafc6b583e072e6c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl
mirror: doc/06_spec/02_integration/remote_jit/ch32v307_composite_runner_path_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/remote_jit/ch32v307_composite_runner_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/remote_jit/ch32v307_composite_runner_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not return the old not-implemented placeholder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips cleanly when wlink or hardware is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/remote_jit/ch32v307_composite_runner_path_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the real adapter-backed execution path when hardware is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
