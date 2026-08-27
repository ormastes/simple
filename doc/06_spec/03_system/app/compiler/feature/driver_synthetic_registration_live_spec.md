# Driver Synthetic Registration Live Specification

> Tests covering FR-DRIVER-0001 live synthetic registration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Synthetic Registration Live Specification

## Scenarios

### FR-DRIVER-0001 live synthetic registration

#### executes register_static_driver for a stub-only @driver ops function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes register_static_driver for a stub-only @driver ops function
   - Expected: rt_file_write_text(src, synthetic_driver_source()) is true
   - Expected: code equals `0`
   - Expected: stderr does not contain `driver registration did not increment static registry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes register_static_driver for a stub-only @driver ops function")
val src = "/tmp/simple_driver_synthetic_registration_live.spl"
delete_if_exists(src)
expect(rt_file_write_text(src, synthetic_driver_source())).to_equal(true)

val (stdout, stderr, code) = rt_process_run(simple_cmd(), [src])
expect(code).to_equal(0)
expect(stderr.contains("driver registration did not increment static registry")).to_equal(false)

delete_if_exists(src)
```

</details>

#### executes register_static_driver for a stub-only @native_lib ops function

- executes register_static_driver for a stub-only @native_lib ops function
   - Expected: rt_file_write_text(src, synthetic_native_lib_source()) is true
   - Expected: code equals `0`
   - Expected: stderr does not contain `native-lib registration did not increment static registry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes register_static_driver for a stub-only @native_lib ops function")
val src = "/tmp/simple_native_lib_synthetic_registration_live.spl"
delete_if_exists(src)
expect(rt_file_write_text(src, synthetic_native_lib_source())).to_equal(true)

val (stdout, stderr, code) = rt_process_run(simple_cmd(), [src])
expect(code).to_equal(0)
expect(stderr.contains("native-lib registration did not increment static registry")).to_equal(false)

delete_if_exists(src)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-DRIVER-0001 live synthetic registration.
- FR-DRIVER-0001 live synthetic registration

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b259eef5b47f4122b10946c0bc1e91c0a2a4914c6d2d257f35b1b359ed2405de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b259eef5b47f4122b10946c0bc1e91c0a2a4914c6d2d257f35b1b359ed2405de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b259eef5b47f4122b10946c0bc1e91c0a2a4914c6d2d257f35b1b359ed2405de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes register_static_driver for a stub-only @driver ops function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes register_static_driver for a stub-only @native_lib ops function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
