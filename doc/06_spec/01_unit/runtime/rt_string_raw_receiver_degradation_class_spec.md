# Rt String Raw Receiver Degradation Class Specification

> Tests covering no runtime string primitive silently degrades on a raw receiver.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rt String Raw Receiver Degradation Class Specification

## Scenarios

### no runtime string primitive silently degrades on a raw receiver

#### proves the census actually detects the defect signature

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- proves the census actually detects the defect signature
- Write a fixture carrying the exact pre-fix shape of rt_string_trim
- The census must flag the fixture by name
- Clean up the control fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("proves the census actually detects the defect signature")
# Anti-vacuity positive control. "A scan that finds nothing may have
# scanned nothing" — so before trusting a clean result, the same scanner
# must produce a hit against a fixture that deliberately carries the
# defect. If this control is silent, the scan is broken, not the runtime.
step("Write a fixture carrying the exact pre-fix shape of rt_string_trim")
val fixture = "/tmp/rt_string_raw_receiver_class_control.c"
val write = "printf '%s\\n' 'int64_t rt_string_fixture_victim(int64_t value) {' " +
    "'    RtCoreString* s = rt_core_as_string(value);' " +
    "'    if (!s) return value;' '    return value;' '}' > " + fixture
sh(write)

step("The census must flag the fixture by name")
val found = sh(CENSUS_AWK + fixture)
expect(found).to_contain("SILENT rt_string_fixture_victim")

step("Clean up the control fixture")
sh("rm -f " + fixture)
```

</details>

#### reports no silently-degrading string primitive in the shipped runtime

- reports no silently-degrading string primitive in the shipped runtime
- Confirm the runtime source was actually read — a census over a missing or empty path would report zero offenders and look identical to a pass
   - Expected: headers does not contain `0\n`
- Run the census over the real runtime — the offender list must be empty
   - Expected: offenders does not contain `SILENT `


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("reports no silently-degrading string primitive in the shipped runtime")
step("Confirm the runtime source was actually read — a census over a missing or empty path would report zero offenders and look identical to a pass")
val headers = sh("grep -c '^\\(static \\)\\?int64_t rt_string_[a-z_0-9]*(' " + RUNTIME_C)
expect(headers.contains("0\n")).to_equal(false)

step("Run the census over the real runtime — the offender list must be empty")
val offenders = sh(CENSUS_AWK + RUNTIME_C)
expect(offenders.contains("SILENT ")).to_equal(false)
```

</details>

#### keeps the shared promotion helper defined and actually used

- keeps the shared promotion helper defined and actually used
- The helper must exist — every promoting call site is dead weight without it
- The originally-filed four must each promote, not just the siblings found later
   - Expected: trim does not contain `0\n`
- A raw receiver below the 0x10000 floor is nil/bool/small-int and must never be dereferenced as a pointer


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("keeps the shared promotion helper defined and actually used")
step("The helper must exist — every promoting call site is dead weight without it")
val defined = sh("grep -c 'static int rt_string_promote_raw_receiver(int64_t value, int64_t\\* out) {' " + RUNTIME_C)
expect(defined).to_contain("1")

step("The originally-filed four must each promote, not just the siblings found later")
val trim = sh("grep -c 'rt_string_promote_raw_receiver' " + RUNTIME_C)
expect(trim.contains("0\n")).to_equal(false)

step("A raw receiver below the 0x10000 floor is nil/bool/small-int and must never be dereferenced as a pointer")
val floor = sh("grep -c 'if (value < 0x10000) return 0;' " + RUNTIME_C)
expect(floor).to_contain("1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering no runtime string primitive silently degrades on a raw receiver.
- no runtime string primitive silently degrades on a raw receiver

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

- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3fa95e9fbefacffda3856d93a66cdea4b6fa1bebfd3491f6cdd410e927b3abef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fa95e9fbefacffda3856d93a66cdea4b6fa1bebfd3491f6cdd410e927b3abef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fa95e9fbefacffda3856d93a66cdea4b6fa1bebfd3491f6cdd410e927b3abef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.spl
mirror: doc/06_spec/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves the census actually detects the defect signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no silently-degrading string primitive in the shipped runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/rt_string_raw_receiver_degradation_class_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the shared promotion helper defined and actually used' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
