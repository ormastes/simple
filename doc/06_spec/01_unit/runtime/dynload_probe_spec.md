# Dynload Probe Specification

> Tests covering spl_dlopen / spl_dlsym / spl_dlclose (N0 single-definition probe).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynload Probe Specification

## Scenarios

### spl_dlopen / spl_dlsym / spl_dlclose (N0 single-definition probe)

#### opens a real system library (libm.so.6) and returns a non-zero handle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens a real system library (libm.so.6) and returns a non-zero handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("opens a real system library (libm.so.6) and returns a non-zero handle")
val handle = spl_dlopen("libm.so.6")
expect(handle).to_be_greater_than(0)
# dlclose here only to not leak the handle across examples; the
# dedicated dlclose example below opens its own handle.
spl_dlclose(handle)
```

</details>

#### resolves a real exported symbol (cos) to a non-zero function pointer

- resolves a real exported symbol (cos) to a non-zero function pointer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("resolves a real exported symbol (cos) to a non-zero function pointer")
val handle = spl_dlopen("libm.so.6")
expect(handle).to_be_greater_than(0)
val sym = spl_dlsym(handle, "cos")
expect(sym).to_be_greater_than(0)
spl_dlclose(handle)
```

</details>

#### reports an HONEST negative for a library that does not exist -- never a fake handle

- reports an HONEST negative for a library that does not exist -- never a fake handle
   - Expected: handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("reports an HONEST negative for a library that does not exist -- never a fake handle")
val handle = spl_dlopen("libdefinitely_absent_xyz.so")
expect(handle).to_equal(0)
```

</details>

#### spl_dlclose succeeds (returns 0) on a handle opened by spl_dlopen

- spl_dlclose succeeds (returns 0) on a handle opened by spl_dlopen
   - Expected: closed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("spl_dlclose succeeds (returns 0) on a handle opened by spl_dlopen")
val handle = spl_dlopen("libm.so.6")
expect(handle).to_be_greater_than(0)
val closed = spl_dlclose(handle)
expect(closed).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/dynload_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spl_dlopen / spl_dlsym / spl_dlclose (N0 single-definition probe).
- spl_dlopen / spl_dlsym / spl_dlclose (N0 single-definition probe)

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

- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c83bcd6e6ec4f9453ca2f5182dd482a04bbe494a19b12b9eb967ee7e83f54f7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c83bcd6e6ec4f9453ca2f5182dd482a04bbe494a19b12b9eb967ee7e83f54f7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c83bcd6e6ec4f9453ca2f5182dd482a04bbe494a19b12b9eb967ee7e83f54f7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/runtime/dynload_probe_spec.spl
mirror: doc/06_spec/01_unit/runtime/dynload_probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/dynload_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/dynload_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/dynload_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/runtime/dynload_probe_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens a real system library (libm.so.6) and returns a non-zero handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/dynload_probe_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a real exported symbol (cos) to a non-zero function pointer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/dynload_probe_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports an HONEST negative for a library that does not exist -- never a fake handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
