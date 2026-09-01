# Wine Dll Entrypoint Lifecycle Specification

> Tests covering wine dll entrypoint lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll Entrypoint Lifecycle Specification

## Scenarios

### wine dll entrypoint lifecycle

#### models TLS-before-DllMain ordering without executing DLL code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models TLS-before-DllMain ordering without executing DLL code
   - Expected: result.ok is true
   - Expected: result.dll_name equals `kernel32.dll`
   - Expected: result.entrypoint_rva equals `0x1100`
   - Expected: result.tls_callback_count equals `2`
   - Expected: result.status equals `dll-entrypoint-lifecycle-modeled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("models TLS-before-DllMain ordering without executing DLL code")
val session = wine_dll_load_session_new(0x76000000)
val loaded = wine_dll_session_load_modeled(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x6000)
val result = wine_dll_entrypoint_lifecycle_gate(loaded.dll_name, loaded.status, loaded.evidence, 0x1100, 2, false)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.entrypoint_rva).to_equal(0x1100)
expect(result.tls_callback_count).to_equal(2)
expect(result.status).to_equal("dll-entrypoint-lifecycle-modeled")
expect(result.evidence).to_contain("loader-lock-acquired")
expect(result.evidence).to_contain("tls-callbacks-planned")
expect(result.evidence).to_contain("DllMain-process-attach-planned")
expect(result.evidence).to_contain("dll-entrypoint-execution-blocked")
expect(result.evidence).to_contain("tls-callback-execution-blocked")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### blocks requests to actually execute DllMain or TLS callbacks

- blocks requests to actually execute DllMain or TLS callbacks
   - Expected: result.ok is true
   - Expected: result.status equals `dll-entrypoint-exec-dispatched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks requests to actually execute DllMain or TLS callbacks")
val session = wine_dll_load_session_new(0x77000000)
val loaded = wine_dll_session_load_modeled(session, "kernel32.dll", "C:\\Games", "C:\\Users\\Player", [], ["kernel32.dll"], 0x6000)
val result = wine_dll_entrypoint_lifecycle_gate(loaded.dll_name, loaded.status, loaded.evidence, 0x1100, 1, true)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-entrypoint-exec-dispatched")
expect(result.evidence).to_contain("dll-entrypoint-execution-requested")
expect(result.evidence).to_contain("dll-entrypoint-exec-dispatched")
```

</details>

#### requires a modeled load session and valid lifecycle inputs

- requires a modeled load session and valid lifecycle inputs
   - Expected: missing_load.ok is false
   - Expected: missing_load.error equals `dll-load-session-required:rolled-back`
   - Expected: missing_evidence.error equals `missing-modeled-loaded-image-evidence`
   - Expected: invalid_entry.error equals `invalid-dll-entrypoint-rva`
   - Expected: invalid_tls.error equals `invalid-tls-callback-count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a modeled load session and valid lifecycle inputs")
val missing_load = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "rolled-back", "dll-load-session-created", 0x1100, 0, false)
expect(missing_load.ok).to_equal(false)
expect(missing_load.error).to_equal("dll-load-session-required:rolled-back")
val missing_evidence = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "dll-load-session-recorded", "dll-load-session-created", 0x1100, 0, false)
expect(missing_evidence.error).to_equal("missing-modeled-loaded-image-evidence")
val invalid_entry = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "dll-load-session-recorded", "modeled-loaded-image", 0, 0, false)
expect(invalid_entry.error).to_equal("invalid-dll-entrypoint-rva")
val invalid_tls = wine_dll_entrypoint_lifecycle_gate("kernel32.dll", "dll-load-session-recorded", "modeled-loaded-image", 0x1100, -1, false)
expect(invalid_tls.error).to_equal("invalid-tls-callback-count")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wine dll entrypoint lifecycle.
- wine dll entrypoint lifecycle

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `53ffa52e56a447df4d6ce8ba52256efec1f2b12f6b66ddbcd7f1ffb4f2cc9446`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53ffa52e56a447df4d6ce8ba52256efec1f2b12f6b66ddbcd7f1ffb4f2cc9446`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53ffa52e56a447df4d6ce8ba52256efec1f2b12f6b66ddbcd7f1ffb4f2cc9446`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models TLS-before-DllMain ordering without executing DLL code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks requests to actually execute DllMain or TLS callbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_dll_entrypoint_lifecycle_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a modeled load session and valid lifecycle inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
