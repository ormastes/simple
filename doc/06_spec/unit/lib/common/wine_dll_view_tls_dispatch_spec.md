# Wine Dll View Tls Dispatch Specification

> Tests covering wine dll view TLS dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll View Tls Dispatch Specification

## Scenarios

### wine dll view TLS dispatch

#### records TLS callback dispatch after import binding without executing callbacks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records TLS callback dispatch after import binding without executing callbacks
   - Expected: result.ok is true
   - Expected: result.status equals `dll-view-tls-dispatch-recorded`
   - Expected: result.callback_count equals `1`
   - Expected: result.first_callback_rva equals `0x2100`
   - Expected: result.dispatch_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records TLS callback dispatch after import binding without executing callbacks")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_record_file_view_tls_dispatch("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dll-view-tls-dispatch-recorded")
expect(result.callback_count).to_equal(1)
expect(result.first_callback_rva).to_equal(0x2100)
expect(result.dispatch_count).to_equal(1)
expect(result.evidence).to_contain("dll-import-thunk-bytes-written")
expect(result.evidence).to_contain("tls-callback-dispatch")
expect(result.evidence).to_contain("tls-before-dllmain")
expect(result.evidence).to_contain("no-tls-callback-executed")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### keeps TLS planning behind callback support evidence

- keeps TLS planning behind callback support evidence
   - Expected: result.ok is false
   - Expected: result.error equals `dll-tls:missing-api-tls-callback`
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps TLS planning behind callback support evidence")
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_record_file_view_tls_dispatch("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("dll-tls:missing-api-tls-callback")
expect(result.evidence).to_contain("no-tls-callback-executed")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_dll_view_tls_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wine dll view TLS dispatch.
- wine dll view TLS dispatch

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `164c3586257520f5927e782ae3018f085fdff918f62aa2989317dec5ba1541ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `164c3586257520f5927e782ae3018f085fdff918f62aa2989317dec5ba1541ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `164c3586257520f5927e782ae3018f085fdff918f62aa2989317dec5ba1541ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/wine_dll_view_tls_dispatch_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_dll_view_tls_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_dll_view_tls_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_dll_view_tls_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_dll_view_tls_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_dll_view_tls_dispatch_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records TLS callback dispatch after import binding without executing callbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_dll_view_tls_dispatch_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps TLS planning behind callback support evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
