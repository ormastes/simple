# scv_format_version_spec

> Purpose: This spec proves object/format versioning (SCV-MIG-12, P0.2): `scv

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_format_version_spec

Purpose: This spec proves object/format versioning (SCV-MIG-12, P0.2): `scv

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_format_version_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves object/format versioning (SCV-MIG-12, P0.2): `scv
init` writes a `.scv/format.sdn` marker at version 2, `scv doctor` reports the
repo format version row, a v1 repo (no marker) stays fully readable — doctor
reports v1 and fsck stays clean — and an unknown future version fails closed.
Audience: Maintainers of the SCV storage layer (scv_v2_final_report §18.1).

## Scenarios

### scv object/format versions (SCV-MIG-12)

#### writes a version-2 format marker on init and reports it in doctor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes a version-2 format marker on init and reports it in doctor
- Init, read format.sdn, run doctor


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes a version-2 format marker on init and reports it in doctor")
step("Init, read format.sdn, run doctor")
var lines = _prelude("v2")
lines.push("cat .scv/format.sdn")
lines.push("scv doctor")
val out = _run(lines)
expect(out).to_contain("version: 2")
expect(out).to_contain("format  v2  OK")
expect(out).to_contain("exit=0")
```

</details>

#### reads a v1 repo (no marker): doctor reports v1 and fsck stays clean

- reads a v1 repo (no marker): doctor reports v1 and fsck stays clean
- Remove the marker to simulate a v1 repo, run doctor and fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads a v1 repo (no marker): doctor reports v1 and fsck stays clean")
step("Remove the marker to simulate a v1 repo, run doctor and fsck")
var lines = _prelude("v1")
lines.push("rm .scv/format.sdn")
lines.push("scv doctor")
lines.push("scv fsck")
val out = _run(lines)
expect(out).to_contain("format  v1  OK")
expect(out).to_contain("OK checked=")
expect(out).to_contain("exit=0")
```

</details>

#### fails closed on an unknown future format version

- fails closed on an unknown future format version
- Write a version-9 marker, run doctor and fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed on an unknown future format version")
step("Write a version-9 marker, run doctor and fsck")
var lines = _prelude("v9")
lines.push("printf 'version: 9\\n' > .scv/format.sdn")
lines.push("scv doctor || true")
lines.push("scv fsck || true")
val out = _run(lines)
expect(out).to_contain("format  v9  FAIL")
expect(out).to_contain("bad repo format version: 9")
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-FORMAT-VERSION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e30389a55ebab68c62f6610fc01b99167aa4d5b87a1a51027cbf1055300237c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e30389a55ebab68c62f6610fc01b99167aa4d5b87a1a51027cbf1055300237c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e30389a55ebab68c62f6610fc01b99167aa4d5b87a1a51027cbf1055300237c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_format_version_spec.spl
mirror: doc/06_spec/integration/app/scv_format_version_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_format_version_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_format_version_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_format_version_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_format_version_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes a version-2 format marker on init and reports it in doctor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_format_version_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a v1 repo (no marker): doctor reports v1 and fsck stays clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_format_version_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on an unknown future format version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
