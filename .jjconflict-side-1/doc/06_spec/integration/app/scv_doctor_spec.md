# scv_doctor_spec

> Purpose: This spec proves `scv doctor` prints one `<component>  OK|STALE|FAIL`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_doctor_spec

Purpose: This spec proves `scv doctor` prints one `<component>  OK|STALE|FAIL`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_doctor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv doctor` prints one `<component>  OK|STALE|FAIL`
row per health check and a final verdict line with fail-closed exit codes
(stabilization report §3).
Audience: Maintainers of the SCV stabilization tooling.

## Scenarios

### scv doctor

#### reports every component OK on a healthy repository

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports every component OK on a healthy repository
- Run doctor on a healthy repository
- Verify one row per component and a PASS verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports every component OK on a healthy repository")
step("Run doctor on a healthy repository")
var lines = _prelude("healthy")
lines.push("scv doctor")
lines.push("printf 'doctor_code=%s\\n' \"$?\"")
val out = _run(lines)
step("Verify one row per component and a PASS verdict")
expect(out).to_contain("objects  OK")
expect(out).to_contain("refs  OK")
expect(out).to_contain("operation heads  OK")
expect(out).to_contain("view  OK")
expect(out).to_contain("checkpoints  OK")
expect(out).to_contain("parser index  OK")
expect(out).to_contain("PASS — 8 check(s), 0 failed")
expect(out).to_contain("doctor_code=0")
expect(out).to_contain("exit=0")
```

</details>

#### fails with exit 1 when an object is corrupted

- fails with exit 1 when an object is corrupted
- Corrupt a commit object and run doctor
- Verify the objects row FAILs and the verdict is FAIL exit 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails with exit 1 when an object is corrupted")
step("Corrupt a commit object and run doctor")
var lines = _prelude("corrupt")
lines.push("C=$(sed -n 's/default: //p' .scv/meta/workspaces.sdn)")
lines.push("printf 'garbage\\n' >> \".scv/objects/commits/$C.sdn\"")
lines.push("set +e")
lines.push("scv doctor")
lines.push("printf 'doctor_code=%s\\n' \"$?\"")
lines.push("set -e")
val out = _run(lines)
step("Verify the objects row FAILs and the verdict is FAIL exit 1")
expect(out).to_contain("objects  FAIL")
expect(out).to_contain("FAIL — 8 check(s), 1 failed")
expect(out).to_contain("doctor_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### errors with exit 2 outside a repository

- errors with exit 2 outside a repository
- Run doctor in a directory with no repository
- Verify the nothing-was-checked verdict and exit 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("errors with exit 2 outside a repository")
step("Run doctor in a directory with no repository")
val lines = [
    "set -eu",
    "REPO=$(pwd)",
    "TMP=$(mktemp -d /tmp/scv-doctor-norepo.XXXXXX)",
    "cd \"$TMP\"",
    "set +e",
    "SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" doctor",
    "printf 'doctor_code=%s\\n' \"$?\"",
    "set -e"
]
val out = _run(lines)
step("Verify the nothing-was-checked verdict and exit 2")
expect(out).to_contain("ERROR — nothing was checked")
expect(out).to_contain("doctor_code=2")
expect(out).to_contain("exit=0")
```

</details>

#### reports a stale journal row and reconciles it from the published head

- reports a stale journal row and reconciles it from the published head
- Desynchronize the workspace pointer from the head view
- Verify the first run reports the stale journal, reconciles, and the second is OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports a stale journal row and reconciles it from the published head")
step("Desynchronize the workspace pointer from the head view")
var lines = _prelude("staleview")
lines.push("cp .scv/meta/workspaces.sdn ws.before")
lines.push("printf 'x2\\n' > b.txt")
lines.push("SCV_FAULT_AFTER=head scv snapshot >/dev/null 2>&1 || true")
lines.push("scv doctor")
lines.push("printf 'doctor_code=%s\\n' \"$?\"")
lines.push("scv doctor")
val out = _run(lines)
step("Verify the first run reports the stale journal, reconciles, and the second is OK")
expect(out).to_contain("journal  STALE")
expect(out).to_contain("journal  OK")
expect(out).to_not_contain("view  STALE")
expect(out).to_contain("view  OK")
expect(out).to_contain("doctor_code=0")
expect(out).to_contain("exit=0")
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-DOCTOR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `526a0e5bb0fb62c0fdb1bd6d24294d2ad4e6f87cdf57b4b4e3a2424584425c42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `526a0e5bb0fb62c0fdb1bd6d24294d2ad4e6f87cdf57b4b4e3a2424584425c42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `526a0e5bb0fb62c0fdb1bd6d24294d2ad4e6f87cdf57b4b4e3a2424584425c42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_doctor_spec.spl
mirror: doc/06_spec/integration/app/scv_doctor_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_doctor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_doctor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_doctor_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_doctor_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports every component OK on a healthy repository' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_doctor_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails with exit 1 when an object is corrupted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_doctor_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors with exit 2 outside a repository' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
