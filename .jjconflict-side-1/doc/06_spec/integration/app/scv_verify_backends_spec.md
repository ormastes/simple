# scv_verify_backends_spec

> Purpose: This spec proves `scv verify-backends --git <path>` compares the SCV

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_verify_backends_spec

Purpose: This spec proves `scv verify-backends --git <path>` compares the SCV

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_verify_backends_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv verify-backends --git <path>` compares the SCV
current tree byte-for-byte against a git worktree tree and reports a fail-closed
verdict (stabilization report §4).
Audience: Maintainers of the SCV stabilization tooling.

## Scenarios

### scv verify-backends

#### passes when the git tree matches the SCV tree byte for byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes when the git tree matches the SCV tree byte for byte
- Compare the SCV tree against an identical git commit
- Verify the PASS verdict counts the compared paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("passes when the git tree matches the SCV tree byte for byte")
step("Compare the SCV tree against an identical git commit")
var lines = _prelude("match")
lines.push("scv verify-backends --git \"$TMP/mirror\"")
lines.push("printf 'vb_code=%s\\n' \"$?\"")
val out = _run(lines)
step("Verify the PASS verdict counts the compared paths")
expect(out).to_contain("PASS — 2 path(s) compared, 0 mismatches")
expect(out).to_contain("vb_code=0")
expect(out).to_contain("exit=0")
```

</details>

#### fails when bytes differ or paths are missing on either side

- fails when bytes differ or paths are missing on either side
- Diverge the git mirror and re-compare
- Verify every mismatch class is named and the exit code is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails when bytes differ or paths are missing on either side")
step("Diverge the git mirror and re-compare")
var lines = _prelude("diverge")
lines.push("printf 'ALPHA\\n' > \"$TMP/mirror/a.txt\"")
lines.push("rm \"$TMP/mirror/sub/b.txt\"")
lines.push("printf 'gamma\\n' > \"$TMP/mirror/c.txt\"")
lines.push("git -C \"$TMP/mirror\" add -A")
lines.push("git -C \"$TMP/mirror\" -c user.email=t@t -c user.name=t commit -q -m diverge")
lines.push("set +e")
lines.push("scv verify-backends --git \"$TMP/mirror\"")
lines.push("printf 'vb_code=%s\\n' \"$?\"")
lines.push("set -e")
val out = _run(lines)
step("Verify every mismatch class is named and the exit code is 1")
expect(out).to_contain("bytes differ: a.txt")
expect(out).to_contain("missing in git: sub/b.txt")
expect(out).to_contain("missing in scv: c.txt")
expect(out).to_contain("FAIL — 3 mismatch(es)")
expect(out).to_contain("vb_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### errors when the git side cannot be read

- errors when the git side cannot be read
- Point --git at a directory that is not a git repository
- Verify the nothing-was-checked verdict and exit 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("errors when the git side cannot be read")
step("Point --git at a directory that is not a git repository")
var lines = _prelude("nogit")
lines.push("mkdir \"$TMP/empty\"")
lines.push("set +e")
lines.push("scv verify-backends --git \"$TMP/empty\"")
lines.push("printf 'vb_code=%s\\n' \"$?\"")
lines.push("set -e")
val out = _run(lines)
step("Verify the nothing-was-checked verdict and exit 2")
expect(out).to_contain("ERROR — nothing was checked")
expect(out).to_contain("vb_code=2")
expect(out).to_contain("exit=0")
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
- `REQ-SCV-VERIFY-BACKENDS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33a2cbdaa7bf27dfc6b74644db14776af670737ff55b6f50e4c651cf15187a47`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33a2cbdaa7bf27dfc6b74644db14776af670737ff55b6f50e4c651cf15187a47`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33a2cbdaa7bf27dfc6b74644db14776af670737ff55b6f50e4c651cf15187a47`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_verify_backends_spec.spl
mirror: doc/06_spec/integration/app/scv_verify_backends_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_verify_backends_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_verify_backends_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_verify_backends_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_verify_backends_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes when the git tree matches the SCV tree byte for byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_verify_backends_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails when bytes differ or paths are missing on either side' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_verify_backends_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors when the git side cannot be read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
