# scv_shadow_write_spec

> Purpose: This spec proves SCV-IMPL-B-05 — CONTINUOUS native shadow write on

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_shadow_write_spec

Purpose: This spec proves SCV-IMPL-B-05 — CONTINUOUS native shadow write on

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_shadow_write_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-B-05 — CONTINUOUS native shadow write on
the commit path. Once `scv shadow-write enable --dest <dir>` is set, every
explicit revision (every operation through store.spl scv_write_operation:
snapshot, new-change, close-change, ...) automatically dual-writes to the
native shadow and is compared — tree, content, parent DAG, refs (MIG-24
scv_dual_write_verify), and reachability (shadow fsck) — appending a
fail-closed report row to .scv/meta/shadow_write_log.sdn. A divergence is a
FAIL row that `scv shadow-write status` surfaces until a later PASS resolves
it. Default (no config) is a strict no-op. Host note: jj is broken on this
host; the git side of the dual write is the read-only backend_git/shadow
path — nothing shells out to sj/jj.
Audience: Maintainers of the SCV dual-write/native-shadow path.

## Scenarios

### scv continuous shadow write (SCV-IMPL-B-05)

#### dual-writes and compares automatically on every explicit revision once enabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Enable shadow-write, then commit twice through the normal snapshot path
- Verify two automatic rows, both PASS, and shadow holds the commit objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-SHADOW-WRITE-001
step("Enable shadow-write, then commit twice through the normal snapshot path")
var lines = _prelude("cont")
lines.push("scv shadow-write enable --dest \"$TMP/shadow\"")
lines.push("printf 'gamma\\n' >> a.txt")
lines.push("scv snapshot >/dev/null")
lines.push("printf 'delta\\n' >> sub/b.txt")
lines.push("scv snapshot >/dev/null")
lines.push("scv shadow-write status")
lines.push("ls \"$TMP/shadow/objects/commits\" | wc -l")
val out = _run(lines)
step("Verify two automatic rows, both PASS, and shadow holds the commit objects")
expect(out).to_contain("PASS — shadow-write enabled:")
expect(out).to_contain("rows: 2")
expect(out).to_contain("1|op_")
expect(out).to_contain("2|op_")
expect(out).to_contain("verify=PASS — dual-write verified:")
expect(out).to_contain("fsck=PASS — shadow fsck:")
expect(out).to_contain("PASS — shadow-write continuous: 2 row(s), 2 pass, 0 fail, latest PASS")
expect(out).to_contain("exit=0")
```

</details>

#### records a fail-closed FAIL row on shadow divergence and surfaces it in status

- Enable + commit, corrupt a shadow chunk, commit again
- Verify the divergence became a FAIL row that status refuses to hide


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-SHADOW-WRITE-001
step("Enable + commit, corrupt a shadow chunk, commit again")
var lines = _prelude("diverge")
lines.push("scv shadow-write enable --dest \"$TMP/shadow\" >/dev/null")
lines.push("printf 'gamma\\n' >> a.txt")
lines.push("scv snapshot >/dev/null")
lines.push("CHUNK=$(find \"$TMP/shadow/objects/chunks\" -type f | head -1)")
lines.push("printf 'CORRUPTED' > \"$CHUNK\"")
lines.push("printf 'delta\\n' >> a.txt")
lines.push("scv snapshot >/dev/null")
lines.push("scv shadow-write status || echo status-rc=$?")
val out = _run(lines)
step("Verify the divergence became a FAIL row that status refuses to hide")
expect(out).to_contain("|FAIL|")
expect(out).to_contain("FAIL — shadow-write divergence unresolved:")
expect(out).to_contain("status-rc=1")
expect(out).to_contain("exit=0")
```

</details>

#### is a strict no-op by default: no config, no log, unchanged commit behavior

- Commit without enabling shadow-write; then ask for status
- Verify nothing was written and status is a fail-closed ERROR


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-SHADOW-WRITE-001
step("Commit without enabling shadow-write; then ask for status")
var lines = _prelude("noop")
lines.push("printf 'gamma\\n' >> a.txt")
lines.push("scv snapshot")
lines.push("test ! -e .scv/meta/shadow_write_log.sdn && echo NO-LOG-WRITTEN")
lines.push("test ! -e \"$TMP/shadow\" && echo NO-SHADOW-DIR")
lines.push("scv shadow-write status || echo status-rc=$?")
val out = _run(lines)
step("Verify nothing was written and status is a fail-closed ERROR")
expect(out).to_contain("snapshot commit_")
expect(out).to_contain("NO-LOG-WRITTEN")
expect(out).to_contain("NO-SHADOW-DIR")
expect(out).to_contain("ERROR — nothing was checked (shadow-write not enabled)")
expect(out).to_contain("status-rc=2")
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
- `REQ-SCV-SHADOW-WRITE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea9008f8cef577ee7bcdfdf546d967e59b3d21635cf6ea8b897c5891609142b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea9008f8cef577ee7bcdfdf546d967e59b3d21635cf6ea8b897c5891609142b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea9008f8cef577ee7bcdfdf546d967e59b3d21635cf6ea8b897c5891609142b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_shadow_write_spec.spl
mirror: doc/06_spec/integration/app/scv_shadow_write_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_shadow_write_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_shadow_write_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_shadow_write_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_shadow_write_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dual-writes and compares automatically on every explicit revision once enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_shadow_write_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a fail-closed FAIL row on shadow divergence and surfaces it in status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_shadow_write_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is a strict no-op by default: no config, no log, unchanged commit behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
