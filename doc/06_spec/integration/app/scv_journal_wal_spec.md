# scv_journal_wal_spec

> Purpose: This spec proves the SCV append-only operation/event journal + WAL

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_journal_wal_spec

Purpose: This spec proves the SCV append-only operation/event journal + WAL

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_journal_wal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV append-only operation/event journal + WAL
(MIG-10, v2 final report §16.1, stabilization §7): every repo mutation appends
one line-framed event record to `.scv/journal/events.log`; the mutable
head/meta publication is bracketed by `BEGIN op=`/`COMMIT op=` in
`.scv/journal/wal.log`; a crash injected at the `wal` fault point leaves an
incomplete trailing transaction that the next open rolls back — old or new,
never half — and `scv doctor` stays PASS.
Audience: Maintainers of the SCV storage layer.

## Scenarios

### scv journal and WAL

#### appends one framed event record per snapshot mutation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- appends one framed event record per snapshot mutation
- Snapshot twice and inspect the append-only event journal


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("appends one framed event record per snapshot mutation")
step("Snapshot twice and inspect the append-only event journal")
var lines = _harness()
lines.push("printf 'two\\n' > a.txt")
lines.push("scv snapshot >/dev/null")
lines.push("printf 'events=%s\\n' \"$(grep -c '^op=' .scv/journal/events.log)\"")
lines.push("grep -Ec '^op=op_[0-9a-f]+ kind=snapshot refs=commit_[0-9a-f]+ sha=tree_[0-9a-f]+ utc=[0-9]+$' .scv/journal/events.log")
val out = _run(lines)
expect(out).to_contain("events=2")
expect(out).to_contain("exit=0")
```

</details>

#### brackets every head publication in a committed WAL transaction

- brackets every head publication in a committed WAL transaction
- Verify BEGIN/SET/NEW/COMMIT framing for the snapshot's WAL entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("brackets every head publication in a committed WAL transaction")
step("Verify BEGIN/SET/NEW/COMMIT framing for the snapshot's WAL entry")
var lines = _harness()
lines.push("grep -c '^BEGIN op=' .scv/journal/wal.log")
lines.push("grep -c '^SET path=HEAD_OP old=' .scv/journal/wal.log")
lines.push("grep -c '^SET path=meta/workspaces.sdn old=' .scv/journal/wal.log")
lines.push("grep -c '^COMMIT op=' .scv/journal/wal.log")
lines.push("printf 'framed=ok\\n'")
val out = _run(lines)
expect(out).to_contain("framed=ok")
expect(out).to_contain("exit=0")
```

</details>

#### rolls back an incomplete trailing WAL transaction on restart, old-or-new never half

- rolls back an incomplete trailing WAL transaction on restart, old-or-new never half
- Inject SCV_FAULT_AFTER=wal, restart, verify rollback + doctor PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rolls back an incomplete trailing WAL transaction on restart, old-or-new never half")
step("Inject SCV_FAULT_AFTER=wal, restart, verify rollback + doctor PASS")
var lines = _harness()
lines.push("OLD_OP=$(cat .scv/HEAD_OP)")
lines.push("OLD_COMMIT=$(sed -n 's/default: //p' .scv/meta/workspaces.sdn)")
lines.push("printf 'edited\\n' > a.txt")
lines.push("set +e")
lines.push("SCV_FAULT_AFTER=wal scv snapshot")
lines.push("printf 'fault_code=%s\\n' \"$?\"")
lines.push("set -e")
lines.push("scv doctor")
lines.push("grep -c 'recovered=rollback' .scv/journal/wal.log")
lines.push("NEW_OP=$(cat .scv/HEAD_OP)")
lines.push("NEW_COMMIT=$(sed -n 's/default: //p' .scv/meta/workspaces.sdn)")
lines.push("test \"$NEW_OP\" = \"$OLD_OP\" && test \"$NEW_COMMIT\" = \"$OLD_COMMIT\" && printf 'state=old\\n'")
lines.push("scv snapshot >/dev/null")
lines.push("scv fsck | tail -1")
val out = _run(lines)
expect(out).to_contain("FAULT injected after wal")
expect(out).to_contain("fault_code=3")
expect(out).to_contain("state=old")
expect(out).to_contain("PASS")
expect(out).to_contain("exit=0")
```

</details>

#### rolls a published head forward so head and workspace never disagree

- rolls a published head forward so head and workspace never disagree
- Inject SCV_FAULT_AFTER=head, reopen, verify forward recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rolls a published head forward so head and workspace never disagree")
step("Inject SCV_FAULT_AFTER=head, reopen, verify forward recovery")
var lines = _harness()
lines.push("OLD_OP=$(cat .scv/HEAD_OP)")
lines.push("printf 'edited\\n' > a.txt")
lines.push("set +e")
lines.push("SCV_FAULT_AFTER=head scv snapshot >/dev/null 2>&1")
lines.push("printf 'fault_code=%s\\n' \"$?\"")
lines.push("set -e")
lines.push("scv doctor")
lines.push("grep -c 'recovered=forward' .scv/journal/wal.log")
lines.push("NEW_OP=$(cat .scv/HEAD_OP)")
lines.push("NEW_COMMIT=$(sed -n 's/default: //p' .scv/meta/workspaces.sdn)")
lines.push("test \"$NEW_OP\" != \"$OLD_OP\" && printf 'state=new\\n'")
lines.push("scv fsck | tail -1")
val out = _run(lines)
expect(out).to_contain("fault_code=3")
expect(out).to_contain("state=new")
expect(out).to_contain("PASS")
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
- `REQ-SCV-JOURNAL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b947b113bb51b9d28a91f56cf553e640ba332ea7fd74ad20d531976af6e902d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b947b113bb51b9d28a91f56cf553e640ba332ea7fd74ad20d531976af6e902d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b947b113bb51b9d28a91f56cf553e640ba332ea7fd74ad20d531976af6e902d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_journal_wal_spec.spl
mirror: doc/06_spec/integration/app/scv_journal_wal_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_journal_wal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_journal_wal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_journal_wal_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_journal_wal_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends one framed event record per snapshot mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_journal_wal_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'brackets every head publication in a committed WAL transaction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_journal_wal_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rolls back an incomplete trailing WAL transaction on restart, old-or-new never half' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
