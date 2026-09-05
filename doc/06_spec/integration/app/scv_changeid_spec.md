# scv_changeid_spec

> Purpose: This spec proves SCV allocates a persistent logical ChangeId that is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_changeid_spec

Purpose: This spec proves SCV allocates a persistent logical ChangeId that is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_changeid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV allocates a persistent logical ChangeId that is
carried across successive snapshots of the same working-copy change, and that a
new change is allocated only by `scv new-change` or after `scv close-change`.
Audience: Maintainers of the SCV storage layer (report §3.3.A / §7.7 / §14.2).

## Scenarios

### scv persistent logical ChangeId

#### carries the same change id across a comment-only re-snapshot

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries the same change id across a comment-only re-snapshot
- Snapshot, add a comment line, snapshot again
- Verify the commit id changed but the change id was carried


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("carries the same change id across a comment-only re-snapshot")
step("Snapshot, add a comment line, snapshot again")
var lines = _prelude("comment")
lines.push("printf '# note\\nfn main():\\n    1\\n' > a.spl")
lines.push("scv snapshot >/dev/null")
lines.push("C2=$(cur_commit); CH2=$(cur_change)")
lines.push("printf 'commit_changed=%s\\n' \"$([ \"$C1\" != \"$C2\" ] && echo yes || echo no)\"")
lines.push("printf 'change_same=%s\\n' \"$([ \"$CH1\" = \"$CH2\" ] && echo yes || echo no)\"")
lines.push("printf 'latest_is_c2=%s\\n' \"$([ \"$(sed -n 's/latest: //p' .scv/objects/changes/$CH2.sdn)\" = \"$C2\" ] && echo yes || echo no)\"")
lines.push("printf 'pred_is_c1=%s\\n' \"$([ \"$(sed -n 's/predecessors: //p' .scv/objects/changes/$CH2.sdn)\" = \"$C1\" ] && echo yes || echo no)\"")
lines.push("printf 'format=%s\\n' \"$(sed -n 's/format: //p' .scv/objects/changes/$CH2.sdn)\"")
lines.push("printf 'state=%s\\n' \"$(sed -n 's/state: //p' .scv/objects/changes/$CH2.sdn)\"")
val out = _run(lines)
step("Verify the commit id changed but the change id was carried")
expect(out).to_contain("commit_changed=yes")
expect(out).to_contain("change_same=yes")
expect(out).to_contain("latest_is_c2=yes")
expect(out).to_contain("pred_is_c1=yes")
expect(out).to_contain("format=2")
expect(out).to_contain("state=open")
expect(out).to_contain("exit=0")
```

</details>

#### allocates a fresh change id only on new-change

- allocates a fresh change id only on new-change
- Run new-change, then snapshot an edit
- Verify the new change differs, is carried, and fsck stays clean


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allocates a fresh change id only on new-change")
step("Run new-change, then snapshot an edit")
var lines = _prelude("new")
lines.push("scv new-change")
lines.push("CH2=$(cur_change)")
lines.push("printf 'x\\n' > b.txt")
lines.push("scv snapshot >/dev/null")
lines.push("CH3=$(cur_change)")
lines.push("printf 'new_differs=%s\\n' \"$([ \"$CH1\" != \"$CH2\" ] && echo yes || echo no)\"")
lines.push("printf 'new_carried=%s\\n' \"$([ \"$CH2\" = \"$CH3\" ] && echo yes || echo no)\"")
lines.push("printf 'prefix=%s\\n' \"$(printf '%s' \"$CH2\" | cut -c1-7)\"")
lines.push("FSCK=$(scv fsck || true)")
lines.push("printf 'fsck_struct_errors=%s\\n' \"$(printf '%s' \"$FSCK\" | grep -Ec 'missing|corrupt|mismatch|bad (commit|change|tree)' || true)\"")
val out = _run(lines)
step("Verify the new change differs, is carried, and fsck stays clean")
expect(out).to_contain("new-change change_")
expect(out).to_contain("new_differs=yes")
expect(out).to_contain("new_carried=yes")
expect(out).to_contain("prefix=change_")
expect(out).to_contain("fsck_struct_errors=0")
expect(out).to_contain("exit=0")
```

</details>

#### allocates a fresh change id after close-change

- allocates a fresh change id after close-change
- Close the active change, then snapshot an edit
- Verify the closed change is frozen and a new one was allocated


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allocates a fresh change id after close-change")
step("Close the active change, then snapshot an edit")
var lines = _prelude("close")
lines.push("scv close-change")
lines.push("printf 'closed_state=%s\\n' \"$(sed -n 's/state: //p' .scv/objects/changes/$CH1.sdn)\"")
lines.push("printf 'y\\n' > c.txt")
lines.push("scv snapshot >/dev/null")
lines.push("CH2=$(cur_change)")
lines.push("printf 'after_close_differs=%s\\n' \"$([ \"$CH1\" != \"$CH2\" ] && echo yes || echo no)\"")
lines.push("printf 'old_latest_kept=%s\\n' \"$([ \"$(sed -n 's/latest: //p' .scv/objects/changes/$CH1.sdn)\" = \"$C1\" ] && echo yes || echo no)\"")
lines.push("FSCK=$(scv fsck || true)")
lines.push("printf 'fsck_struct_errors=%s\\n' \"$(printf '%s' \"$FSCK\" | grep -Ec 'missing|corrupt|mismatch|bad (commit|change|tree)' || true)\"")
val out = _run(lines)
step("Verify the closed change is frozen and a new one was allocated")
expect(out).to_contain("close-change change_")
expect(out).to_contain("closed_state=closed")
expect(out).to_contain("after_close_differs=yes")
expect(out).to_contain("old_latest_kept=yes")
expect(out).to_contain("fsck_struct_errors=0")
expect(out).to_contain("exit=0")
```

</details>

#### keeps reading v1 change objects that have no format field

- keeps reading v1 change objects that have no format field
- Rewrite the change object in v1 shape and snapshot again
- Verify a v1 object is treated as an open change and upgraded on write


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps reading v1 change objects that have no format field")
step("Rewrite the change object in v1 shape and snapshot again")
var lines = _prelude("v1")
lines.push("printf 'latest: %s\\npredecessors: \\n' \"$C1\" > \".scv/objects/changes/$CH1.sdn\"")
lines.push("printf 'z\\n' > d.txt")
lines.push("scv snapshot >/dev/null")
lines.push("CH2=$(cur_change)")
lines.push("printf 'v1_carried=%s\\n' \"$([ \"$CH1\" = \"$CH2\" ] && echo yes || echo no)\"")
lines.push("FSCK=$(scv fsck || true)")
lines.push("printf 'fsck_struct_errors=%s\\n' \"$(printf '%s' \"$FSCK\" | grep -Ec 'missing|corrupt|mismatch|bad (commit|change|tree)' || true)\"")
val out = _run(lines)
step("Verify a v1 object is treated as an open change and upgraded on write")
expect(out).to_contain("v1_carried=yes")
expect(out).to_contain("fsck_struct_errors=0")
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
- `REQ-SCV-CHANGEID-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `464386b885ed592a66bfdface4bf73355b6e2c973e06a003942d100f7e14a29a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `464386b885ed592a66bfdface4bf73355b6e2c973e06a003942d100f7e14a29a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `464386b885ed592a66bfdface4bf73355b6e2c973e06a003942d100f7e14a29a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_changeid_spec.spl
mirror: doc/06_spec/integration/app/scv_changeid_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_changeid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_changeid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_changeid_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_changeid_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries the same change id across a comment-only re-snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_changeid_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates a fresh change id only on new-change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_changeid_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates a fresh change id after close-change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
