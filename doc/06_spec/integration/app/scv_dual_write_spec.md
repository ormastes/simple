# scv_dual_write_spec

> Purpose: This spec proves the SCV-MIG-24 dual-write comparison gate: after an

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_dual_write_spec

Purpose: This spec proves the SCV-MIG-24 dual-write comparison gate: after an

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_dual_write_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV-MIG-24 dual-write comparison gate: after an
explicit commit/snapshot, `scv_dual_write_verify(root, dest)` shadow-syncs and
then INDEPENDENTLY compares primary vs shadow — recomputed hash equality for
immutable object kinds, byte agreement for refs/heads, field-wise comparison
for the in-place-mutable change objects, and commit parent-DAG agreement —
reporting counts per kind; and `scv_dual_write_fsck(dest)` runs object-level
integrity checks against the shadow store itself. Fails closed: a corrupted
shadow object is named. Idempotent on re-verify.
Note: the month plan row names `scv_dual_write_compare_spec.spl`; this lane
was directed to `scv_dual_write_spec.spl` — SCV-MIG-24.shs maps to this file.
Audience: Maintainers of the SCV dual-write/native-shadow path.

## Scenarios

### scv dual-write verify (SCV-MIG-24)

#### agrees after an explicit snapshot: 0 mismatches, per-kind counts > 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- agrees after an explicit snapshot: 0 mismatches, per-kind counts > 0
- Snapshot, then dual-write verify + shadow fsck via the driver
- Verify sync ran, independent compare agrees, and shadow fsck is clean


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("agrees after an explicit snapshot: 0 mismatches, per-kind counts > 0")
step("Snapshot, then dual-write verify + shadow fsck via the driver")
var lines = _prelude("green")
lines.push("drv")
val out = _run(lines)
step("Verify sync ran, independent compare agrees, and shadow fsck is clean")
expect(out).to_contain("sync: PASS")
expect(out).to_contain("compared:")
expect(out).to_contain("chunks=2")
expect(out).to_contain("commits=1")
expect(out).to_contain("changes=1")
expect(out).to_contain("PASS — dual-write verified:")
expect(out).to_contain("0 mismatch(es)")
expect(out).to_contain("PASS — shadow fsck:")
expect(out).to_contain("0 error(s)")
expect(out).to_contain("exit=0")
```

</details>

#### fails closed naming a corrupted shadow object via independent recomputed hashes

- fails closed naming a corrupted shadow object via independent recomputed hashes
- Verify once, corrupt a shadow chunk, verify again
- Verify both the compare and the shadow fsck name the corrupt object


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed naming a corrupted shadow object via independent recomputed hashes")
step("Verify once, corrupt a shadow chunk, verify again")
var lines = _prelude("corrupt")
lines.push("drv >/dev/null")
lines.push("CHUNK=$(find \"$TMP/shadow/objects/chunks\" -type f | head -1)")
lines.push("printf 'CORRUPTED' > \"$CHUNK\"")
lines.push("drv")
val out = _run(lines)
step("Verify both the compare and the shadow fsck name the corrupt object")
expect(out).to_contain("FAIL — dual-write verified:")
expect(out).to_contain("objects/chunks/")
expect(out).to_contain("FAIL — shadow fsck:")
expect(out).to_contain("exit=0")
```

</details>

#### still agrees after a change object evolves in place across snapshots

- still agrees after a change object evolves in place across snapshots
- Verify, then snapshot again (change mutates in place), verify again
- Verify the mutable change kind is compared field-wise and agrees


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("still agrees after a change object evolves in place across snapshots")
step("Verify, then snapshot again (change mutates in place), verify again")
var lines = _prelude("evolve")
lines.push("drv >/dev/null")
lines.push("printf 'gamma\\n' > c.txt")
lines.push("scv snapshot >/dev/null")
lines.push("drv")
val out = _run(lines)
step("Verify the mutable change kind is compared field-wise and agrees")
expect(out).to_contain("sync: PASS")
expect(out).to_contain("changes=")
expect(out).to_contain("PASS — dual-write verified:")
expect(out).to_contain("0 mismatch(es)")
expect(out).to_contain("exit=0")
```

</details>

#### is idempotent: an immediate re-verify copies nothing and still agrees

- is idempotent: an immediate re-verify copies nothing and still agrees
- Run the driver twice back to back
- Verify the second run syncs 0 objects and the compare still passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is idempotent: an immediate re-verify copies nothing and still agrees")
step("Run the driver twice back to back")
var lines = _prelude("idem")
lines.push("drv >/dev/null")
lines.push("drv")
val out = _run(lines)
step("Verify the second run syncs 0 objects and the compare still passes")
expect(out).to_contain("sync: PASS — 0 object(s) replicated")
expect(out).to_contain("PASS — dual-write verified:")
expect(out).to_contain("0 mismatch(es)")
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
- `REQ-SCV-DUAL-WRITE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a5e957dc3f81ab791bb91165ed8c7afe526169a4cd9dc373998252e5f4da1b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a5e957dc3f81ab791bb91165ed8c7afe526169a4cd9dc373998252e5f4da1b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a5e957dc3f81ab791bb91165ed8c7afe526169a4cd9dc373998252e5f4da1b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_dual_write_spec.spl
mirror: doc/06_spec/integration/app/scv_dual_write_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_dual_write_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_dual_write_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_dual_write_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_dual_write_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees after an explicit snapshot: 0 mismatches, per-kind counts > 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_dual_write_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed naming a corrupted shadow object via independent recomputed hashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_dual_write_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still agrees after a change object evolves in place across snapshots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
