# scv_quarantine_gc_spec

> Purpose: This spec proves `scv gc` (MIG-21, stabilization §9) is a conservative

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_quarantine_gc_spec

Purpose: This spec proves `scv gc` (MIG-21, stabilization §9) is a conservative

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_quarantine_gc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv gc` (MIG-21, stabilization §9) is a conservative
quarantine GC: dry run by default (deletes nothing, lists would-delete ids);
real pruning only via `--prune --checkpoint <verified-checkpoint-id>` and only
when fsck is clean, the checkpoint verifies, and objects have been unreachable
longer than SCV_GC_QUARANTINE_DAYS (30) — otherwise FAIL naming the unmet
condition. Pruned objects move to `.scv/quarantine/<date>/` and stay
recoverable; nothing is unlinked. Verdict is the last line.
Audience: Maintainers of the SCV storage layer.

## Scenarios

### scv gc quarantine (MIG-21)

#### defaults to a dry run that lists would-delete objects and deletes nothing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to a dry run that lists would-delete objects and deletes nothing
- Orphan chunk, count objects, run bare gc, counts unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defaults to a dry run that lists would-delete objects and deletes nothing")
step("Orphan chunk, count objects, run bare gc, counts unchanged")
var lines = _harness()
lines.push("BEFORE=$(find .scv/objects -type f | wc -l)")
lines.push("scv gc")
lines.push("AFTER=$(find .scv/objects -type f | wc -l)")
lines.push("test \"$BEFORE\" = \"$AFTER\" && printf 'objects=unchanged\\n'")
lines.push("test -e .scv/objects/chunks/sha256_orphan.blob && printf 'orphan=still-present\\n'")
val out = _run(lines)
expect(out).to_contain("would-delete chunks/sha256_orphan.blob")
expect(out).to_contain("PASS — gc dry run, nothing deleted")
expect(out).to_contain("objects=unchanged")
expect(out).to_contain("orphan=still-present")
expect(out).to_contain("exit=0")
```

</details>

#### refuses --prune without a checkpoint and when fsck is not clean

- refuses --prune without a checkpoint and when fsck is not clean
- Prune without checkpoint FAILs; corrupt chunk makes fsck gate FAIL


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses --prune without a checkpoint and when fsck is not clean")
step("Prune without checkpoint FAILs; corrupt chunk makes fsck gate FAIL")
var lines = _harness()
lines.push("scv gc --prune > prune1.out 2>&1 || true")
lines.push("cat prune1.out")
lines.push("test -e .scv/objects/chunks/sha256_orphan.blob && printf 'orphan1=kept\\n'")
lines.push("CP=$(scv checkpoint | awk '{print $2}')")
lines.push("LIVE=$(ls .scv/objects/chunks | grep -v orphan | head -1)")
lines.push("printf 'corrupt' >> \".scv/objects/chunks/$LIVE\"")
lines.push("scv gc --prune --checkpoint \"$CP\" > prune2.out 2>&1 || true")
lines.push("cat prune2.out")
lines.push("test -e .scv/objects/chunks/sha256_orphan.blob && printf 'orphan2=kept\\n'")
val out = _run(lines)
expect(out).to_contain("FAIL — prune requires --checkpoint <verified-checkpoint-id>")
expect(out).to_contain("FAIL — fsck not clean, refusing to prune")
expect(out).to_contain("orphan1=kept")
expect(out).to_contain("orphan2=kept")
```

</details>

#### enforces the retention age and quarantines aged objects recoverably

- enforces the retention age and quarantines aged objects recoverably
- Young orphan FAILs retention; backdated orphan moves to quarantine and is recoverable


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("enforces the retention age and quarantines aged objects recoverably")
step("Young orphan FAILs retention; backdated orphan moves to quarantine and is recoverable")
var lines = _harness()
lines.push("CP=$(scv checkpoint | awk '{print $2}')")
lines.push("scv gc --prune --checkpoint \"$CP\" > young.out 2>&1 || true")
lines.push("cat young.out")
lines.push("test -e .scv/objects/chunks/sha256_orphan.blob && printf 'young=kept\\n'")
lines.push("touch -d '40 days ago' .scv/objects/chunks/sha256_orphan.blob")
lines.push("scv gc --prune --checkpoint \"$CP\"")
lines.push("test ! -e .scv/objects/chunks/sha256_orphan.blob && printf 'orphan=gone-from-objects\\n'")
lines.push("Q=$(find .scv/quarantine -name sha256_orphan.blob | head -1)")
lines.push("test -n \"$Q\" && printf 'quarantine=holds-orphan\\n'")
lines.push("cp \"$Q\" .scv/objects/chunks/sha256_orphan.blob")
lines.push("test \"$(cat .scv/objects/chunks/sha256_orphan.blob)\" = 'orphan' && printf 'recovered=yes\\n'")
val out = _run(lines)
expect(out).to_contain("FAIL — retention age not met (SCV_GC_QUARANTINE_DAYS=30)")
expect(out).to_contain("young=kept")
expect(out).to_contain("PASS — gc pruned 1 object(s) to quarantine")
expect(out).to_contain("orphan=gone-from-objects")
expect(out).to_contain("quarantine=holds-orphan")
expect(out).to_contain("recovered=yes")
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
- `REQ-SCV-GC-QUARANTINE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de0c1045d4663b00d0b2d5541433eaf57290dc3ff61ba42ebcd27bb21f477933`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de0c1045d4663b00d0b2d5541433eaf57290dc3ff61ba42ebcd27bb21f477933`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de0c1045d4663b00d0b2d5541433eaf57290dc3ff61ba42ebcd27bb21f477933`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_quarantine_gc_spec.spl
mirror: doc/06_spec/integration/app/scv_quarantine_gc_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_quarantine_gc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_quarantine_gc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_quarantine_gc_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_quarantine_gc_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to a dry run that lists would-delete objects and deletes nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_quarantine_gc_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses --prune without a checkpoint and when fsck is not clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_quarantine_gc_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enforces the retention age and quarantines aged objects recoverably' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
