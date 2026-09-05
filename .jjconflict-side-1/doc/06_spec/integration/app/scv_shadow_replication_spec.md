# scv_shadow_replication_spec

> Purpose: This spec proves `scv shadow-sync --dest <dir>` replicates the SCV

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_shadow_replication_spec

Purpose: This spec proves `scv shadow-sync --dest <dir>` replicates the SCV

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_shadow_replication_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv shadow-sync --dest <dir>` replicates the SCV
immutable objects and refs into a shadow store as content-addressed copies
verified by recomputed hashes, records a watermark in
.scv/meta/shadow_state.sdn, is idempotent on re-run, and fails closed (no
watermark advance) on a corrupted shadow object (SCV-MIG-16, asymmetric
replication: GitHub canonical + SCV shadow; the documented production dest is
/mnt/data/scv-backup/scv-shadow — the spec uses a temp dir).
Audience: Maintainers of the SCV shadow replication path.

## Scenarios

### scv shadow-sync

#### replicates immutable objects and refs, then is idempotent on re-run

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replicates immutable objects and refs, then is idempotent on re-run
- Sync into an empty shadow store, then re-run over the same dest
- Verify replication, the watermark, and the idempotent zero-copy re-run


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("replicates immutable objects and refs, then is idempotent on re-run")
step("Sync into an empty shadow store, then re-run over the same dest")
var lines = _prelude("green")
lines.push("scv shadow-sync --dest \"$TMP/shadow\"")
lines.push("printf 'ss1_code=%s\\n' \"$?\"")
lines.push("scv shadow-sync --dest \"$TMP/shadow\"")
lines.push("printf 'ss2_code=%s\\n' \"$?\"")
lines.push("head -1 .scv/meta/shadow_state.sdn")
lines.push("test -f \"$TMP/shadow/HEAD_OP\" && echo shadow_head=present")
val out = _run(lines)
step("Verify replication, the watermark, and the idempotent zero-copy re-run")
expect(out).to_contain("object(s) replicated, 0 up-to-date")
expect(out).to_contain("PASS — 0 object(s) replicated")
expect(out).to_contain("ss1_code=0")
expect(out).to_contain("ss2_code=0")
expect(out).to_contain("shadow_state:")
expect(out).to_contain("shadow_head=present")
expect(out).to_contain("exit=0")
```

</details>

#### replicates only the new objects after a further explicit commit

- replicates only the new objects after a further explicit commit
- Sync, add a file, snapshot again, sync again
- Verify the second sync copies new objects and keeps the old ones up-to-date


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("replicates only the new objects after a further explicit commit")
step("Sync, add a file, snapshot again, sync again")
var lines = _prelude("delta")
lines.push("scv shadow-sync --dest \"$TMP/shadow\" >/dev/null")
lines.push("printf 'gamma\\n' > c.txt")
lines.push("scv snapshot >/dev/null")
lines.push("scv shadow-sync --dest \"$TMP/shadow\"")
lines.push("printf 'ss_code=%s\\n' \"$?\"")
val out = _run(lines)
step("Verify the second sync copies new objects and keeps the old ones up-to-date")
expect(out).to_contain("object(s) replicated")
expect(out).to_contain("up-to-date")
expect(out).to_contain("PASS")
expect(out).to_contain("ss_code=0")
expect(out).to_contain("exit=0")
```

</details>

#### fails closed when a shadow object is corrupted

- fails closed when a shadow object is corrupted
- Corrupt a replicated shadow object, then re-run shadow-sync
- Verify the corruption is named, the exit is 1, and the watermark did not advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed when a shadow object is corrupted")
step("Corrupt a replicated shadow object, then re-run shadow-sync")
var lines = _prelude("corrupt")
lines.push("scv shadow-sync --dest \"$TMP/shadow\" >/dev/null")
lines.push("cp .scv/meta/shadow_state.sdn \"$TMP/state_before\"")
lines.push("CHUNK=$(find \"$TMP/shadow/objects/chunks\" -type f | head -1)")
lines.push("printf 'CORRUPTED' > \"$CHUNK\"")
lines.push("set +e")
lines.push("scv shadow-sync --dest \"$TMP/shadow\"")
lines.push("printf 'ss_code=%s\\n' \"$?\"")
lines.push("set -e")
lines.push("cmp -s .scv/meta/shadow_state.sdn \"$TMP/state_before\" && echo watermark=unchanged || echo watermark=advanced")
val out = _run(lines)
step("Verify the corruption is named, the exit is 1, and the watermark did not advance")
expect(out).to_contain("shadow object corrupted:")
expect(out).to_contain("FAIL — 1 shadow object(s) failed verification; watermark not advanced")
expect(out).to_contain("ss_code=1")
expect(out).to_contain("watermark=unchanged")
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
- `REQ-SCV-SHADOW-REPLICATION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4d20e3c2b76d658a2e498d4e206c02b012dc8fcd4207d5a74ae801e5c789f7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4d20e3c2b76d658a2e498d4e206c02b012dc8fcd4207d5a74ae801e5c789f7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4d20e3c2b76d658a2e498d4e206c02b012dc8fcd4207d5a74ae801e5c789f7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_shadow_replication_spec.spl
mirror: doc/06_spec/integration/app/scv_shadow_replication_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_shadow_replication_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_shadow_replication_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_shadow_replication_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_shadow_replication_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replicates immutable objects and refs, then is idempotent on re-run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_shadow_replication_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replicates only the new objects after a further explicit commit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_shadow_replication_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when a shadow object is corrupted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
