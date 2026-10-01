# scv_fsck_strong_spec

> Purpose: This spec proves the strengthened `scv fsck` (SCV-MIG-09): a freshly

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_fsck_strong_spec

Purpose: This spec proves the strengthened `scv fsck` (SCV-MIG-09): a freshly

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_fsck_strong_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the strengthened `scv fsck` (SCV-MIG-09): a freshly
initialized repo is fully clean (including the parser lock, which init now
writes in the modern 8-field format), full checkpoint verification recomputes
manifest and payload hashes, change objects are format-2 validated (state must
be open|closed, latest must resolve), and a legacy 3-line parser lock is
reported STALE rather than failing fsck.
Audience: Maintainers of the SCV integrity layer (scv_v2_final_report §14/§18.1).

## Scenarios

### scv fsck strong (SCV-MIG-09)

#### is fully clean on a fresh repo, including the parser lock

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is fully clean on a fresh repo, including the parser lock
- Init, snapshot, checkpoint, then fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is fully clean on a fresh repo, including the parser lock")
step("Init, snapshot, checkpoint, then fsck")
var lines = _prelude("clean")
lines.push("scv checkpoint >/dev/null")
lines.push("scv fsck")
val out = _run(lines)
expect(out).to_contain("OK checked=")
expect(out).to_contain("exit=0")
```

</details>

#### fails when a checkpoint payload file is corrupted

- fails when a checkpoint payload file is corrupted
- Create a checkpoint, corrupt one payload file, fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails when a checkpoint payload file is corrupted")
step("Create a checkpoint, corrupt one payload file, fsck")
var lines = _prelude("ckpt")
lines.push("scv checkpoint >/dev/null")
lines.push("F=$(find .scv/checkpoints/*/data -type f | head -n 1)")
lines.push("printf 'corrupted' >> \"$F\"")
lines.push("scv fsck || true")
val out = _run(lines)
expect(out).to_contain("checkpoint file hash mismatch")
```

</details>

#### fails on a change object with an invalid state

- fails on a change object with an invalid state
- Rewrite a change record with a bogus state, fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails on a change object with an invalid state")
step("Rewrite a change record with a bogus state, fsck")
var lines = _prelude("state")
lines.push("CH=$(ls .scv/objects/changes | head -n 1)")
lines.push("sed -i 's/^state: .*/state: bogus/' \".scv/objects/changes/$CH\"")
lines.push("scv fsck || true")
val out = _run(lines)
expect(out).to_contain("bad change state")
```

</details>

#### reports a legacy 3-line parser lock as STALE, not FAIL

- reports a legacy 3-line parser lock as STALE, not FAIL
- Overwrite the parser lock with the legacy header form, fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports a legacy 3-line parser lock as STALE, not FAIL")
step("Overwrite the parser lock with the legacy header form, fsck")
var lines = _prelude("legacy")
lines.push("printf 'language: fallback-line\\nruntime: pure-simple\\nversion: builtin\\n' > .scv/meta/parsers.sdn")
lines.push("scv fsck")
val out = _run(lines)
expect(out).to_contain("OK checked=")
expect(out).to_contain("stale=parser-lock")
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
- `REQ-SCV-FSCK-STRONG-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d467c1b5f4ba813f9a8e5fe8384e2925d73588273991a743e159ff2429a1ed37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d467c1b5f4ba813f9a8e5fe8384e2925d73588273991a743e159ff2429a1ed37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d467c1b5f4ba813f9a8e5fe8384e2925d73588273991a743e159ff2429a1ed37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_fsck_strong_spec.spl
mirror: doc/06_spec/integration/app/scv_fsck_strong_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_fsck_strong_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_fsck_strong_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_fsck_strong_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_fsck_strong_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is fully clean on a fresh repo, including the parser lock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_fsck_strong_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails when a checkpoint payload file is corrupted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_fsck_strong_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails on a change object with an invalid state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
