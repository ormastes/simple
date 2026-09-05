# scv_recover_levels_spec

> Purpose: This spec proves `scv recover --level 0..5` (MIG-22, stabilization

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_recover_levels_spec

Purpose: This spec proves `scv recover --level 0..5` (MIG-22, stabilization

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_recover_levels_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv recover --level 0..5` (MIG-22, stabilization
§12): 0 rebuilds derived indexes, 1 rebuilds the DB from journal/objects,
2 reconstructs heads from the operation DAG, 3 reconstructs from a git backend
checkout, 4 restores a checkpoint and replays the journal after it, and 5 is a
report-only statement of what GitHub-only recovery preserves/loses. Levels 0-4
inject the matching damage first and must end doctor PASS + fsck OK; the house
verdict is always the last line.
Audience: Maintainers of the SCV storage layer.

## Scenarios

### scv recover levels (MIG-22)

#### level 0 rebuilds derived indexes after they are deleted

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- level 0 rebuilds derived indexes after they are deleted
- Delete status/object/parser indexes, recover --level 0, doctor PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("level 0 rebuilds derived indexes after they are deleted")
step("Delete status/object/parser indexes, recover --level 0, doctor PASS")
var lines = _harness()
lines.push("rm -f .scv/meta/status_index.sdn .scv/meta/object_index.sdn .scv/meta/parser_index.sdn")
lines.push("scv recover --level 0")
lines.push("test -f .scv/meta/status_index.sdn && printf 'status_index=rebuilt\\n'")
val out = _run(lines)
expect(out).to_contain("PASS — recover level 0 complete (doctor PASS, fsck OK)")
expect(out).to_contain("status_index=rebuilt")
expect(out).to_contain("exit=0")
```

</details>

#### level 1 rebuilds the DB from journal and objects

- level 1 rebuilds the DB from journal and objects
- Delete DB-derived meta, recover --level 1, doctor PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("level 1 rebuilds the DB from journal and objects")
step("Delete DB-derived meta, recover --level 1, doctor PASS")
var lines = _harness()
lines.push("rm -f .scv/meta/status_index.sdn .scv/meta/object_index.sdn")
lines.push("scv recover --level 1")
lines.push("test -f .scv/meta/status_index.sdn && printf 'db=rebuilt\\n'")
val out = _run(lines)
expect(out).to_contain("PASS — recover level 1 complete (doctor PASS, fsck OK)")
expect(out).to_contain("db=rebuilt")
expect(out).to_contain("exit=0")
```

</details>

#### level 2 reconstructs heads from the operation DAG

- level 2 reconstructs heads from the operation DAG
- Two snapshots, delete HEAD_OP, recover --level 2 restores the newest tip


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("level 2 reconstructs heads from the operation DAG")
step("Two snapshots, delete HEAD_OP, recover --level 2 restores the newest tip")
var lines = _harness()
lines.push("printf 'v2\\n' > a.txt")
lines.push("scv snapshot >/dev/null")
lines.push("rm -f .scv/HEAD_OP")
lines.push("scv recover --level 2")
lines.push("test -s .scv/HEAD_OP && printf 'head=reconstructed\\n'")
val out = _run(lines)
expect(out).to_contain("head reconstructed from operation DAG: op_")
expect(out).to_contain("PASS — recover level 2 complete (doctor PASS, fsck OK)")
expect(out).to_contain("head=reconstructed")
expect(out).to_contain("exit=0")
```

</details>

#### level 3 reconstructs a fresh repository from a git backend

- level 3 reconstructs a fresh repository from a git backend
- Fresh dir plus a git checkout as source, recover --level 3 --git


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("level 3 reconstructs a fresh repository from a git backend")
step("Fresh dir plus a git checkout as source, recover --level 3 --git")
var lines = _harness()
lines.push("GIT=$(mktemp -d /tmp/scv-recover-git.XXXXXX)")
lines.push("git -C \"$GIT\" init -q .")
lines.push("printf 'from-git\\n' > \"$GIT/f.txt\"")
lines.push("git -C \"$GIT\" add .")
lines.push("git -C \"$GIT\" -c user.email=t@t -c user.name=t commit -qm seed")
lines.push("FRESH=$(mktemp -d /tmp/scv-recover-fresh.XXXXXX)")
lines.push("cd \"$FRESH\"")
lines.push("scv recover --level 3 --git \"$GIT\"")
lines.push("test \"$(cat f.txt)\" = 'from-git' && printf 'worktree=imported\\n'")
val out = _run(lines)
expect(out).to_contain("imported 1 file(s) from git backend")
expect(out).to_contain("PASS — recover level 3 complete (doctor PASS, fsck OK)")
expect(out).to_contain("worktree=imported")
expect(out).to_contain("exit=0")
```

</details>

#### level 4 restores a checkpoint and replays the post-checkpoint journal

- level 4 restores a checkpoint and replays the post-checkpoint journal
- Checkpoint, snapshot after it, delete head/meta, recover --level 4 --checkpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("level 4 restores a checkpoint and replays the post-checkpoint journal")
step("Checkpoint, snapshot after it, delete head/meta, recover --level 4 --checkpoint")
var lines = _harness()
lines.push("CP=$(scv checkpoint | awk '{print $2}')")
lines.push("printf 'post\\n' > a.txt")
lines.push("scv snapshot >/dev/null")
lines.push("POST_OP=$(cat .scv/HEAD_OP)")
lines.push("rm -f .scv/HEAD_OP .scv/meta/workspaces.sdn .scv/meta/status_index.sdn")
lines.push("scv recover --level 4 --checkpoint \"$CP\"")
lines.push("test \"$(cat .scv/HEAD_OP)\" = \"$POST_OP\" && printf 'journal=replayed-past-checkpoint\\n'")
val out = _run(lines)
expect(out).to_contain("restored ")
expect(out).to_contain("journal replay advanced HEAD_OP to op_")
expect(out).to_contain("PASS — recover level 4 complete (doctor PASS, fsck OK)")
expect(out).to_contain("journal=replayed-past-checkpoint")
expect(out).to_contain("exit=0")
```

</details>

#### level 5 reports what GitHub-only recovery would preserve and lose

- level 5 reports what GitHub-only recovery would preserve and lose
- Report-only: names preserved source history and lost semantic history, modifies nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("level 5 reports what GitHub-only recovery would preserve and lose")
step("Report-only: names preserved source history and lost semantic history, modifies nothing")
var lines = _harness()
lines.push("BEFORE=$(find .scv -type f | wc -l)")
lines.push("scv recover --level 5")
lines.push("AFTER=$(find .scv -type f | wc -l)")
lines.push("test \"$BEFORE\" = \"$AFTER\" && printf 'repo=untouched\\n'")
val out = _run(lines)
expect(out).to_contain("preserved: source files and git commit history")
expect(out).to_contain("lost: changes=")
expect(out).to_contain("PASS — recover level 5 report complete")
expect(out).to_contain("repo=untouched")
expect(out).to_contain("exit=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-RECOVER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7f1f5489f26c9bfe3162df7fc352c0e39e148af4e63b2e40046de4983d4dfc1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7f1f5489f26c9bfe3162df7fc352c0e39e148af4e63b2e40046de4983d4dfc1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7f1f5489f26c9bfe3162df7fc352c0e39e148af4e63b2e40046de4983d4dfc1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_recover_levels_spec.spl
mirror: doc/06_spec/integration/app/scv_recover_levels_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_recover_levels_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_recover_levels_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_recover_levels_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_recover_levels_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'level 0 rebuilds derived indexes after they are deleted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_recover_levels_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'level 1 rebuilds the DB from journal and objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_recover_levels_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'level 2 reconstructs heads from the operation DAG' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
