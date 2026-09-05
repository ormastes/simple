# scv_identity_merge_spec

> Purpose: This spec proves SCV-IMPL-D-04 — identity-aware merge. A logical

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_identity_merge_spec

Purpose: This spec proves SCV-IMPL-D-04 — identity-aware merge. A logical

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_identity_merge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-D-04 — identity-aware merge. A logical
file renamed on one side (accepted FileEntityId move) and edited on the other
is merged by EntityId, not by path or by exact-chunk coincidence: the edit
lands at the renamed path. Rename-vs-rename and rename-vs-delete on the same
EntityId are recorded as typed conflict DATA (jj stays the conflict-storage
authority; SCV never invents a clean merge for them).
Audience: Maintainers of the SCV merge engine.

## Scenarios

### scv identity-aware merge (D-04)

#### merges a hint-accepted rename+edit on one side with an edit on the other via EntityId

**Manual warnings:**
- invalid manual visibility metadata: # @manual scv-identity-aware-merge (expected show, folded, detail, or skip)


- Left renames a.txt -> moved.txt AND edits line 1 (accepted move edge, content differs from base)
   - Protocol capture: after_step
- Right edits line 3 of a.txt at the base path


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-IDENTITY-MERGE-001
step("Left renames a.txt -> moved.txt AND edits line 1 (accepted move edge, content differs from base)")
step("Right edits line 3 of a.txt at the base path")
val script = _prologue("rename-edit") + "mv a.txt moved.txt\nprintf 'ONE\\ntwo\\nthree\\n' > moved.txt\nLEFT_OUT=$($SCV snapshot --rename a.txt moved.txt)\nprintf '%s\\n' \"$LEFT_OUT\"\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | head -1 | awk '{print $2}')\n$SCV restore-op \"$BASE_OP\" >/dev/null\nprintf 'one\\ntwo\\nTHREE\\n' > a.txt\nRIGHT=$($SCV snapshot | head -1 | awk '{print $2}')\n$SCV merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\n$SCV export-tree out >/dev/null\ntest ! -e out/a.txt\nprintf 'moved=%s\\n' \"$(cat out/moved.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("move a.txt -> moved.txt")
expect(out).to_contain("status=accepted")
expect(out).to_contain("conflicts=0")
expect(out).to_contain("a.txt: identity-rename-source")
expect(out).to_contain("moved.txt: identity-rename-edit")
expect(out).to_contain("moved=ONE|two|THREE|")
expect(out).to_contain("exit=0")
```

</details>

#### never silently merges rename-vs-rename: the second rename is a typed conflict, nothing is dropped

- Rename a.txt on both sides, then ask merge-commits and conflicts what happened


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-IDENTITY-MERGE-001
step("Rename a.txt on both sides, then ask merge-commits and conflicts what happened")
# The linear identity store (I-02) can attribute only ONE accepted
# rename per EntityId: after the left rename, `--rename a.txt right.txt`
# on the right finds no live id at a.txt, so right.txt carries no entity.
# The identity pre-pass therefore sees file_1 renamed-left / gone-right
# and records conflict DATA rather than inventing a clean merge; the
# unattributed right.txt survives on the path-based route. The strategy
# label `identity-rename-delete` reflects the STORE's view, not ground
# truth; SCV-IMPL-D-07 typed conflicts own the naming.
# TODO(I-04): with lane C's relations API both renames become
# attributable and this case is the entity_identity_ambiguous kind.
val script = _prologue("rename-rename") + "mv a.txt left.txt\nLEFT=$($SCV snapshot --rename a.txt left.txt | head -1 | awk '{print $2}')\n$SCV restore-op \"$BASE_OP\" >/dev/null\nmv a.txt right.txt\nprintf 'one\\ntwo\\nTHREE\\n' > right.txt\nRIGHT=$($SCV snapshot --rename a.txt right.txt | head -1 | awk '{print $2}')\n$SCV merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\n$SCV conflicts\n"
val out = _run_script(script)
expect(out).to_contain("conflicts=1")
expect(out).to_contain("a.txt: identity-rename-source")
expect(out).to_contain("left.txt: identity-rename-delete conflict entity=file_1")
expect(out).to_contain("right.txt: right-only")
expect(out).to_contain("kind: entity_rename_delete")
expect(out).to_contain("entity: file_1")
expect(out).to_contain("exit=0")
```

</details>

#### records rename-vs-delete of one EntityId as conflict data instead of silently dropping it

- Rename a.txt on the left, delete it on the right, then merge and read the conflict record


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-IDENTITY-MERGE-001
step("Rename a.txt on the left, delete it on the right, then merge and read the conflict record")
val script = _prologue("rename-delete") + "mv a.txt moved.txt\nprintf 'ONE\\ntwo\\nthree\\n' > moved.txt\nLEFT=$($SCV snapshot --rename a.txt moved.txt | head -1 | awk '{print $2}')\n$SCV restore-op \"$BASE_OP\" >/dev/null\nrm a.txt\nprintf 'keep\\n' > other.txt\nRIGHT=$($SCV snapshot | head -1 | awk '{print $2}')\n$SCV merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\n$SCV conflicts\n"
val out = _run_script(script)
expect(out).to_contain("conflicts=1")
expect(out).to_contain("identity-rename-delete")
expect(out).to_contain("kind: entity_rename_delete")
expect(out).to_contain("other.txt: right-only")
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

- `REQ-SCV-IDENTITY-MERGE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0bd58ff309a10309804e5d80772e9fa06ad88b44b53564c753970b21d9fb4903`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0bd58ff309a10309804e5d80772e9fa06ad88b44b53564c753970b21d9fb4903`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0bd58ff309a10309804e5d80772e9fa06ad88b44b53564c753970b21d9fb4903`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/scv_identity_merge_spec.spl
mirror: doc/06_spec/02_integration/app/scv_identity_merge_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_identity_merge_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/02_integration/app/scv_identity_merge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_identity_merge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
