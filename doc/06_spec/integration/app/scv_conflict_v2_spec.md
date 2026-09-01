# scv_conflict_v2_spec

> Purpose: This spec proves SCV-IMPL-D-07 — typed conflict objects v2. Every

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_conflict_v2_spec

Purpose: This spec proves SCV-IMPL-D-07 — typed conflict objects v2. Every

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_conflict_v2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-D-07 — typed conflict objects v2. Every
merge conflict is additionally recorded as a `scv/conflict/v2` DATA object
(separate store `objects/conflicts_v2` — the v1 payloads and `$SCV conflicts`
output stay byte-stable) carrying: kind (content_overlap, signature_conflict,
entity_identity_ambiguous, entity_rename_delete, parser_disagreement), entity
IDs, node sides (base/left/right tree lines), parser identity, the attempted
merge algorithms, and diagnostics. The D-04 rename-vs-rename ceiling is now
NAMED properly: the identity store can attribute only one accepted rename per
EntityId, so when the "deleting" side actually carries an unattributed added
path, the v2 kind is entity_identity_ambiguous (with diagnostics naming the
store ceiling), not entity_rename_delete. parser_disagreement is reachable by
construction (two parser identities disagreeing about the same bytes); no
merge path emits it yet, which the constructor documents honestly.
Audience: Maintainers of the SCV merge engine.

## Scenarios

### scv typed conflict objects v2 (D-07)

#### declares version, kinds, parser identity, and a field-addressable payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Declare the v2 schema surface: version, kinds, parser identity, payload fields
   - Expected: kinds.len() equals `5`
   - Expected: scv_conflict_v2_field(payload, "kind") equals `parser_disagreement`
   - Expected: scv_conflict_v2_field(payload, "entities") equals `file_9`
   - Expected: scv_conflict_v2_field(payload, "attempted") equals `structural-anchor,line`
   - Expected: scv_conflict_v2_payload("a.spl", "bogus_kind", "", "", "", "", "", "") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-CONFLICT-V2-001, REQ-SSPEC-INTEGRATION
step("Declare the v2 schema surface: version, kinds, parser identity, payload fields")
expect(scv_conflict_v2_version()).to_contain("scv/conflict/v2")
val kinds = scv_conflict_v2_kinds()
# oracle: exactly 5 kinds — the closed set content_overlap, signature_conflict, entity_identity_ambiguous, entity_rename_delete, parser_disagreement
expect(kinds.len()).to_equal(5)
var joined = ""
for k in kinds:
    joined = joined + k + "\n"
expect(joined).to_contain("content_overlap")
expect(joined).to_contain("entity_identity_ambiguous")
expect(joined).to_contain("entity_rename_delete")
expect(joined).to_contain("signature_conflict")
expect(joined).to_contain("parser_disagreement")
expect(scv_conflict_v2_parser_identity()).to_contain("scv-text-blocks/v1")
val payload = scv_conflict_v2_payload("a.spl", "parser_disagreement", "file_9", "a.txt|f|c1|3|0", "a.txt|f|c2|3|0", "a.txt|f|c3|3|0", "structural-anchor,line", "two parser identities disagree; reachable by construction only today")
expect(payload).to_contain("schema: scv/conflict/v2")
expect(scv_conflict_v2_field(payload, "kind")).to_equal("parser_disagreement")
expect(scv_conflict_v2_field(payload, "entities")).to_equal("file_9")
expect(scv_conflict_v2_field(payload, "attempted")).to_equal("structural-anchor,line")
expect(scv_conflict_v2_field(payload, "parser")).to_contain("scv-text-blocks/v1")
expect(scv_conflict_v2_field(payload, "left")).to_contain("c2")
# an unknown kind is refused, never stored mislabeled
expect(scv_conflict_v2_payload("a.spl", "bogus_kind", "", "", "", "", "", "")).to_equal("")
```

</details>

#### classifies both-sides signature change as signature_conflict, body overlap as content_overlap

- Classify left/right variants against the base text block
   - Expected: scv_conflict_v2_classify(base, sig_left, sig_right) equals `signature_conflict`
   - Expected: scv_conflict_v2_classify(base, body_left, body_right) equals `content_overlap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-CONFLICT-V2-001
step("Classify left/right variants against the base text block")
val base = "fn alpha(x: i64) -> i64:\n    1\n"
val sig_left = "fn alpha(x: i64, y: i64) -> i64:\n    1\n"
val sig_right = "fn alpha(x: text) -> i64:\n    1\n"
expect(scv_conflict_v2_classify(base, sig_left, sig_right)).to_equal("signature_conflict")
val body_left = "fn alpha(x: i64) -> i64:\n    10\n"
val body_right = "fn alpha(x: i64) -> i64:\n    99\n"
expect(scv_conflict_v2_classify(base, body_left, body_right)).to_equal("content_overlap")
```

</details>

#### a merge content conflict writes a v2 object with kind, sides, parser identity and attempted algorithms

- Both sides edit line 1 of a.txt differently -> conflict; v2 object recorded beside v1
   - Expected: out does not contain `NO-V2-OBJECTS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-CONFLICT-V2-001
step("Both sides edit line 1 of a.txt differently -> conflict; v2 object recorded beside v1")
val script = _prologue("overlap") + "printf 'LEFT\\ntwo\\nthree\\n' > a.txt\nLEFT=$($SCV snapshot | head -1 | awk '{print $2}')\n$SCV restore-op \"$BASE_OP\" >/dev/null\nprintf 'RIGHT\\ntwo\\nthree\\n' > a.txt\nRIGHT=$($SCV snapshot | head -1 | awk '{print $2}')\n$SCV merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\ncat .scv/objects/conflicts_v2/* 2>/dev/null || echo 'NO-V2-OBJECTS'\n"
val out = _run_script(script)
expect(out).to_contain("conflicts=1")
expect(out).to_contain("schema: scv/conflict/v2")
expect(out).to_contain("kind: content_overlap")
expect(out).to_contain("parser: scv-text-blocks/v1")
expect(out).to_contain("attempted: syntax-node,line")
expect(out).to_contain("path: a.txt")
expect(out.contains("NO-V2-OBJECTS")).to_equal(false)
```

</details>

#### names the D-04 rename-vs-rename ceiling properly: v2 kind is entity_identity_ambiguous, v1 stays byte-stable

- Left renames a.txt->left.txt; right renames a.txt->right.txt (unattributable second rename)
   - Expected: out does not contain `NO-V2-OBJECTS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-CONFLICT-V2-001
step("Left renames a.txt->left.txt; right renames a.txt->right.txt (unattributable second rename)")
val script = _prologue("rename-rename") + "mv a.txt left.txt\nLEFT=$($SCV snapshot --rename a.txt left.txt | head -1 | awk '{print $2}')\n$SCV restore-op \"$BASE_OP\" >/dev/null\nmv a.txt right.txt\nprintf 'one\\ntwo\\nTHREE\\n' > right.txt\nRIGHT=$($SCV snapshot --rename a.txt right.txt | head -1 | awk '{print $2}')\n$SCV merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\n$SCV conflicts\necho '--V2--'\ncat .scv/objects/conflicts_v2/* 2>/dev/null || echo 'NO-V2-OBJECTS'\n"
val out = _run_script(script)
# v1 surface unchanged (identity spec pins these):
expect(out).to_contain("conflicts=1")
expect(out).to_contain("kind: entity_rename_delete")
# v2 names the ambiguity, with entity id and diagnostics:
expect(out).to_contain("kind: entity_identity_ambiguous")
expect(out).to_contain("entities: file_1")
expect(out).to_contain("identity store attributes only one accepted rename per EntityId")
expect(out.contains("NO-V2-OBJECTS")).to_equal(false)
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
- `REQ-SCV-CONFLICT-V2-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e220b8b10bfb996d3306a4bed316ec4482f07f4337f059bbb5f3e1708837cd30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e220b8b10bfb996d3306a4bed316ec4482f07f4337f059bbb5f3e1708837cd30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e220b8b10bfb996d3306a4bed316ec4482f07f4337f059bbb5f3e1708837cd30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/app/scv_conflict_v2_spec.spl
mirror: doc/06_spec/integration/app/scv_conflict_v2_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_conflict_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_conflict_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_conflict_v2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_conflict_v2_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares version, kinds, parser identity, and a field-addressable payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_conflict_v2_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies both-sides signature change as signature_conflict, body overlap as content_overlap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_conflict_v2_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a merge content conflict writes a v2 object with kind, sides, parser identity and attempted algorithms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
