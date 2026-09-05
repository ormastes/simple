# scv_dual_byte_spec

> Purpose: This spec proves SCV-IMPL-B-03 — the dual-byte content model:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_dual_byte_spec

Purpose: This spec proves SCV-IMPL-B-03 — the dual-byte content model:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_dual_byte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-B-03 — the dual-byte content model:
WorktreeContentId (bytes as they sit in the worktree) vs RepositoryContentId
(bytes after the repository transform), tied together by a TransformId for
EOL/filter/attribute policies. The native default is the identity transform,
under which both ids carry the same payload hash; an unknown TransformId is
an honest ERROR, never a silent identity.
Audience: Maintainers of the SCV native backend.

## Scenarios

### scv dual-byte content model (B-03)

#### defaults to the identity transform natively

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Ask the native backend which transform it uses when none is named


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
step("Ask the native backend which transform it uses when none is named")
expect(scv_transform_default()).to_be("identity")
expect(scv_transform_valid("identity")).to_be(true)
```

</details>

#### knows the EOL policy transforms and rejects unknown ones

- Validate each named transform policy against the registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
step("Validate each named transform policy against the registry")
expect(scv_transform_valid("eol-lf")).to_be(true)
expect(scv_transform_valid("eol-crlf")).to_be(true)
expect(scv_transform_valid("")).to_be(false)
expect(scv_transform_valid("smudge-magic")).to_be(false)
```

</details>

#### identity transform leaves bytes untouched

- Apply the identity transform to mixed-EOL bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
step("Apply the identity transform to mixed-EOL bytes")
val content = "a\r\nb\nc"
expect(scv_apply_transform("identity", content)).to_be(content)
```

</details>

#### eol-lf normalises CRLF to LF; eol-crlf expands LF to CRLF

- eol-crlf does not double-expand an already-CRLF stream
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
expect(scv_apply_transform("eol-lf", "a\r\nb\r\n")).to_be("a\nb\n")
expect(scv_apply_transform("eol-lf", "a\nb\n")).to_be("a\nb\n")
expect(scv_apply_transform("eol-crlf", "a\nb\n")).to_be("a\r\nb\r\n")
step("eol-crlf does not double-expand an already-CRLF stream")
expect(scv_apply_transform("eol-crlf", "a\r\nb\r\n")).to_be("a\r\nb\r\n")
```

</details>

#### errors on an unknown transform instead of silently passing through

- Apply a transform that no policy defines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
step("Apply a transform that no policy defines")
val out = scv_apply_transform("smudge-magic", "abc")
expect(out.starts_with("ERROR")).to_be(true)
```

</details>

#### keeps worktree and repository ids in distinct namespaces

- Under identity the payload hash is shared, only the prefix differs
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
val wt = scv_worktree_content_id("hello\n")
val repo = scv_repository_content_id("identity", "hello\n")
expect(wt.starts_with("wct_")).to_be(true)
expect(repo.starts_with("rep_")).to_be(true)
step("Under identity the payload hash is shared, only the prefix differs")
expect(wt[4:]).to_be(repo[4:])
```

</details>

#### diverges the two ids exactly when the transform changes bytes

- The repository id equals the id of the transformed bytes
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
val crlf = "a\r\nb\r\n"
val wt = scv_worktree_content_id(crlf)
val repo = scv_repository_content_id("eol-lf", crlf)
expect(wt[4:] == repo[4:]).to_be(false)
step("The repository id equals the id of the transformed bytes")
expect(repo[4:]).to_be(scv_repository_content_id("identity", "a\nb\n")[4:])
```

</details>

#### records the full dual-byte triple with an honest transform id

- Record the dual-byte triple for a valid and an invalid transform


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-DUAL-BYTE-001
step("Record the dual-byte triple for a valid and an invalid transform")
val rec = scv_dual_byte_record("eol-lf", "x\r\n")
expect(rec).to_contain("transform: eol-lf")
expect(rec).to_contain("worktree: wct_")
expect(rec).to_contain("repository: rep_")
val bad = scv_dual_byte_record("smudge-magic", "x")
expect(bad.starts_with("ERROR")).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SCV-DUAL-BYTE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `278f090e1cd14970b4373947a4b962d34d4f6fba7797fdc5feaff4d46c54414f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `278f090e1cd14970b4373947a4b962d34d4f6fba7797fdc5feaff4d46c54414f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `278f090e1cd14970b4373947a4b962d34d4f6fba7797fdc5feaff4d46c54414f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_dual_byte_spec.spl
mirror: doc/06_spec/integration/app/scv_dual_byte_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_dual_byte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_dual_byte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_dual_byte_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to the identity transform natively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_dual_byte_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'knows the EOL policy transforms and rejects unknown ones' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_dual_byte_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identity transform leaves bytes untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
