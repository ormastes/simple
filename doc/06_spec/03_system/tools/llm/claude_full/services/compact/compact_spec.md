# Claude Full Compact Service Slice

> Focused Simple coverage for no-I/O compact service helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Compact Service Slice

Focused Simple coverage for no-I/O compact service helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for no-I/O compact service helpers from
services/compact/compact.ts.

## Scenarios

### Claude full compact service parity

#### should model post compact ordering and boundary annotation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model post compact ordering and boundary annotation
- Check compact message ordering
   - Expected: buildPostCompactMessagesRoute(true, 1, 1, 1, true) equals `boundary -> summaries -> kept -> attachments -> hooks`
   - Expected: annotateBoundaryWithPreservedSegmentRoute("boundary", "", "", "") equals `boundary`
   - Expected: annotateBoundaryWithPreservedSegmentRoute("boundary", "h", "a", "t") equals `boundary headUuid=h anchorUuid=a tailUuid=t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model post compact ordering and boundary annotation")
step("Check compact message ordering")
expect(buildPostCompactMessagesRoute(true, 1, 1, 1, true)).to_equal("boundary -> summaries -> kept -> attachments -> hooks")
expect(annotateBoundaryWithPreservedSegmentRoute("boundary", "", "", "")).to_equal("boundary")
expect(annotateBoundaryWithPreservedSegmentRoute("boundary", "h", "a", "t")).to_equal("boundary headUuid=h anchorUuid=a tailUuid=t")
```

</details>

#### should model hook merge and media stripping

- should model hook merge and media stripping
- Check hook and media helpers
   - Expected: mergeHookInstructionsRoute("", "h") equals `h`
   - Expected: mergeHookInstructionsRoute("u", "") equals `u`
   - Expected: mergeHookInstructionsRoute("u", "h") equals `u\n\nh`
   - Expected: stripImagesFromMessagesRoute("assistant", true, true) equals `unchanged`
   - Expected: stripImagesFromMessagesRoute("user", true, false) equals `user media stripped`
   - Expected: stripImagesFromMessagesRoute("user", false, true) equals `nested media stripped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model hook merge and media stripping")
step("Check hook and media helpers")
expect(mergeHookInstructionsRoute("", "h")).to_equal("h")
expect(mergeHookInstructionsRoute("u", "")).to_equal("u")
expect(mergeHookInstructionsRoute("u", "h")).to_equal("u\n\nh")
expect(stripImagesFromMessagesRoute("assistant", true, true)).to_equal("unchanged")
expect(stripImagesFromMessagesRoute("user", true, false)).to_equal("user media stripped")
expect(stripImagesFromMessagesRoute("user", false, true)).to_equal("nested media stripped")
```

</details>

#### should model attachment filtering and error messages

- should model attachment filtering and error messages
- Check attachment and error helpers
   - Expected: stripReinjectedAttachmentsRoute(true, "skill_discovery") equals `removed`
   - Expected: stripReinjectedAttachmentsRoute(true, "skill_listing") equals `removed`
   - Expected: stripReinjectedAttachmentsRoute(false, "skill_listing") equals `kept`
   - Expected: compactReactiveErrorMessageRoute("too_few_groups") equals `Not enough messages to compact`
   - Expected: compactReactiveErrorMessageRoute("aborted") equals `User aborted compaction`
   - Expected: compactReactiveErrorMessageRoute("error") equals `Compaction did not produce a complete response`
   - Expected: compactReactiveErrorMessageRoute("media_unstrippable") equals `Compaction did not produce a complete response`
   - Expected: compactServiceSourceLinesModeled() equals `1705`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model attachment filtering and error messages")
step("Check attachment and error helpers")
expect(stripReinjectedAttachmentsRoute(true, "skill_discovery")).to_equal("removed")
expect(stripReinjectedAttachmentsRoute(true, "skill_listing")).to_equal("removed")
expect(stripReinjectedAttachmentsRoute(false, "skill_listing")).to_equal("kept")
expect(compactReactiveErrorMessageRoute("too_few_groups")).to_equal("Not enough messages to compact")
expect(compactReactiveErrorMessageRoute("aborted")).to_equal("User aborted compaction")
expect(compactReactiveErrorMessageRoute("error")).to_equal("Compaction did not produce a complete response")
expect(compactReactiveErrorMessageRoute("media_unstrippable")).to_equal("Compaction did not produce a complete response")
expect(compactServiceSourceLinesModeled()).to_equal(1705)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd4f397e465c86dcebc8dc0621861ff34e55e60ddd51d6ea11e72fb832d808ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd4f397e465c86dcebc8dc0621861ff34e55e60ddd51d6ea11e72fb832d808ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd4f397e465c86dcebc8dc0621861ff34e55e60ddd51d6ea11e72fb832d808ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/compact/compact_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/compact/compact_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/compact/compact_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model post compact ordering and boundary annotation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model post compact ordering and boundary annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model hook merge and media stripping' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model hook merge and media stripping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model attachment filtering and error messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/compact/compact_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model attachment filtering and error messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
