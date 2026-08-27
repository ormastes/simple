# Claude Full Assistant Session History

> Mirrors `tmp/claude/claude-code-main/src/assistant/sessionHistory.ts` for the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Assistant Session History

Mirrors `tmp/claude/claude-code-main/src/assistant/sessionHistory.ts` for the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/assistant/sessionHistory.ts` for the
small session-history slice: auth context construction, latest/older request
parameters, non-200 null pages, and page response normalization.

## Scenarios

### Claude full assistant sessionHistory

#### builds the BYOC session history auth context

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds the BYOC session history auth context
- Create a reusable history context from OAuth request outputs
   - Expected: ctx.baseUrl equals `https://api.anthropic.test/v1/sessions/sess_123/events`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds the BYOC session history auth context")
step("Create a reusable history context from OAuth request outputs")
val ctx = createHistoryAuthCtx("sess_123", "https://api.anthropic.test", "tok_abc", "org_9")
expect(ctx.baseUrl).to_equal("https://api.anthropic.test/v1/sessions/sess_123/events")
expect(ctx.headers).to_contain("Authorization: Bearer tok_abc")
expect(ctx.headers).to_contain("anthropic-beta: ccr-byoc-2025-07-29")
expect(ctx.headers).to_contain("x-organization-uuid: org_9")
```

</details>

#### normalizes successful event pages and treats null first_id as empty cursor

- normalizes successful event pages and treats null first_id as empty cursor
- Parse Claude's session events response into a history page shape
   - Expected: parsed.data.len() equals `1`
   - Expected: parsed.data[0].raw equals `{"id":"evt_1"}`
   - Expected: parsed.has_more is false
   - Expected: parsed.first_id equals ``
   - Expected: parsed.last_id equals `evt_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes successful event pages and treats null first_id as empty cursor")
step("Parse Claude's session events response into a history page shape")
val parsed = parseSessionEventsResponse("{\"data\":[{\"id\":\"evt_1\"}],\"has_more\":false,\"first_id\":null,\"last_id\":\"evt_1\"}")
expect(parsed.data.len()).to_equal(1)
expect(parsed.data[0].raw).to_equal("{\"id\":\"evt_1\"}")
expect(parsed.has_more).to_equal(false)
expect(parsed.first_id).to_equal("")
expect(parsed.last_id).to_equal("evt_1")
```

</details>

#### requests the latest page with anchor_to_latest and default page size

- requests the latest page with anchor_to_latest and default page size
- Fetch the newest chronological page using Claude's anchor_to_latest parameter
   - Expected: latestEventsParams(0) equals `limit=" + HISTORY_PAGE_SIZE.to_text() + "&anchor_to_latest=true`
   - Expected: p.events.len() equals `2`
   - Expected: p.firstId equals `evt_1`
   - Expected: p.hasMore is true
   - Expected: "missing page" equals `present page`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requests the latest page with anchor_to_latest and default page size")
step("Fetch the newest chronological page using Claude's anchor_to_latest parameter")
val ctx = createHistoryAuthCtx("sess_123", "https://api.anthropic.test", "tok_abc", "org_9")
expect(latestEventsParams(0)).to_equal("limit=" + HISTORY_PAGE_SIZE.to_text() + "&anchor_to_latest=true")
val page = fetchPage(ctx, latestEventsParams(0), "fetchLatestEvents", ok_fetcher)
match page:
    Some(p):
        expect(p.events.len()).to_equal(2)
        expect(p.events[1].raw).to_contain("hi, comma ok")
        expect(p.firstId).to_equal("evt_1")
        expect(p.hasMore).to_equal(true)
    nil:
        expect("missing page").to_equal("present page")
```

</details>

#### requests the older page before the supplied cursor

- requests the older page before the supplied cursor
- Fetch events immediately before Claude's firstId cursor
   - Expected: olderEventsParams("evt_before", 25) equals `limit=25&before_id=evt_before`
   - Expected: p.hasMore is true
   - Expected: "missing page" equals `present page`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requests the older page before the supplied cursor")
step("Fetch events immediately before Claude's firstId cursor")
val ctx = createHistoryAuthCtx("sess_abc", "https://api.anthropic.test", "tok_xyz", "org_2")
expect(olderEventsParams("evt_before", 25)).to_equal("limit=25&before_id=evt_before")
val page = fetchPage(ctx, olderEventsParams("evt_before", 25), "fetchOlderEvents", ok_fetcher)
match page:
    Some(p):
        expect(p.events[0].raw).to_contain("\"type\":\"user\"")
        expect(p.hasMore).to_equal(true)
    nil:
        expect("missing page").to_equal("present page")
```

</details>

#### returns nil for non-200 history responses

- returns nil for non-200 history responses
- Preserve Claude's null page behavior for failed HTTP responses
   - Expected: "nil" equals `page`
   - Expected: captured_request.label equals `fetchLatestEvents`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for non-200 history responses")
step("Preserve Claude's null page behavior for failed HTTP responses")
val ctx = createHistoryAuthCtx("sess_abc", "https://api.anthropic.test", "tok_xyz", "org_2")
val page = fetchPage(ctx, "limit=1", "fetchLatestEvents", bad_fetcher)
match page:
    Some(_p):
        expect("nil").to_equal("page")
    nil:
        expect(captured_request.label).to_equal("fetchLatestEvents")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `55af66923e6928af85e7d116f1ae26bf111ae56f66700c096a80d831bafb42d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55af66923e6928af85e7d116f1ae26bf111ae56f66700c096a80d831bafb42d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55af66923e6928af85e7d116f1ae26bf111ae56f66700c096a80d831bafb42d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the BYOC session history auth context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes successful event pages and treats null first_id as empty cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/assistant/sessionHistory_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requests the latest page with anchor_to_latest and default page size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
