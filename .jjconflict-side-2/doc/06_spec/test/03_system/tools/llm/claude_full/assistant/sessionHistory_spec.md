# Claude Full Assistant Session History

> Mirrors `tmp/claude/claude-code-main/src/assistant/sessionHistory.ts` for the

<!-- sdn-diagram:id=sessionHistory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sessionHistory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sessionHistory_spec -> std
sessionHistory_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sessionHistory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/assistant/sessionHistory.ts` for the
small session-history slice: auth context construction, latest/older request
parameters, non-200 null pages, and page response normalization.

## Scenarios

### Claude full assistant sessionHistory

#### builds the BYOC session history auth context

- Create a reusable history context from OAuth request outputs
   - Expected: ctx.baseUrl equals `https://api.anthropic.test/v1/sessions/sess_123/events`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a reusable history context from OAuth request outputs")
val ctx = createHistoryAuthCtx("sess_123", "https://api.anthropic.test", "tok_abc", "org_9")
expect(ctx.baseUrl).to_equal("https://api.anthropic.test/v1/sessions/sess_123/events")
expect(ctx.headers).to_contain("Authorization: Bearer tok_abc")
expect(ctx.headers).to_contain("anthropic-beta: ccr-byoc-2025-07-29")
expect(ctx.headers).to_contain("x-organization-uuid: org_9")
```

</details>

#### normalizes successful event pages and treats null first_id as empty cursor

- Parse Claude's session events response into a history page shape
   - Expected: parsed.data.len() equals `1`
   - Expected: parsed.data[0].raw equals `{"id":"evt_1"}`
   - Expected: parsed.has_more is false
   - Expected: parsed.first_id equals ``
   - Expected: parsed.last_id equals `evt_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Fetch the newest chronological page using Claude's anchor_to_latest parameter
   - Expected: latestEventsParams(0) equals `limit=" + HISTORY_PAGE_SIZE.to_text() + "&anchor_to_latest=true`
- Some
   - Expected: p.events.len() equals `2`
   - Expected: p.firstId equals `evt_1`
   - Expected: p.hasMore is true
   - Expected: "missing page" equals `present page`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Fetch events immediately before Claude's firstId cursor
   - Expected: olderEventsParams("evt_before", 25) equals `limit=25&before_id=evt_before`
- Some
   - Expected: p.hasMore is true
   - Expected: "missing page" equals `present page`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Preserve Claude's null page behavior for failed HTTP responses
- Some
   - Expected: "nil" equals `page`
   - Expected: captured_request.label equals `fetchLatestEvents`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
