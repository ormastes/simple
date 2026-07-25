# Claude Full First Party Event Logging Exporter

> This SSpec pins the Claude CLI `FirstPartyEventLoggingExporter` parity slice in Simple. It checks that the exporter keeps the same public telemetry contract: only OpenTelemetry event-scope logs are transformed, GrowthBook experiment logs use their own envelope, internal Claude Code events retain event names and safe metadata, failed POSTs are queued, auth is skipped or retried according to the source rules, queued failures are drained when the endpoint becomes healthy, and shutdown stops further exports.

<!-- sdn-diagram:id=firstPartyEventLoggingExporter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=firstPartyEventLoggingExporter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

firstPartyEventLoggingExporter_spec -> their own envelope, internal Claude Code events retain event names and safe
firstPartyEventLoggingExporter_spec -> std
firstPartyEventLoggingExporter_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=firstPartyEventLoggingExporter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full First Party Event Logging Exporter

This SSpec pins the Claude CLI `FirstPartyEventLoggingExporter` parity slice in Simple. It checks that the exporter keeps the same public telemetry contract: only OpenTelemetry event-scope logs are transformed, GrowthBook experiment logs use their own envelope, internal Claude Code events retain event names and safe metadata, failed POSTs are queued, auth is skipped or retried according to the source rules, queued failures are drained when the endpoint becomes healthy, and shutdown stops further exports.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - parity lane for upstream Claude CLI source surface. |
| Plan | N/A - targeted parity slice selected by strict checker output. |
| Design | N/A - implementation mirrors |
| Research | N/A - local upstream TypeScript source is the controlling |
| Source | `test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This SSpec pins the Claude CLI `FirstPartyEventLoggingExporter` parity slice in
Simple. It checks that the exporter keeps the same public telemetry contract:
only OpenTelemetry event-scope logs are transformed, GrowthBook experiment logs
use their own envelope, internal Claude Code events retain event names and safe
metadata, failed POSTs are queued, auth is skipped or retried according to the
source rules, queued failures are drained when the endpoint becomes healthy, and
shutdown stops further exports.

The Simple implementation is deterministic and in-memory. Network calls are
represented by a planned `postPlan`, failed JSONL storage is represented by the
`queued` and `previousFiles` arrays, and scheduled timers are represented by
`scheduledDelays`. That keeps the spec fast while still checking the branch
logic that matters for source parity.

## Requirements

**Requirements:** N/A - parity lane for upstream Claude CLI source surface.
**Plan:** N/A - targeted parity slice selected by strict checker output.
**Design:** N/A - implementation mirrors
`tmp/claude/claude-code-main/src/services/analytics/firstPartyEventLoggingExporter.ts`.
**Research:** N/A - local upstream TypeScript source is the controlling
reference.

## Syntax

Each scenario uses modern SSpec `describe`, `it`, `step`, and focused
`expect(...).to_equal(...)` / `to_contain(...)` assertions. The spec avoids
placeholder passes and uses only deterministic in-memory fixtures.

## Examples

Run this focused spec with:

`bin/simple test test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl --mode=interpreter`

Regenerate the manual with:

`bin/simple spipe-docgen test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl`

## Scenarios

### Claude full FirstPartyEventLoggingExporter

#### should build default endpoint and transform only event scope logs

- Create mixed scope logs
- FirstPartyReadableLogRecord event
- FirstPartyReadableLogRecord otherScope
- FirstPartyReadableLogRecord growthbook
   - Expected: exporter.endpoint equals `https://api.anthropic.com/api/event_logging/batch`
   - Expected: events.len() equals `2`
   - Expected: events[0].eventType equals `ClaudeCodeInternalEvent`
   - Expected: events[1].eventType equals `GrowthbookExperimentEvent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create mixed scope logs")
val exporter = firstPartyExporterDefault()
val logs = [
    FirstPartyReadableLogRecord.event("tool_call", "evt-1"),
    FirstPartyReadableLogRecord.otherScope("ignored"),
    FirstPartyReadableLogRecord.growthbook("gb-1", "experiment-a"),
]
val events = exporter.transformLogsToEvents(logs)
expect(exporter.endpoint).to_equal("https://api.anthropic.com/api/event_logging/batch")
expect(events.len()).to_equal(2)
expect(events[0].eventType).to_equal("ClaudeCodeInternalEvent")
expect(events[1].eventType).to_equal("GrowthbookExperimentEvent")
```

</details>

#### should emit transform error when core metadata is missing

- Transform a log without core metadata
- var log = FirstPartyReadableLogRecord event
   - Expected: events[0].eventName equals `body-name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Transform a log without core metadata")
val exporter = firstPartyExporterDefault()
var log = FirstPartyReadableLogRecord.event("", "evt-2")
log.body = "body-name"
log.coreMetadata = false
val events = exporter.transformLogsToEvents([log])
expect(events[0].eventName).to_equal("body-name")
expect(events[0].eventData).to_contain("transform_error")
```

</details>

#### should strip proto metadata from additional metadata

- Transform a log with hoisted proto keys
- var log = FirstPartyReadableLogRecord event


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Transform a log with hoisted proto keys")
val exporter = firstPartyExporterDefault()
var log = FirstPartyReadableLogRecord.event("startup", "evt-3")
log.userEmail = "a@example.com"
log.protoSkillName = "skill-a"
log.additionalMetadata = "safe=1,_PROTO_secret=drop"
val events = exporter.transformLogsToEvents([log])
expect(events[0].eventData).to_contain("skill:skill-a")
expect(events[0].eventData).to_contain("additional:safe=1,")
```

</details>

#### should chunk posts and short circuit remaining batches after failure

- Export three events with max batch size two and a failing first post
- exporter postPlan = [FirstPartyPostResult fail
- FirstPartyReadableLogRecord event
- FirstPartyReadableLogRecord event
- FirstPartyReadableLogRecord event
   - Expected: result.code equals `FAILED`
   - Expected: exporter.posts.len() equals `1`
   - Expected: exporter.getQueuedEventCount() equals `3`
   - Expected: exporter.scheduledDelays[0] equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Export three events with max batch size two and a failing first post")
val options = FirstPartyExporterOptions.new()
options.maxBatchSize = 2
val exporter = FirstPartyEventLoggingExporter.new(options)
exporter.postPlan = [FirstPartyPostResult.fail(503, "503 Service Unavailable")]
val result = exporter.export([
    FirstPartyReadableLogRecord.event("a", "1"),
    FirstPartyReadableLogRecord.event("b", "2"),
    FirstPartyReadableLogRecord.event("c", "3"),
])
expect(result.code).to_equal("FAILED")
expect(result.error).to_contain("3 events")
expect(exporter.posts.len()).to_equal(1)
expect(exporter.getQueuedEventCount()).to_equal(3)
expect(exporter.scheduledDelays[0]).to_equal(500)
```

</details>

#### should retry authenticated 401 without auth

- Plan a 401 followed by a successful unauthenticated POST
- exporter postPlan = [FirstPartyPostResult fail
   - Expected: result.code equals `SUCCESS`
   - Expected: exporter.posts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a 401 followed by a successful unauthenticated POST")
val exporter = firstPartyExporterDefault()
exporter.postPlan = [FirstPartyPostResult.fail(401, "401 Unauthorized"), FirstPartyPostResult.ok(200)]
val result = exporter.export([FirstPartyReadableLogRecord.event("auth", "4")])
expect(result.code).to_equal("SUCCESS")
expect(exporter.posts.len()).to_equal(2)
expect(exporter.posts[0]).to_contain("|auth")
expect(exporter.posts[1]).to_contain("|noauth")
```

</details>

#### should skip auth when trust is missing or oauth is expired

- Compare trust and subscriber skip-auth gates
   - Expected: trustExporter.shouldUseAuth() is false
   - Expected: oauthExporter.shouldUseAuth() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare trust and subscriber skip-auth gates")
val trustOptions = FirstPartyExporterOptions.new()
trustOptions.trusted = false
val trustExporter = FirstPartyEventLoggingExporter.new(trustOptions)
expect(trustExporter.shouldUseAuth()).to_equal(false)
val oauthOptions = FirstPartyExporterOptions.new()
oauthOptions.subscriber = true
oauthOptions.oauthExpired = true
val oauthExporter = FirstPartyEventLoggingExporter.new(oauthOptions)
expect(oauthExporter.shouldUseAuth()).to_equal(false)
```

</details>

#### should drain queued failures after a healthy export

- Seed failed queue and make the new export succeed
- exporter queued = [FirstPartyEventLoggingEvent new
   - Expected: result.code equals `SUCCESS`
   - Expected: exporter.getQueuedEventCount() equals `0`
   - Expected: exporter.attempts equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Seed failed queue and make the new export succeed")
val exporter = firstPartyExporterDefault()
exporter.queued = [FirstPartyEventLoggingEvent.new("ClaudeCodeInternalEvent", "old", "old-1", "old")]
val result = exporter.export([FirstPartyReadableLogRecord.event("new", "5")])
expect(result.code).to_equal("SUCCESS")
expect(exporter.getQueuedEventCount()).to_equal(0)
expect(exporter.attempts).to_equal(0)
```

</details>

#### should drop queued events after max attempts and cancel on shutdown

- Retry with max attempts already reached
- exporter queued = [FirstPartyEventLoggingEvent new
- exporter retryFailedEvents
   - Expected: exporter.getQueuedEventCount() equals `0`
- exporter shutdown
   - Expected: exporter.shutdownFlag is true
   - Expected: exporter.cancelBackoff is false
   - Expected: result.code equals `FAILED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retry with max attempts already reached")
val exporter = firstPartyExporterDefault()
exporter.queued = [FirstPartyEventLoggingEvent.new("ClaudeCodeInternalEvent", "old", "old-2", "old")]
exporter.attempts = 8
exporter.retryFailedEvents()
expect(exporter.getQueuedEventCount()).to_equal(0)
exporter.cancelBackoff = true
exporter.shutdown()
expect(exporter.shutdownFlag).to_equal(true)
expect(exporter.cancelBackoff).to_equal(false)
val result = exporter.export([FirstPartyReadableLogRecord.event("after", "6")])
expect(result.code).to_equal("FAILED")
```

</details>

#### should retry previous batch files and rewrite only failures

- Load two previous synthetic files
- [FirstPartyEventLoggingEvent new
- exporter postPlan = [FirstPartyPostResult fail
- exporter retryPreviousBatches
   - Expected: exporter.previousFiles[0].len() equals `1`
   - Expected: exporter.deletedFiles equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load two previous synthetic files")
val exporter = firstPartyExporterDefault()
exporter.previousFiles = [
    [FirstPartyEventLoggingEvent.new("ClaudeCodeInternalEvent", "a", "1", "a")],
    [],
]
exporter.postPlan = [FirstPartyPostResult.fail(503, "down")]
exporter.retryPreviousBatches()
expect(exporter.previousFiles[0].len()).to_equal(1)
expect(exporter.deletedFiles).to_equal(1)
```

</details>

#### should expose source-backed constants

- Pin modeled source surface
   - Expected: firstPartyExporterSourceLinesModeled() equals `720`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin modeled source surface")
expect(firstPartyExporterSourceLinesModeled()).to_equal(720)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [N/A - parity lane for upstream Claude CLI source surface.](N/A - parity lane for upstream Claude CLI source surface.)
- **Plan:** [N/A - targeted parity slice selected by strict checker output.](N/A - targeted parity slice selected by strict checker output.)
- **Design:** [N/A - implementation mirrors](N/A - implementation mirrors)
- **Research:** [N/A - local upstream TypeScript source is the controlling](N/A - local upstream TypeScript source is the controlling)


</details>
