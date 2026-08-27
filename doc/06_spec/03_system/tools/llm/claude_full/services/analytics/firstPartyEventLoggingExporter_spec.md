# Claude Full First Party Event Logging Exporter

> Purpose: should build default endpoint and transform only event scope logs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full First Party Event Logging Exporter

Purpose: should build default endpoint and transform only event scope logs

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should build default endpoint and transform only event scope logs
Audience: compiler and tooling engineers who maintain this spec

# Claude Full First Party Event Logging Exporter

## Overview

This SSpec pins the Claude CLI `FirstPartyEventLoggingExporter` parity slice in
Simple. It checks that the exporter keeps the same public telemetry contract:
only OpenTelemetry event-scope logs are transformed, GrowthBook experiment logs
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should build default endpoint and transform only event scope logs
- Verify: should build default endpoint and transform only event scope logs
- Create mixed scope logs
   - Expected: exporter.endpoint equals `https://api.anthropic.com/api/event_logging/batch`
   - Expected: events.len() equals `2`
   - Expected: events[0].eventType equals `ClaudeCodeInternalEvent`
   - Expected: events[1].eventType equals `GrowthbookExperimentEvent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build default endpoint and transform only event scope logs")
step("Verify: should build default endpoint and transform only event scope logs")
# @req: REQ-TOOLS-Firs-001
step("Create mixed scope logs")
val exporter = firstPartyExporterDefault()
val logs = [
    FirstPartyReadableLogRecord.event("tool_call", "evt-1"),
    FirstPartyReadableLogRecord.otherScope("ignored"),
    FirstPartyReadableLogRecord.growthbook("gb-1", "experiment-a"),
]
val events = exporter.transformLogsToEvents(logs)
expect(exporter.endpoint).to_equal("https://api.anthropic.com/api/event_logging/batch")
expect(events.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(events[0].eventType).to_equal("ClaudeCodeInternalEvent")
expect(events[1].eventType).to_equal("GrowthbookExperimentEvent")
```

</details>

#### should emit transform error when core metadata is missing

- should emit transform error when core metadata is missing
- Verify: should emit transform error when core metadata is missing
- Transform a log without core metadata
   - Expected: events[0].eventName equals `body-name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit transform error when core metadata is missing")
step("Verify: should emit transform error when core metadata is missing")
# @req: REQ-TOOLS-Firs-001
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

- should strip proto metadata from additional metadata
- Verify: should strip proto metadata from additional metadata
- Transform a log with hoisted proto keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should strip proto metadata from additional metadata")
step("Verify: should strip proto metadata from additional metadata")
# @req: REQ-TOOLS-Firs-001
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

- should chunk posts and short circuit remaining batches after failure
- Verify: should chunk posts and short circuit remaining batches after failure
- Export three events with max batch size two and a failing first post
   - Expected: result.code equals `FAILED`
   - Expected: exporter.posts.len() equals `1`
   - Expected: exporter.getQueuedEventCount() equals `3`
   - Expected: exporter.scheduledDelays[0] equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should chunk posts and short circuit remaining batches after failure")
step("Verify: should chunk posts and short circuit remaining batches after failure")
# @req: REQ-TOOLS-Firs-001
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
expect(exporter.posts.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(exporter.getQueuedEventCount()).to_equal(3)  # oracle: value fixed by the spec contract
expect(exporter.scheduledDelays[0]).to_equal(500)  # oracle: value fixed by the spec contract
```

</details>

#### should retry authenticated 401 without auth

- should retry authenticated 401 without auth
- Verify: should retry authenticated 401 without auth
- Plan a 401 followed by a successful unauthenticated POST
   - Expected: result.code equals `SUCCESS`
   - Expected: exporter.posts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retry authenticated 401 without auth")
step("Verify: should retry authenticated 401 without auth")
# @req: REQ-TOOLS-Firs-001
step("Plan a 401 followed by a successful unauthenticated POST")
val exporter = firstPartyExporterDefault()
exporter.postPlan = [FirstPartyPostResult.fail(401, "401 Unauthorized"), FirstPartyPostResult.ok(200)]
val result = exporter.export([FirstPartyReadableLogRecord.event("auth", "4")])
expect(result.code).to_equal("SUCCESS")
expect(exporter.posts.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(exporter.posts[0]).to_contain("|auth")
expect(exporter.posts[1]).to_contain("|noauth")
```

</details>

#### should skip auth when trust is missing or oauth is expired

- should skip auth when trust is missing or oauth is expired
- Verify: should skip auth when trust is missing or oauth is expired
- Compare trust and subscriber skip-auth gates
   - Expected: trustExporter.shouldUseAuth() is false
   - Expected: oauthExporter.shouldUseAuth() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should skip auth when trust is missing or oauth is expired")
step("Verify: should skip auth when trust is missing or oauth is expired")
# @req: REQ-TOOLS-Firs-001
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

- should drain queued failures after a healthy export
- Verify: should drain queued failures after a healthy export
- Seed failed queue and make the new export succeed
   - Expected: result.code equals `SUCCESS`
   - Expected: exporter.getQueuedEventCount() equals `0`
   - Expected: exporter.attempts equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should drain queued failures after a healthy export")
step("Verify: should drain queued failures after a healthy export")
# @req: REQ-TOOLS-Firs-001
step("Seed failed queue and make the new export succeed")
val exporter = firstPartyExporterDefault()
exporter.queued = [FirstPartyEventLoggingEvent.new("ClaudeCodeInternalEvent", "old", "old-1", "old")]
val result = exporter.export([FirstPartyReadableLogRecord.event("new", "5")])
expect(result.code).to_equal("SUCCESS")
expect(exporter.getQueuedEventCount()).to_equal(0)  # oracle: value fixed by the spec contract
expect(exporter.attempts).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should drop queued events after max attempts and cancel on shutdown

- should drop queued events after max attempts and cancel on shutdown
- Verify: should drop queued events after max attempts and cancel on shutdown
- Retry with max attempts already reached
   - Expected: exporter.getQueuedEventCount() equals `0`
   - Expected: exporter.shutdownFlag is true
   - Expected: exporter.cancelBackoff is false
   - Expected: result.code equals `FAILED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should drop queued events after max attempts and cancel on shutdown")
step("Verify: should drop queued events after max attempts and cancel on shutdown")
# @req: REQ-TOOLS-Firs-001
step("Retry with max attempts already reached")
val exporter = firstPartyExporterDefault()
exporter.queued = [FirstPartyEventLoggingEvent.new("ClaudeCodeInternalEvent", "old", "old-2", "old")]
exporter.attempts = 8
exporter.retryFailedEvents()
expect(exporter.getQueuedEventCount()).to_equal(0)  # oracle: value fixed by the spec contract
exporter.cancelBackoff = true
exporter.shutdown()
expect(exporter.shutdownFlag).to_equal(true)
expect(exporter.cancelBackoff).to_equal(false)
val result = exporter.export([FirstPartyReadableLogRecord.event("after", "6")])
expect(result.code).to_equal("FAILED")
```

</details>

#### should retry previous batch files and rewrite only failures

- should retry previous batch files and rewrite only failures
- Verify: should retry previous batch files and rewrite only failures
- Load two previous synthetic files
   - Expected: exporter.previousFiles[0].len() equals `1`
   - Expected: exporter.deletedFiles equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retry previous batch files and rewrite only failures")
step("Verify: should retry previous batch files and rewrite only failures")
# @req: REQ-TOOLS-Firs-001
step("Load two previous synthetic files")
val exporter = firstPartyExporterDefault()
exporter.previousFiles = [
    [FirstPartyEventLoggingEvent.new("ClaudeCodeInternalEvent", "a", "1", "a")],
    [],
]
exporter.postPlan = [FirstPartyPostResult.fail(503, "down")]
exporter.retryPreviousBatches()
expect(exporter.previousFiles[0].len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(exporter.deletedFiles).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should expose source-backed constants

- should expose source-backed constants
- Verify: should expose source-backed constants
- Pin modeled source surface
   - Expected: firstPartyExporterSourceLinesModeled() equals `720`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed constants")
step("Verify: should expose source-backed constants")
# @req: REQ-TOOLS-Firs-001
step("Pin modeled source surface")
expect(firstPartyExporterSourceLinesModeled()).to_equal(720)  # oracle: value fixed by the spec contract
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

- **Requirements:** `N/A - parity lane for upstream Claude CLI source surface.`
- **Plan:** `N/A - targeted parity slice selected by strict checker output.`
- **Design:** `N/A - implementation mirrors`
- **Research:** `N/A - local upstream TypeScript source is the controlling`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Firs-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ecf82667acbefdc0d751f61a5ece6953fd6b847fc8d0712b6facabe764115710`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecf82667acbefdc0d751f61a5ece6953fd6b847fc8d0712b6facabe764115710`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecf82667acbefdc0d751f61a5ece6953fd6b847fc8d0712b6facabe764115710`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build default endpoint and transform only event scope logs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build default endpoint and transform only event scope logs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit transform error when core metadata is missing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit transform error when core metadata is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should strip proto metadata from additional metadata' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should strip proto metadata from additional metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should chunk posts and short circuit remaining batches after failure' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:131:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retry authenticated 401 without auth' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/analytics/firstPartyEventLoggingExporter_spec.spl:145:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should skip auth when trust is missing or oauth is expired' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
