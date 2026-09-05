# Claude Full Telemetry, Terminal, Highlighting, and Ultraplan

> Purpose: should bootstrap telemetry env and parse exporters

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Telemetry, Terminal, Highlighting, and Ultraplan

Purpose: should bootstrap telemetry env and parse exporters

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should bootstrap telemetry env and parse exporters
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Telemetry, Terminal, Highlighting, and Ultraplan

Checks modern SSpec parity for the remaining utility control surfaces.

## Scenarios

### Claude full telemetry terminal highlighting ultraplan

#### should bootstrap telemetry env and parse exporters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should bootstrap telemetry env and parse exporters
- Verify: should bootstrap telemetry env and parse exporters
   - Expected: env.metricsExporter equals `otlp`
   - Expected: env.temporalityPreference equals `delta`
   - Expected: parseExporterTypes("console, none, otlp").len() equals `2`
   - Expected: telemetryTimeout(5, "slow").name equals `TelemetryTimeoutError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bootstrap telemetry env and parse exporters")
step("Verify: should bootstrap telemetry env and parse exporters")
# @req: REQ-TOOLS-TeleTermUltr-001
var env = TelemetryBootstrapEnv.new("ant")
env.antMetricsExporter = "otlp"
env = env.bootstrapTelemetry()
expect(env.metricsExporter).to_equal("otlp")
expect(env.temporalityPreference).to_equal("delta")
expect(parseExporterTypes("console, none, otlp").len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(telemetryTimeout(5, "slow").name).to_equal("TelemetryTimeoutError")
```

</details>

#### should log OTEL diagnostic errors and warnings

- should log OTEL diagnostic errors and warnings
- Verify: should log OTEL diagnostic errors and warnings
   - Expected: logger.errors[0] equals `boom`
   - Expected: logger.warnings[0] equals `careful`
   - Expected: logger.debugMessages.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should log OTEL diagnostic errors and warnings")
step("Verify: should log OTEL diagnostic errors and warnings")
# @req: REQ-TOOLS-TeleTermUltr-001
var logger = ClaudeCodeDiagLogger.new()
logger = logger.error("boom").warn("careful").info("ignored")
expect(logger.errors[0]).to_equal("boom")
expect(logger.warnings[0]).to_equal("careful")
expect(logger.debugMessages.len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should model terminal panel tmux and fallback paths

- should model terminal panel tmux and fallback paths
- Verify: should model terminal panel tmux and fallback paths
   - Expected: panel.socket() equals `claude-panel-12345678`
   - Expected: panel.sessionExists is true
   - Expected: panel.attached is true
   - Expected: panel.cleanupRegistered is true
   - Expected: TerminalPanel.new("abcdefghi", "/repo", "sh").checkTmux(1).toggle().fallbackLaunches equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model terminal panel tmux and fallback paths")
step("Verify: should model terminal panel tmux and fallback paths")
# @req: REQ-TOOLS-TeleTermUltr-001
var panel = TerminalPanel.new("123456789abcdef", "/repo", "/bin/bash")
expect(panel.socket()).to_equal("claude-panel-12345678")
panel = panel.checkTmux(0).toggle()
expect(panel.sessionExists).to_equal(true)
expect(panel.attached).to_equal(true)
expect(panel.cleanupRegistered).to_equal(true)
expect(TerminalPanel.new("abcdefghi", "/repo", "sh").checkTmux(1).toggle().fallbackLaunches).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should segment text by non-overlapping highlights

- should segment text by non-overlapping highlights
- Verify: should segment text by non-overlapping highlights
   - Expected: segments.len() equals `3`
   - Expected: segments[1].text equals `bc`
   - Expected: segments[1].highlighted is true
   - Expected: segmentTextByHighlights("plain", []).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should segment text by non-overlapping highlights")
step("Verify: should segment text by non-overlapping highlights")
# @req: REQ-TOOLS-TeleTermUltr-001
val segments = segmentTextByHighlights("abcdef", [TextHighlight.new(1, 3, "red", 1), TextHighlight.new(2, 5, "blue", 2)])
expect(segments.len()).to_equal(3)  # oracle: value fixed by the spec contract
expect(segments[1].text).to_equal("bc")
expect(segments[1].highlighted).to_equal(true)
expect(segmentTextByHighlights("plain", []).len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should scan ultraplan CCR events

- should scan ultraplan CCR events
- Verify: should scan ultraplan CCR events
   - Expected: result.kind equals `pending`
   - Expected: result.kind equals `teleport`
   - Expected: result.plan equals `ship it`
   - Expected: UltraplanPollError.new("bad", "timeout_pending", 2).reason equals `timeout_pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should scan ultraplan CCR events")
step("Verify: should scan ultraplan CCR events")
# @req: REQ-TOOLS-TeleTermUltr-001
var scanner = ExitPlanModeScanner.new()
var result = scanner.ingest([CcrEvent.toolUse("call-1")])
expect(result.kind).to_equal("pending")
scanner = result.scanner
result = scanner.ingest([CcrEvent.toolResult("call-1", ULTRAPLAN_TELEPORT_SENTINEL + "\nship it", false)])
expect(result.kind).to_equal("teleport")
expect(result.plan).to_equal("ship it")
expect(UltraplanPollError.new("bad", "timeout_pending", 2).reason).to_equal("timeout_pending")
```

</details>

#### should expose source sizes

- should expose source sizes
- Verify: should expose source sizes
   - Expected: telemetryInstrumentationSourceLinesModeled() equals `825`
   - Expected: telemetryLoggerSourceLinesModeled() equals `26`
   - Expected: terminalPanelSourceLinesModeled() equals `191`
   - Expected: textHighlightingSourceLinesModeled() equals `166`
   - Expected: ultraplanCcrSessionSourceLinesModeled() equals `349`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source sizes")
step("Verify: should expose source sizes")
# @req: REQ-TOOLS-TeleTermUltr-001
expect(telemetryInstrumentationSourceLinesModeled()).to_equal(825)  # oracle: value fixed by the spec contract
expect(telemetryLoggerSourceLinesModeled()).to_equal(26)  # oracle: value fixed by the spec contract
expect(terminalPanelSourceLinesModeled()).to_equal(191)  # oracle: value fixed by the spec contract
expect(textHighlightingSourceLinesModeled()).to_equal(166)  # oracle: value fixed by the spec contract
expect(ultraplanCcrSessionSourceLinesModeled()).to_equal(349)  # oracle: value fixed by the spec contract
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

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-TeleTermUltr-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a088e03e07783ba8828bc63638749fbe98c64543da86ceeeef353d53f3e802ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a088e03e07783ba8828bc63638749fbe98c64543da86ceeeef353d53f3e802ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a088e03e07783ba8828bc63638749fbe98c64543da86ceeeef353d53f3e802ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bootstrap telemetry env and parse exporters' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bootstrap telemetry env and parse exporters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should log OTEL diagnostic errors and warnings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should log OTEL diagnostic errors and warnings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model terminal panel tmux and fallback paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model terminal panel tmux and fallback paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should segment text by non-overlapping highlights' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should scan ultraplan CCR events' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose source sizes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
