# Claude Full Telemetry, Terminal, Highlighting, and Ultraplan

> Checks modern SSpec parity for the remaining utility control surfaces.

<!-- sdn-diagram:id=telemetry_terminal_ultraplan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=telemetry_terminal_ultraplan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

telemetry_terminal_ultraplan_spec -> std
telemetry_terminal_ultraplan_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=telemetry_terminal_ultraplan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Telemetry, Terminal, Highlighting, and Ultraplan

Checks modern SSpec parity for the remaining utility control surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/telemetry_terminal_ultraplan_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the remaining utility control surfaces.

## Scenarios

### Claude full telemetry terminal highlighting ultraplan

#### should bootstrap telemetry env and parse exporters

- var env = TelemetryBootstrapEnv new
- env = env bootstrapTelemetry
   - Expected: env.metricsExporter equals `otlp`
   - Expected: env.temporalityPreference equals `delta`
   - Expected: parseExporterTypes("console, none, otlp").len() equals `2`
   - Expected: telemetryTimeout(5, "slow").name equals `TelemetryTimeoutError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = TelemetryBootstrapEnv.new("ant")
env.antMetricsExporter = "otlp"
env = env.bootstrapTelemetry()
expect(env.metricsExporter).to_equal("otlp")
expect(env.temporalityPreference).to_equal("delta")
expect(parseExporterTypes("console, none, otlp").len()).to_equal(2)
expect(telemetryTimeout(5, "slow").name).to_equal("TelemetryTimeoutError")
```

</details>

#### should log OTEL diagnostic errors and warnings

- var logger = ClaudeCodeDiagLogger new
- logger = logger error
   - Expected: logger.errors[0] equals `boom`
   - Expected: logger.warnings[0] equals `careful`
   - Expected: logger.debugMessages.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var logger = ClaudeCodeDiagLogger.new()
logger = logger.error("boom").warn("careful").info("ignored")
expect(logger.errors[0]).to_equal("boom")
expect(logger.warnings[0]).to_equal("careful")
expect(logger.debugMessages.len()).to_equal(2)
```

</details>

#### should model terminal panel tmux and fallback paths

- var panel = TerminalPanel new
   - Expected: panel.socket() equals `claude-panel-12345678`
- panel = panel checkTmux
   - Expected: panel.sessionExists is true
   - Expected: panel.attached is true
   - Expected: panel.cleanupRegistered is true
   - Expected: TerminalPanel.new("abcdefghi", "/repo", "sh").checkTmux(1).toggle().fallbackLaunches equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var panel = TerminalPanel.new("123456789abcdef", "/repo", "/bin/bash")
expect(panel.socket()).to_equal("claude-panel-12345678")
panel = panel.checkTmux(0).toggle()
expect(panel.sessionExists).to_equal(true)
expect(panel.attached).to_equal(true)
expect(panel.cleanupRegistered).to_equal(true)
expect(TerminalPanel.new("abcdefghi", "/repo", "sh").checkTmux(1).toggle().fallbackLaunches).to_equal(1)
```

</details>

#### should segment text by non-overlapping highlights

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val segments = segmentTextByHighlights("abcdef", [TextHighlight.new(1, 3, "red", 1), TextHighlight.new(2, 5, "blue", 2)])
expect(segments.len()).to_equal(3)
expect(segments[1].text).to_equal("bc")
expect(segments[1].highlighted).to_equal(true)
expect(segmentTextByHighlights("plain", []).len()).to_equal(1)
```

</details>

#### should scan ultraplan CCR events

- var scanner = ExitPlanModeScanner new
- var result = scanner ingest
   - Expected: result.kind equals `pending`
- result = scanner ingest
   - Expected: result.kind equals `teleport`
   - Expected: result.plan equals `ship it`
   - Expected: UltraplanPollError.new("bad", "timeout_pending", 2).reason equals `timeout_pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(telemetryInstrumentationSourceLinesModeled()).to_equal(825)
expect(telemetryLoggerSourceLinesModeled()).to_equal(26)
expect(terminalPanelSourceLinesModeled()).to_equal(191)
expect(textHighlightingSourceLinesModeled()).to_equal(166)
expect(ultraplanCcrSessionSourceLinesModeled()).to_equal(349)
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
