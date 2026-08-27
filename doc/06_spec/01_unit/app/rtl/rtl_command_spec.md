# Rtl Command Specification

> Tests covering RTL command parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rtl Command Specification

## Scenarios

### RTL command parser

#### parses bench suite and target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses bench suite and target


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bench suite and target")
val command = parse_rtl_command(["rtl", "bench", "--suite=smoke", "--target=ice40"])
check(command.is_bench())
expect command.suite == "smoke"
expect command.target == "ice40"
```

</details>

#### parses compare baselines

- parses compare baselines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses compare baselines")
val command = parse_rtl_command(["rtl", "compare", "--baseline=old", "--candidate=new"])
check(command.is_compare())
expect command.baseline == "old"
expect command.candidate == "new"
```

</details>

#### parses qor report command

- parses qor report command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses qor report command")
val command = parse_rtl_command(["rtl", "qor", "report", "--design=rv32i_core"])
check(command.is_report())
expect command.design == "rv32i_core"
```

</details>

#### parses rtl explain command

- parses rtl explain command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses rtl explain command")
val command = parse_rtl_command(["rtl", "explain", "--map=core.vhd.map.json", "--vhdl-line=8"])
check(command.is_explain())
expect command.map_path == "core.vhd.map.json"
expect command.vhdl_line == 8
```

</details>

#### renders a bench preview report

- renders a bench preview report


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a bench preview report")
val command = parse_rtl_command(["rtl", "bench", "--suite=smoke", "--target=generic"])
val markdown = render_rtl_bench_preview(command)
check(markdown.contains("RTL QoR Run"))
check(markdown.contains("ghdl-yosys"))
```

</details>

#### renders an explain preview from source map JSON

- renders an explain preview from source map JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an explain preview from source map JSON")
val command = parse_rtl_command(["rtl", "explain", "--vhdl-line=8"])
val map_json = "{\"ports\":[{\"name\":\"a\",\"originalName\":\"a\",\"sanitizedName\":\"a\",\"line\":8,\"hwirId\":\"port:a:8\",\"sourceLine\":2}]}"
val text = render_rtl_explain_preview(command, map_json)
check(text.contains("port:a:8"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/rtl/rtl_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RTL command parser.
- RTL command parser

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `21e782f891e814752d179796a14549448ee593e2d47f9734056ccf193fa3149b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21e782f891e814752d179796a14549448ee593e2d47f9734056ccf193fa3149b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21e782f891e814752d179796a14549448ee593e2d47f9734056ccf193fa3149b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/rtl/rtl_command_spec.spl
mirror: doc/06_spec/01_unit/app/rtl/rtl_command_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/rtl/rtl_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/rtl/rtl_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/rtl/rtl_command_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bench suite and target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/rtl/rtl_command_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses compare baselines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/rtl/rtl_command_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses qor report command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
