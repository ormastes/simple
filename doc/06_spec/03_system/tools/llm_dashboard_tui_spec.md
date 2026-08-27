# Llm Dashboard Tui Specification

> Tests covering LLM Dashboard TUI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Dashboard Tui Specification

## Scenarios

### LLM Dashboard TUI

#### plain (non-tty) mode prints a real collector summary and exits cleanly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plain (non-tty) mode prints a real collector summary and exits cleanly
   - Expected: code equals `0`
   - Expected: out contains `LLM Agent Dashboard`
   - Expected: out contains `mode=tui`
   - Expected: out contains `Agents:`
   - Expected: out contains `Files:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plain (non-tty) mode prints a real collector summary and exits cleanly")
# TERM=dumb forces the non-interactive path (see _is_interactive_tty in
# src/app/llm_dashboard/main.spl) so this asserts on the real
# AgentDashboardStore.summary_line() output, not a canned string.
val (out, _, code) = rt_process_run("/bin/bash", ["-c",
    "TERM=dumb bin/simple run src/app/llm_dashboard/main.spl --tui 2>/dev/null"])
expect(code).to_equal(0)
expect(out.contains("LLM Agent Dashboard")).to_equal(true)
expect(out.contains("mode=tui")).to_equal(true)
expect(out.contains("Agents:")).to_equal(true)
expect(out.contains("Files:")).to_equal(true)
```

</details>

#### reports web status without launching a host

- reports web status without launching a host
   - Expected: code equals `0`
   - Expected: out contains `command=llm-dashboard`
   - Expected: out contains `mode=web`
   - Expected: out contains `host_status=not-started`
   - Expected: out contains `status=ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports web status without launching a host")
val (out, _, code) = rt_process_run("/bin/bash", ["-c",
    "bin/simple run src/app/llm_dashboard/main.spl --web --status 2>/dev/null"])
expect(code).to_equal(0)
expect(out.contains("command=llm-dashboard")).to_equal(true)
expect(out.contains("mode=web")).to_equal(true)
expect(out.contains("host_status=not-started")).to_equal(true)
expect(out.contains("status=ready")).to_equal(true)
```

</details>

#### reports selected mode in json log output

- reports selected mode in json log output
   - Expected: code equals `0`
   - Expected: out contains `"command":"llm-dashboard"`
   - Expected: out contains `"status":"ready"`
   - Expected: out contains `"mode":"ios"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports selected mode in json log output")
val (out, _, code) = rt_process_run("/bin/bash", ["-c",
    "bin/simple run src/app/llm_dashboard/main.spl --ios --json 2>/dev/null"])
expect(code).to_equal(0)
expect(out.contains("\"command\":\"llm-dashboard\"")).to_equal(true)
expect(out.contains("\"status\":\"ready\"")).to_equal(true)
expect(out.contains("\"mode\":\"ios\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm_dashboard_tui_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Dashboard TUI.
- LLM Dashboard TUI

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

- Canonical SPipe generation for source `9797e4478880edbdfe3957682d8ec9a557d3f5b2d95ad1c071b1e1c49fe080c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9797e4478880edbdfe3957682d8ec9a557d3f5b2d95ad1c071b1e1c49fe080c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9797e4478880edbdfe3957682d8ec9a557d3f5b2d95ad1c071b1e1c49fe080c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm_dashboard_tui_spec.spl
mirror: doc/06_spec/03_system/tools/llm_dashboard_tui_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm_dashboard_tui_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm_dashboard_tui_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm_dashboard_tui_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm_dashboard_tui_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plain (non-tty) mode prints a real collector summary and exits cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm_dashboard_tui_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports web status without launching a host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm_dashboard_tui_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports selected mode in json log output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
