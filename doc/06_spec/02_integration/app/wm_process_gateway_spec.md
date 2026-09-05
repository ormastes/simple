# Wm Process Gateway Specification

> Tests covering host process gateway (simple process backing), wm daemon (headless compositor over daemon_sdk routing).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Process Gateway Specification

## Scenarios

### host process gateway (simple process backing)

#### spawns a real child, registers, kills, deregisters, and waits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- spawns a real child, registers, kills, deregisters, and waits
   - Expected: pid > 0 is true
   - Expected: _registry_has_pid(pid) is true
   - Expected: process_is_running(pid) is true
   - Expected: process_kill(pid) is true
   - Expected: _registry_has_pid(pid) is false
   - Expected: timed_out is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("spawns a real child, registers, kills, deregisters, and waits")
val pid = process_spawn_async("sleep", ["5"])
expect(pid > 0).to_equal(true)

registry_add(pid, "sleep 5")
expect(_registry_has_pid(pid)).to_equal(true)
expect(process_is_running(pid)).to_equal(true)

expect(process_kill(pid)).to_equal(true)
registry_remove(pid)
expect(_registry_has_pid(pid)).to_equal(false)

# After kill the wait must return promptly (any code, but not timeout -2).
val code = process_wait(pid, 2000)
val timed_out = code == -2
expect(timed_out).to_equal(false)
```

</details>

### wm daemon (headless compositor over daemon_sdk routing)

#### starts, lists empty, opens a window, lists it, and stops

- starts, lists empty, opens a window, lists it, and stops
   - Expected: s.empty_count equals `0`
   - Expected: s.opened_count equals `1`
   - Expected: s.opened_id equals `1`
   - Expected: s.listed_count equals `1`
   - Expected: s.listed_title equals `Terminal`
   - Expected: s.stop_requested is true
   - Expected: s.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("starts, lists empty, opens a window, lists it, and stops")
val s = wm_daemon_inprocess_scenario()
expect(s.empty_count).to_equal(0)
expect(s.opened_count).to_equal(1)
expect(s.opened_id).to_equal("1")
expect(s.listed_count).to_equal(1)
expect(s.listed_title).to_equal("Terminal")
expect(s.stop_requested).to_equal(true)
expect(s.ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/wm_process_gateway_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host process gateway (simple process backing), wm daemon (headless compositor over daemon_sdk routing).
- host process gateway (simple process backing)
- wm daemon (headless compositor over daemon_sdk routing)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0fefad1eabef85668056c654b6d2414389b2a48975b3390d6dd8fe3d71931ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0fefad1eabef85668056c654b6d2414389b2a48975b3390d6dd8fe3d71931ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0fefad1eabef85668056c654b6d2414389b2a48975b3390d6dd8fe3d71931ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/wm_process_gateway_spec.spl
mirror: doc/06_spec/02_integration/app/wm_process_gateway_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/wm_process_gateway_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/wm_process_gateway_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/wm_process_gateway_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/wm_process_gateway_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spawns a real child, registers, kills, deregisters, and waits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/wm_process_gateway_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts, lists empty, opens a window, lists it, and stops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
