# Watchdog Manager Specification

> Tests covering backend-isolation Gap D: WatchdogManager facade owns rt_watchdog_* externs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Watchdog Manager Specification

## Scenarios

### backend-isolation Gap D: WatchdogManager facade owns rt_watchdog_* externs

#### adds the WatchdogManager facade module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adds the WatchdogManager facade module
   - Expected: file_exists("src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl") is true
   - Expected: source contains `extern fn rt_watchdog_start`
   - Expected: source contains `extern fn rt_watchdog_stop`
   - Expected: source contains `class WatchdogManager`
   - Expected: source contains `fn start(timeout_secs: i64)`
   - Expected: source contains `fn stop()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adds the WatchdogManager facade module")
expect(file_exists("src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl")).to_equal(true)
val source = read_file("src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl")
expect(source.contains("extern fn rt_watchdog_start")).to_equal(true)
expect(source.contains("extern fn rt_watchdog_stop")).to_equal(true)
expect(source.contains("class WatchdogManager")).to_equal(true)
expect(source.contains("fn start(timeout_secs: i64)")).to_equal(true)
expect(source.contains("fn stop()")).to_equal(true)
```

</details>

#### leaves no app-layer copy of the watchdog module to re-declare the externs

- leaves no app-layer copy of the watchdog module to re-declare the externs
   - Expected: file_exists("src/app/interpreter/core/watchdog.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves no app-layer copy of the watchdog module to re-declare the externs")
expect(file_exists("src/app/interpreter/core/watchdog.spl")).to_equal(false)
```

</details>

#### keeps the facade as the sole declarer of the rt_watchdog_* externs

- keeps the facade as the sole declarer of the rt_watchdog_* externs
   - Expected: facade contains `extern fn rt_watchdog_start`
   - Expected: facade contains `extern fn rt_watchdog_stop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the facade as the sole declarer of the rt_watchdog_* externs")
# (Checked by inspection 2026-08-17: `check-ui-backend-isolation.shs`
# does not mention `rt_watchdog` by name -- it bans app-layer externs by
# path class, not by symbol -- so this block pins the facade itself
# rather than asserting gate text that does not exist.)
val facade = read_file("src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl")
expect(facade.contains("extern fn rt_watchdog_start")).to_equal(true)
expect(facade.contains("extern fn rt_watchdog_stop")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering backend-isolation Gap D: WatchdogManager facade owns rt_watchdog_* externs.
- backend-isolation Gap D: WatchdogManager facade owns rt_watchdog_* externs

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ae6f3e42c130f2f3f2157fdf7d2a2198c853171bb0b120390ec5a214d63a1831`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae6f3e42c130f2f3f2157fdf7d2a2198c853171bb0b120390ec5a214d63a1831`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae6f3e42c130f2f3f2157fdf7d2a2198c853171bb0b120390ec5a214d63a1831`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds the WatchdogManager facade module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves no app-layer copy of the watchdog module to re-declare the externs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the facade as the sole declarer of the rt_watchdog_* externs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
