# Browser Sandbox Posture: Honest Jailed/Unjailed Reporting

> I run the in-process Simple Browser, which today executes its engine and page

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Sandbox Posture: Honest Jailed/Unjailed Reporting

I run the in-process Simple Browser, which today executes its engine and page

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Security |
| Status | Active |
| Source | `test/01_unit/app/browser/browser_sandbox_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

I run the in-process Simple Browser, which today executes its engine and page
script in the host process with no OS jail. The jailed path exists only in the
hosted renderer worker behind `rt_browser_renderer_sandbox_enter`. Until this
app's rendering is routed through that worker, the sandbox knob
`SIMPLE_BROWSER_SANDBOX=1` must be handled honestly: a request that cannot be
honoured is refused, never silently served unjailed and never falsely
reported as jailed.

The audience is whoever lands the worker routing (they flip
`browser_sandbox_worker_routing_available` and this spec tells them what the
posture contract is) and whoever audits the browser's security claims.

## Scope

Covers `src/app/browser/sandbox_status.spl` only. The seccomp ALLOW-list
itself is proven natively by
`src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c`.
Tracking: doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md

## Scenarios

### browser sandbox posture is reported honestly

#### reports unjailed-in-process when no sandbox was requested

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports unjailed-in-process when no sandbox was requested
- read the posture with the knob unset in this test process
   - Expected: s.mode equals `BROWSER_SANDBOX_MODE_UNJAILED`
- the reason names the env knob so the posture is discoverable
- knob is set in this environment: posture must not claim jailed


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports unjailed-in-process when no sandbox was requested")
step("read the posture with the knob unset in this test process")
if env_get(BROWSER_SANDBOX_ENV) != "1":
    val s = browser_sandbox_status()
    assert_false(s.requested)
    assert_false(s.jailed)
    expect(s.mode).to_equal(BROWSER_SANDBOX_MODE_UNJAILED)
    step("the reason names the env knob so the posture is discoverable")
    expect(s.reason).to_contain(BROWSER_SANDBOX_ENV)
else:
    step("knob is set in this environment: posture must not claim jailed")
    assert_false(browser_sandbox_status().jailed)
```

</details>

#### never claims jailed while worker routing is unavailable

- never claims jailed while worker routing is unavailable
- check the routing flip-line is still off
- whatever was requested, jailed must be false
- a refused posture must carry a concrete reason
- routing landed: jailed may only be claimed with requested
   - Expected: s2.mode equals `BROWSER_SANDBOX_MODE_JAILED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never claims jailed while worker routing is unavailable")
step("check the routing flip-line is still off")
if not browser_sandbox_worker_routing_available():
    val s = browser_sandbox_status()
    step("whatever was requested, jailed must be false")
    assert_false(s.jailed)
    step("a refused posture must carry a concrete reason")
    if s.mode == BROWSER_SANDBOX_MODE_REFUSED:
        expect(s.reason).to_contain("renderer worker")
else:
    step("routing landed: jailed may only be claimed with requested")
    val s2 = browser_sandbox_status()
    if s2.jailed:
        assert_true(s2.requested)
        expect(s2.mode).to_equal(BROWSER_SANDBOX_MODE_JAILED)
```

</details>

#### renders a status line that carries the mode and the reason

- renders a status line that carries the mode and the reason
- format the current posture


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a status line that carries the mode and the reason")
step("format the current posture")
val s = browser_sandbox_status()
val line = browser_sandbox_status_line(s)
expect(line).to_start_with("browser sandbox: ")
expect(line).to_contain(s.mode)
```

</details>

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
- `REQ-BROWSER-SANDBOX-STATUS-001`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `24d74dda998bd8795362bf98003f4fe572ec84c8bef586c97be366d18e54b188`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24d74dda998bd8795362bf98003f4fe572ec84c8bef586c97be366d18e54b188`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24d74dda998bd8795362bf98003f4fe572ec84c8bef586c97be366d18e54b188`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/browser/browser_sandbox_status_spec.spl
mirror: doc/06_spec/01_unit/app/browser/browser_sandbox_status_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/browser/browser_sandbox_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/browser/browser_sandbox_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/browser/browser_sandbox_status_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/browser/browser_sandbox_status_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports unjailed-in-process when no sandbox was requested' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/browser/browser_sandbox_status_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never claims jailed while worker routing is unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/browser/browser_sandbox_status_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a status line that carries the mode and the reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
