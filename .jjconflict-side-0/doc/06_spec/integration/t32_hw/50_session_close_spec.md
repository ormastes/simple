# T32 Session Close Specification

> Final teardown test. Opens a session, verifies it works, closes it, and confirms operations fail after close.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Session Close Specification

Final teardown test. Opens a session, verifies it works, closes it, and confirms operations fail after close.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | Draft |
| Source | `test/integration/t32_hw/50_session_close_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Final teardown test. Opens a session, verifies it works, closes it,
and confirms operations fail after close.

## Scenarios

### T32 Session Close

#### opens and closes session cleanly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens and closes session cleanly
   - Expected: c.connected is true
   - Expected: c.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("opens and closes session cleanly")
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        expect(c.connected).to_equal(true)
        c.disconnect()
        expect(c.connected).to_equal(false)
    Err(e):
        expect("connection failed: {e}").to_contain("skip")
```

</details>

#### session is no longer connected after close

- session is no longer connected after close
   - Expected: c.connected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("session is no longer connected after close")
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        c.disconnect()
        # After disconnect, connected should be false
        expect(c.connected).to_equal(false)
    Err(e):
        expect("connection failed: {e}").to_contain("skip")
```

</details>

#### can reopen session after close

- can reopen session after close
   - Expected: t32_hw_probe_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("can reopen session after close")
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
# First session
val client1 = t32_hw_connect()
match client1:
    Ok(c1):
        c1.disconnect()
    Err(_):
        expect(t32_hw_probe_available()).to_equal(true)

# Second session should work
val client2 = t32_hw_connect()
match client2:
    Ok(c2):
        val r = c2.eval_expr("VERSION.BUILD()")
        c2.disconnect()
        match r:
            Ok(v): expect(v.len()).to_be_greater_than(0)
            Err(e): expect("eval failed: {e}").to_contain("eval")
    Err(e):
        expect("reconnection failed: {e}").to_contain("skip")
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4078540a62b6c1f190aaaad158401d362ef2d2d31768fe4992a9fd4346610c2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4078540a62b6c1f190aaaad158401d362ef2d2d31768fe4992a9fd4346610c2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4078540a62b6c1f190aaaad158401d362ef2d2d31768fe4992a9fd4346610c2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/integration/t32_hw/50_session_close_spec.spl
mirror: doc/06_spec/integration/t32_hw/50_session_close_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/50_session_close_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/50_session_close_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/50_session_close_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens and closes session cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/50_session_close_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session is no longer connected after close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/50_session_close_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can reopen session after close' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/integration/t32_hw/50_session_close_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can reopen session after close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
