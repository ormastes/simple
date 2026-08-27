# Async I/O Driver

> Tests the async I/O driver infrastructure including event loop setup, poll-based readiness notification, and task scheduling. Verifies that async operations are correctly multiplexed and that callbacks fire with the right results.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async I/O Driver

Tests the async I/O driver infrastructure including event loop setup, poll-based readiness notification, and task scheduling. Verifies that async operations are correctly multiplexed and that callbacks fire with the right results.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | In Progress |
| Source | `test/03_system/feature/io/async_driver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the async I/O driver infrastructure including event loop setup, poll-based
readiness notification, and task scheduling. Verifies that async operations are
correctly multiplexed and that callbacks fire with the right results.

## Scenarios

### IoDriver Lifecycle

#### skips driver tests in interpreter mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- skips driver tests in interpreter mode
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips driver tests in interpreter mode")
var compiled_block_ran = false
skip_on_interpreter "creates a driver with default queue depth":
    compiled_block_ran = true
    print "Would test IoDriver.new()"
skip_on_interpreter "creates a driver with custom queue depth":
    compiled_block_ran = true
    print "Would test IoDriver.with_depth(1024)"
skip_on_interpreter "close sets handle to -1":
    compiled_block_ran = true
    print "Would test driver.close()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Backend

#### skips backend tests in interpreter mode

- skips backend tests in interpreter mode
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips backend tests in interpreter mode")
var compiled_block_ran = false
skip_on_interpreter "reports a valid backend name":
    compiled_block_ran = true
    print "Would test driver.backend_name()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Timeout

#### skips timeout tests in interpreter mode

- skips timeout tests in interpreter mode
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips timeout tests in interpreter mode")
var compiled_block_ran = false
skip_on_interpreter "submits a timeout and gets completion":
    compiled_block_ran = true
    print "Would test driver.submit_timeout()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Cancel

#### skips cancel tests in interpreter mode

- skips cancel tests in interpreter mode
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips cancel tests in interpreter mode")
var compiled_block_ran = false
skip_on_interpreter "cancels a pending timeout":
    compiled_block_ran = true
    print "Would test driver.cancel()"
expect(compiled_block_ran).to_equal(false)
```

</details>

### IoDriver Flush

#### skips flush tests in interpreter mode

- skips flush tests in interpreter mode
   - Expected: compiled_block_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips flush tests in interpreter mode")
var compiled_block_ran = false
skip_on_interpreter "flush with no pending ops returns 0":
    compiled_block_ran = true
    print "Would test driver.flush()"
expect(compiled_block_ran).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `3724997d641419ae7f3a70715d086802acc82d8e2f442f1cc44639c5925512c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3724997d641419ae7f3a70715d086802acc82d8e2f442f1cc44639c5925512c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3724997d641419ae7f3a70715d086802acc82d8e2f442f1cc44639c5925512c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/io/async_driver_spec.spl
mirror: doc/06_spec/03_system/feature/io/async_driver_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/io/async_driver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/io/async_driver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/io/async_driver_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips driver tests in interpreter mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/io/async_driver_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips backend tests in interpreter mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/io/async_driver_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips timeout tests in interpreter mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
