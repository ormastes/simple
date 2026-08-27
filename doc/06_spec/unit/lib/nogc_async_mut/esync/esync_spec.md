# Esync Specification

> Tests covering esync NT event/semaphore.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Esync Specification

## Scenarios

### esync NT event/semaphore

#### create returns a positive handle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create returns a positive handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create returns a positive handle")
val h = esync_create()
expect(h).to_be_greater_than(0)
```

</details>

#### two creates return distinct handles

- two creates return distinct handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two creates return distinct handles")
val h1 = esync_create()
val h2 = esync_create()
expect(h1).to_not_equal(h2)
```

</details>

#### wait on unsignaled handle with timeout=0 returns timeout

- wait on unsignaled handle with timeout=0 returns timeout
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wait on unsignaled handle with timeout=0 returns timeout")
val h = esync_create()
val result = esync_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### signal then wait returns signaled

- signal then wait returns signaled
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signal then wait returns signaled")
val h = esync_create()
esync_signal(h)
val result = esync_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### wait consumes signal (auto-reset)

- wait consumes signal (auto-reset)
   - Expected: result2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wait consumes signal (auto-reset)")
val h = esync_create()
esync_signal(h)
esync_wait(h, 0)
val result2 = esync_wait(h, 0)
expect(result2).to_equal("timeout")
```

</details>

#### reset clears a signaled handle

- reset clears a signaled handle
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset clears a signaled handle")
val h = esync_create()
esync_signal(h)
esync_reset(h)
val result = esync_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### wait on invalid handle returns invalid

- wait on invalid handle returns invalid
   - Expected: result equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wait on invalid handle returns invalid")
val result = esync_wait(-1, 0)
expect(result).to_equal("invalid")
```

</details>

#### signal on invalid handle does not panic

- signal on invalid handle does not panic
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signal on invalid handle does not panic")
esync_signal(-99)
expect(1).to_equal(1)
```

</details>

#### close removes handle from active set

- close removes handle from active set
   - Expected: result equals `invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close removes handle from active set")
val h = esync_create()
esync_close(h)
val result = esync_wait(h, 0)
expect(result).to_equal("invalid")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/esync/esync_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering esync NT event/semaphore.
- esync NT event/semaphore

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `98aee68f88c070935515be79ef004ba99f5a5d0055a694a37caa6b38c8507c70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98aee68f88c070935515be79ef004ba99f5a5d0055a694a37caa6b38c8507c70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98aee68f88c070935515be79ef004ba99f5a5d0055a694a37caa6b38c8507c70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/nogc_async_mut/esync/esync_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/esync/esync_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/esync/esync_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/esync/esync_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/esync/esync_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/esync/esync_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create returns a positive handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/esync/esync_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two creates return distinct handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/esync/esync_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wait on unsignaled handle with timeout=0 returns timeout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
