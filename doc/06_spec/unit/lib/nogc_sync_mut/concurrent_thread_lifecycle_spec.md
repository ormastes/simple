# Thread-handle cleanup unit manual: scope and evidence

## Purpose and audience

Library/runtime maintainers use these scenarios to verify observable terminal
handle behavior: first join returns its payload, repeated join returns nil,
and repeated free remains safe. The second scenario preserves the existing
free-before-join behavior asserted by this runtime lineage.

## Assumptions and workflow

Spawn the first closure returning 29; join once and retain that value. Verify
the handle is done, join again and assert nil as the optional consumed-handle
contract requires. Free twice and verify terminal status. The independent
second scenario uses payload 41 and preserves its existing assertions.

## Traceability and recovery

Source: `test/unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl`.
Owner: `src/lib/nogc_sync_mut/concurrent/thread.spl`, whose `join() -> i64?`
returns nil when `joined` is already true. The canonical `test/01_unit` copy
already asserts nil; it was neither changed nor replayed. Existing
`REQ-SSPEC-UNIT` metadata does not create a new feature requirement.
If cleanup fails, retain the first payload, joined flag, returned optional
value and runtime identity before diagnosing provider behavior. Do not change
the oracle to an unverified backend value.

## Evidence and limitations

Current source SHA256:
`55c74d7c191d17f08f4972882d0ea94baf69b4c7ab70eeccacc1fe335fdec33d`.
Original row 23358 passed 1/2 and recorded `expected Option::None to equal 0`.
The changed legacy file passed 2/2, zero failures/skips, under pinned Phase1
seed `0f9bfc1` and frozen dependency source `e59027c`; kernel exit 0/quiescent 1.
The existing bug's dated follow-up records exact receipts. This is diagnostic
seed evidence for fixture/API synchronization, not native threading or whole
bootstrap qualification. No concurrency scheduling guarantee is inferred from
an interpreter run. The generated executable body is retained below.

# Concurrent Thread Lifecycle Specification

> Tests covering nogc sync thread lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Thread Lifecycle Specification

## Scenarios

### nogc sync thread lifecycle

#### treats repeated terminal cleanup as safe no-ops

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats repeated terminal cleanup as safe no-ops
- Spawn and join a public OS thread
   - Expected: handle.join() equals `29`
- Verify the consumed handle stays terminal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats repeated terminal cleanup as safe no-ops")
step("Spawn and join a public OS thread")
val handle = thread_spawn(\: 29)
expect(handle.join()).to_equal(29)

step("Verify the consumed handle stays terminal")
expect(handle.is_done()).to_be(true)
# The optional join result is nil after the handle was consumed.
expect(handle.join()).to_be_nil()
handle.free()
handle.free()
expect(handle.is_done()).to_be(true)
```

</details>

#### treats free-before-join terminal cleanup as a safe no-op

- treats free-before-join terminal cleanup as a safe no-op
- Spawn and free a public OS thread handle before join
- Verify the freed handle stays terminal
   - Expected: handle.join() equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats free-before-join terminal cleanup as a safe no-op")
step("Spawn and free a public OS thread handle before join")
val handle = thread_spawn(\: 41)
handle.free()

step("Verify the freed handle stays terminal")
expect(handle.is_done()).to_be(true)
expect(handle.join()).to_equal(41)
handle.free()
handle.free()
expect(handle.is_done()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_sync_mut/concurrent_thread_lifecycle_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc sync thread lifecycle.
- nogc sync thread lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
