# Executable Load Consumer Specification

> Tests covering bounded executable load planning, pure executable load lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Executable Load Consumer Specification

## Scenarios

### bounded executable load planning

#### accepts an exact x86_64 SimpleOS plan and counts mapped pages

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts an exact x86_64 SimpleOS plan and counts mapped pages
   - Expected: checked.segment_count equals `2`
   - Expected: checked.page_count equals `3u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts an exact x86_64 SimpleOS plan and counts mapped pages")
val consumer = executable_load_consumer_new_v1(
    "simpleos", "x86_64", "simpleos")
val checked = executable_load_consumer_validate_plan_v1(
    consumer, load_handle("x86_64", "simpleos", [exec_range(), data_range()]),
    0x400100u64)
if not checked.ok:
    fail("valid load plan rejected")
expect(checked.segment_count).to_equal(2)
expect(checked.page_count).to_equal(3u64)
```

</details>

#### rejects unsupported architecture ABI mismatch and non-executable entry

- rejects unsupported architecture ABI mismatch and non-executable entry
   - Expected: wrong_abi.error equals `ExecutableLoadConsumerErrorV1.UnsupportedAbi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unsupported architecture ABI mismatch and non-executable entry")
val unsupported = executable_load_consumer_validate_plan_v1(
    executable_load_consumer_new_v1("simpleos", "mips64", "simpleos"),
    load_handle("mips64", "simpleos", [exec_range()]), 0x400100u64)
expect(unsupported.error).to_equal(
    ExecutableLoadConsumerErrorV1.UnsupportedArchitecture)

val wrong_abi = executable_load_consumer_validate_plan_v1(
    executable_load_consumer_new_v1("simpleos", "x86_64", "linux-gnu"),
    load_handle("x86_64", "linux-gnu", [exec_range()]), 0x400100u64)
expect(wrong_abi.error).to_equal(ExecutableLoadConsumerErrorV1.UnsupportedAbi)

val wrong_entry = executable_load_consumer_validate_plan_v1(
    executable_load_consumer_new_v1("simpleos", "x86_64", "simpleos"),
    load_handle("x86_64", "simpleos", [exec_range()]), 0x500000u64)
expect(wrong_entry.error).to_equal(
    ExecutableLoadConsumerErrorV1.InvalidEntryPoint)
```

</details>

#### rejects W-X page alias overflow and per-segment page excess

- rejects W-X page alias overflow and per-segment page excess


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects W-X page alias overflow and per-segment page excess")
val consumer = executable_load_consumer_new_v1(
    "simpleos", "x86_64", "simpleos")
val wx = ExecutableLoadRangeV1(
    file_offset: 0u64, file_size: 1u64,
    virtual_address: 0x400000u64, memory_size: 4096u64,
    writable: true, executable: true)
expect(executable_load_consumer_validate_plan_v1(
    consumer, load_handle("x86_64", "simpleos", [wx]), 0x400000u64
).error).to_equal(ExecutableLoadConsumerErrorV1.WriteExecuteDenied)

val alias_a = ExecutableLoadRangeV1(
    file_offset: 0u64, file_size: 2048u64,
    virtual_address: 0x400000u64, memory_size: 2048u64,
    writable: false, executable: true)
val alias_b = ExecutableLoadRangeV1(
    file_offset: 2048u64, file_size: 2048u64,
    virtual_address: 0x400800u64, memory_size: 2048u64,
    writable: false, executable: false)
expect(executable_load_consumer_validate_plan_v1(
    consumer,
    load_handle("x86_64", "simpleos", [alias_a, alias_b]), 0x400000u64
).error).to_equal(ExecutableLoadConsumerErrorV1.PageOverlap)

val overflow = ExecutableLoadRangeV1(
    file_offset: 3995u64, file_size: 1u64,
    virtual_address: 18446744073709551515u64, memory_size: 200u64,
    writable: false, executable: true)
expect(executable_load_consumer_validate_plan_v1(
    consumer, load_handle("x86_64", "simpleos", [overflow]),
    18446744073709551515u64
).error).to_equal(ExecutableLoadConsumerErrorV1.AddressOverflow)

val too_many_pages = ExecutableLoadRangeV1(
    file_offset: 0u64, file_size: 1u64,
    virtual_address: 0x400000u64,
    memory_size: (executable_load_consumer_max_segment_pages_v1() + 1u64) * 4096u64,
    writable: false, executable: true)
expect(executable_load_consumer_validate_plan_v1(
    consumer, load_handle("x86_64", "simpleos", [too_many_pages]),
    0x400000u64
).error).to_equal(ExecutableLoadConsumerErrorV1.PageLimitExceeded)
```

</details>

### pure executable load lifecycle

#### rejects a forged ready value with pre-existing lifecycle counters

- rejects a forged ready value with pre-existing lifecycle counters


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a forged ready value with pre-existing lifecycle counters")
var forged_ready = forged_lifecycle(
    ExecutableLoadConsumerStateV1.Ready, 1u64, 0u64, 0u64, 0u64)
forged_ready.segment_count = 0
forged_ready.entry_point = 0u64
val checked = executable_load_consumer_validate_plan_v1(
    forged_ready,
    load_handle("x86_64", "simpleos", [exec_range()]),
    0x400100u64)
expect(checked.error).to_equal(
    ExecutableLoadConsumerErrorV1.InvalidConsumer)
```

</details>

#### quarantines forged unmap counters without subtracting or wrapping

- quarantines forged unmap counters without subtracting or wrapping
   - Expected: zero_rejected.mapped_pages equals `0u64`
   - Expected: zero_rejected.pages_to_unmap equals `1u64`
   - Expected: pending_rejected.mapped_pages equals `1u64`
   - Expected: pending_rejected.pages_to_unmap equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("quarantines forged unmap counters without subtracting or wrapping")
val zero_mapped = forged_lifecycle(
    ExecutableLoadConsumerStateV1.Unmapping, 1u64, 0u64, 1u64, 0u64)
val zero_rejected = executable_load_consumer_unmap_page_v1(
    zero_mapped, true)
expect(zero_rejected.state).to_equal(
    ExecutableLoadConsumerStateV1.Quarantined)
expect(zero_rejected.failure).to_equal(
    ExecutableLoadConsumerErrorV1.InvalidTransition)
expect(zero_rejected.mapped_pages).to_equal(0u64)
expect(zero_rejected.pages_to_unmap).to_equal(1u64)

val impossible_pending = forged_lifecycle(
    ExecutableLoadConsumerStateV1.Unmapping, 2u64, 1u64, 2u64, 0u64)
val pending_rejected = executable_load_consumer_unmap_page_v1(
    impossible_pending, true)
expect(pending_rejected.state).to_equal(
    ExecutableLoadConsumerStateV1.Quarantined)
expect(pending_rejected.mapped_pages).to_equal(1u64)
expect(pending_rejected.pages_to_unmap).to_equal(2u64)
```

</details>

#### quarantines impossible map release and close lifecycle counters

- quarantines impossible map release and close lifecycle counters
   - Expected: map_rejected.mapped_pages equals `2u64`
   - Expected: release_rejected.pages_to_unmap equals `0u64`
   - Expected: close_rejected.close_attempt equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("quarantines impossible map release and close lifecycle counters")
val forged_mapping = forged_lifecycle(
    ExecutableLoadConsumerStateV1.Mapping, 1u64, 2u64, 0u64, 0u64)
val map_rejected = executable_load_consumer_map_page_v1(
    forged_mapping, true)
expect(map_rejected.state).to_equal(
    ExecutableLoadConsumerStateV1.Quarantined)
expect(map_rejected.mapped_pages).to_equal(2u64)

val forged_mapped = forged_lifecycle(
    ExecutableLoadConsumerStateV1.MappedBlocked, 2u64, 1u64, 0u64, 0u64)
val release_rejected = executable_load_consumer_begin_release_v1(
    forged_mapped)
expect(release_rejected.state).to_equal(
    ExecutableLoadConsumerStateV1.Quarantined)
expect(release_rejected.pages_to_unmap).to_equal(0u64)

val forged_close = forged_lifecycle(
    ExecutableLoadConsumerStateV1.ClosePending, 1u64, 1u64, 0u64, 0u64)
val close_rejected = executable_load_consumer_close_v1(
    forged_close, true)
expect(close_rejected.state).to_equal(
    ExecutableLoadConsumerStateV1.Quarantined)
expect(close_rejected.close_attempt).to_equal(0u64)

val close_overflow = forged_lifecycle(
    ExecutableLoadConsumerStateV1.ClosePending,
    1u64, 0u64, 0u64, 18446744073709551615u64)
val overflow_rejected = executable_load_consumer_close_v1(
    close_overflow, false)
expect(overflow_rejected.state).to_equal(
    ExecutableLoadConsumerStateV1.Quarantined)
expect(overflow_rejected.failure).to_equal(
    ExecutableLoadConsumerErrorV1.CloseFailed)
expect(overflow_rejected.close_attempt).to_equal(
    18446744073709551615u64)
```

</details>

#### rolls back a partial map and retries close exactly once per attempt

- rolls back a partial map and retries close exactly once per attempt
   - Expected: state.state equals `ExecutableLoadConsumerStateV1.Unmapping`
   - Expected: state.pages_to_unmap equals `1u64`
   - Expected: state.state equals `ExecutableLoadConsumerStateV1.ClosePending`
   - Expected: state.state equals `ExecutableLoadConsumerStateV1.CloseRetryable`
   - Expected: state.state equals `ExecutableLoadConsumerStateV1.Released`
   - Expected: state.close_attempt equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rolls back a partial map and retries close exactly once per attempt")
val ready = executable_load_consumer_new_v1("simpleos", "x86_64", "simpleos")
val planned = executable_load_consumer_plan_v1(
    ready, load_handle("x86_64", "simpleos", [exec_range(), data_range()]),
    0x400100u64)
var state = executable_load_consumer_begin_mapping_v1(planned)
state = executable_load_consumer_map_page_v1(state, true)
state = executable_load_consumer_map_page_v1(state, false)
expect(state.state).to_equal(ExecutableLoadConsumerStateV1.Unmapping)
expect(state.pages_to_unmap).to_equal(1u64)
state = executable_load_consumer_unmap_page_v1(state, true)
expect(state.state).to_equal(ExecutableLoadConsumerStateV1.ClosePending)
state = executable_load_consumer_close_v1(state, false)
expect(state.state).to_equal(ExecutableLoadConsumerStateV1.CloseRetryable)
state = executable_load_consumer_begin_release_v1(state)
state = executable_load_consumer_close_v1(state, true)
expect(state.state).to_equal(ExecutableLoadConsumerStateV1.Released)
expect(state.close_attempt).to_equal(2u64)
val receipt = executable_load_consumer_receipt_v1(state)
if receipt.execution_authorized:
    fail("pure rollback receipt authorized execution")
```

</details>

#### releases every mapped page before close and quarantines unmap failure

- releases every mapped page before close and quarantines unmap failure
   - Expected: loaded.state equals `ExecutableLoadConsumerStateV1.MappedBlocked`
   - Expected: releasing.state equals `ExecutableLoadConsumerStateV1.Released`
   - Expected: releasing.mapped_pages equals `0u64`
   - Expected: failed.state equals `ExecutableLoadConsumerStateV1.Quarantined`
   - Expected: failed.failure equals `ExecutableLoadConsumerErrorV1.RollbackFailed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("releases every mapped page before close and quarantines unmap failure")
val ready = executable_load_consumer_new_v1("simpleos", "x86_64", "simpleos")
val planned = executable_load_consumer_plan_v1(
    ready, load_handle("x86_64", "simpleos", [exec_range()]), 0x400100u64)
var loaded = executable_load_consumer_begin_mapping_v1(planned)
loaded = executable_load_consumer_map_page_v1(loaded, true)
expect(loaded.state).to_equal(ExecutableLoadConsumerStateV1.MappedBlocked)
val blocked_receipt = executable_load_consumer_receipt_v1(loaded)
expect(blocked_receipt.execution_authorized).to_be(false)
expect(blocked_receipt.reason).to_equal(
    "legacy-loader-mapped-lease-not-scheduler-adoptable")
var releasing = executable_load_consumer_begin_release_v1(loaded)
releasing = executable_load_consumer_unmap_page_v1(releasing, true)
releasing = executable_load_consumer_close_v1(releasing, true)
expect(releasing.state).to_equal(ExecutableLoadConsumerStateV1.Released)
expect(releasing.mapped_pages).to_equal(0u64)

var failed = executable_load_consumer_begin_release_v1(loaded)
failed = executable_load_consumer_unmap_page_v1(failed, false)
expect(failed.state).to_equal(ExecutableLoadConsumerStateV1.Quarantined)
expect(failed.failure).to_equal(ExecutableLoadConsumerErrorV1.RollbackFailed)
```

</details>

#### never turns a forged adopted lifecycle value into authority

- never turns a forged adopted lifecycle value into authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("never turns a forged adopted lifecycle value into authority")
val forged = forged_lifecycle(
    ExecutableLoadConsumerStateV1.Adopted,
    1u64, 1u64, 0u64, 1u64)
val receipt = executable_load_consumer_receipt_v1(forged)
expect(receipt.execution_authorized).to_be(false)
expect(receipt.reason).to_equal(
    "adopted-state-requires-scheduler-authority")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/executable_load_consumer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded executable load planning, pure executable load lifecycle.
- bounded executable load planning
- pure executable load lifecycle

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e7a2800045e6e5e134250a58506a075314050ef4049b7f6b0dbca05f11c9ea10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7a2800045e6e5e134250a58506a075314050ef4049b7f6b0dbca05f11c9ea10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7a2800045e6e5e134250a58506a075314050ef4049b7f6b0dbca05f11c9ea10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/kernel/loader/executable_load_consumer_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/executable_load_consumer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/executable_load_consumer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/executable_load_consumer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/executable_load_consumer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/executable_load_consumer_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an exact x86_64 SimpleOS plan and counts mapped pages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/executable_load_consumer_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsupported architecture ABI mismatch and non-executable entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/executable_load_consumer_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects W-X page alias overflow and per-segment page excess' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
