# Kernel Process Table Specification

> Tests covering kernel_process_table — PID registry, AC-1: process_table_alloc_pid — real PID allocation, AC-1: process_table_register — process entry creation, AC-1: process_table_lookup — process query, AC-1: process_table_reap — entry removal.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Process Table Specification

## Scenarios

### kernel_process_table — PID registry

### AC-1: process_table_alloc_pid — real PID allocation

#### AC-1: alloc_pid returns a positive non-zero PID

- AC-1: alloc_pid returns a positive non-zero PID


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: alloc_pid returns a positive non-zero PID")
val pid = process_table_alloc_pid()
expect(pid).to_be_greater_than(0)
```

</details>

#### AC-1: consecutive alloc_pid calls return distinct PIDs

- AC-1: consecutive alloc_pid calls return distinct PIDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: consecutive alloc_pid calls return distinct PIDs")
val pid1 = process_table_alloc_pid()
val pid2 = process_table_alloc_pid()
expect(pid1).to_be_greater_than(0)
expect(pid2).to_be_greater_than(0)
# PIDs must be distinct (no duplicate allocation)
expect(pid1).to_not_equal(pid2)
```

</details>

#### AC-1: PID zero is reserved and never allocated

- AC-1: PID zero is reserved and never allocated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: PID zero is reserved and never allocated")
# The kernel convention: PID 0 = idle/swapper; never returned to userland
val pid = process_table_alloc_pid()
expect(pid).to_not_equal(0)
```

</details>

### AC-1: process_table_register — process entry creation

#### AC-1: registered process is visible via lookup

- AC-1: registered process is visible via lookup
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: registered process is visible via lookup")
val pid = process_table_alloc_pid()
# asid=1 and a sentinel ns_id=42 represent a real ASID and namespace
process_table_register(pid, 1, 42)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
```

</details>

#### AC-1: registered entry carries the correct PID

- AC-1: registered entry carries the correct PID
   - Expected: entry.is_some is true
   - Expected: entry.value.pid equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: registered entry carries the correct PID")
val pid = process_table_alloc_pid()
process_table_register(pid, 2, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.pid).to_equal(pid)
```

</details>

#### AC-1: registered entry carries the supplied asid

- AC-1: registered entry carries the supplied asid
   - Expected: entry.is_some is true
   - Expected: entry.value.asid equals `asid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: registered entry carries the supplied asid")
val pid = process_table_alloc_pid()
val asid: u64 = 7
process_table_register(pid, asid, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.asid).to_equal(asid)
```

</details>

#### AC-1: registered entry carries the supplied namespace ref

- AC-1: registered entry carries the supplied namespace ref
   - Expected: entry.is_some is true
   - Expected: entry.value.ns_id equals `ns_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: registered entry carries the supplied namespace ref")
val pid = process_table_alloc_pid()
val ns_id: u64 = 99
process_table_register(pid, 1, ns_id)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.ns_id).to_equal(ns_id)
```

</details>

### AC-1: process_table_lookup — process query

#### AC-1: lookup of unregistered PID returns None

- AC-1: lookup of unregistered PID returns None
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: lookup of unregistered PID returns None")
# A large PID unlikely to be registered
val entry = process_table_lookup(65534)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-1: lookup returns Some after register and None after reap

- AC-1: lookup returns Some after register and None after reap
   - Expected: before.is_some is true
2. process table reap
   - Expected: after.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: lookup returns Some after register and None after reap")
val pid = process_table_alloc_pid()
process_table_register(pid, 3, 1)
val before = process_table_lookup(pid)
expect(before.is_some).to_equal(true)
process_table_reap(pid)
val after = process_table_lookup(pid)
expect(after.is_some).to_equal(false)
```

</details>

### AC-1: process_table_reap — entry removal

#### AC-1: reap on a registered PID succeeds without error

- AC-1: reap on a registered PID succeeds without error
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: reap on a registered PID succeeds without error")
val pid = process_table_alloc_pid()
process_table_register(pid, 4, 1)
# reap returns void; we verify by confirming lookup is None afterward
process_table_reap(pid)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-1: no resident fallback markers remain after reap

- AC-1: no resident fallback markers remain after reap
   - Expected: entry.is_some is true
   - Expected: entry.value.state equals `running`
2. process table reap
   - Expected: reaped.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("AC-1: no resident fallback markers remain after reap")
# Validates AC-1: apps launch with real PIDs, no fallback markers
val pid = process_table_alloc_pid()
expect(pid).to_be_greater_than(0)
process_table_register(pid, 5, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.state).to_equal("running")
process_table_reap(pid)
val reaped = process_table_lookup(pid)
expect(reaped.is_some).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_process_table_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel_process_table — PID registry, AC-1: process_table_alloc_pid — real PID allocation, AC-1: process_table_register — process entry creation, AC-1: process_table_lookup — process query, AC-1: process_table_reap — entry removal.
- kernel_process_table — PID registry
- AC-1: process_table_alloc_pid — real PID allocation
- AC-1: process_table_register — process entry creation
- AC-1: process_table_lookup — process query
- AC-1: process_table_reap — entry removal

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-1/REQ-4).`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f5b450f0f8c2aa970049a9dc9ed1f677ef859c1fb022581327fd6e7c1a84433f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5b450f0f8c2aa970049a9dc9ed1f677ef859c1fb022581327fd6e7c1a84433f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5b450f0f8c2aa970049a9dc9ed1f677ef859c1fb022581327fd6e7c1a84433f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/wine/kernel_process_table_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/kernel_process_table_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/wine/kernel_process_table_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/kernel_process_table_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/wine/kernel_process_table_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/kernel/wine/kernel_process_table_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: alloc_pid returns a positive non-zero PID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/kernel_process_table_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: consecutive alloc_pid calls return distinct PIDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/wine/kernel_process_table_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: PID zero is reserved and never allocated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
