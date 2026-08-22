# kernel_process_table_spec

> Verifies the kernel process table behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kernel_process_table_spec

Verifies the kernel process table behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_process_table_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the kernel process table behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### kernel_process_table — PID registry

### AC-1: process_table_alloc_pid — real PID allocation

#### AC-1: alloc_pid returns a positive non-zero PID

- Verify: AC-1: alloc_pid returns a positive non-zero PID


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: alloc_pid returns a positive non-zero PID")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = process_table_alloc_pid()
expect(pid).to_be_greater_than(0)
```

</details>

#### AC-1: consecutive alloc_pid calls return distinct PIDs

- Verify: AC-1: consecutive alloc_pid calls return distinct PIDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: consecutive alloc_pid calls return distinct PIDs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid1 = process_table_alloc_pid()
val pid2 = process_table_alloc_pid()
expect(pid1).to_be_greater_than(0)
expect(pid2).to_be_greater_than(0)
# PIDs must be distinct (no duplicate allocation)
expect(pid1).to_not_equal(pid2)
```

</details>

#### AC-1: PID zero is reserved and never allocated

- Verify: AC-1: PID zero is reserved and never allocated


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: PID zero is reserved and never allocated")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# The kernel convention: PID 0 = idle/swapper; never returned to userland
val pid = process_table_alloc_pid()
expect(pid).to_not_equal(0)
```

</details>

### AC-1: process_table_register — process entry creation

#### AC-1: registered process is visible via lookup

- Verify: AC-1: registered process is visible via lookup
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: registered process is visible via lookup")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = process_table_alloc_pid()
# asid=1 and a sentinel ns_id=42 represent a real ASID and namespace
process_table_register(pid, 1, 42)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
```

</details>

#### AC-1: registered entry carries the correct PID

- Verify: AC-1: registered entry carries the correct PID
   - Expected: entry.is_some is true
   - Expected: entry.value.pid equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: registered entry carries the correct PID")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = process_table_alloc_pid()
process_table_register(pid, 2, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.pid).to_equal(pid)
```

</details>

#### AC-1: registered entry carries the supplied asid

- Verify: AC-1: registered entry carries the supplied asid
   - Expected: entry.is_some is true
   - Expected: entry.value.asid equals `asid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: registered entry carries the supplied asid")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = process_table_alloc_pid()
val asid: u64 = 7
process_table_register(pid, asid, 1)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(true)
expect(entry.value.asid).to_equal(asid)
```

</details>

#### AC-1: registered entry carries the supplied namespace ref

- Verify: AC-1: registered entry carries the supplied namespace ref
   - Expected: entry.is_some is true
   - Expected: entry.value.ns_id equals `ns_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: registered entry carries the supplied namespace ref")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: AC-1: lookup of unregistered PID returns None
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: lookup of unregistered PID returns None")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# A large PID unlikely to be registered
val entry = process_table_lookup(65534)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-1: lookup returns Some after register and None after reap

- Verify: AC-1: lookup returns Some after register and None after reap
   - Expected: before.is_some is true
   - Expected: after.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: lookup returns Some after register and None after reap")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: AC-1: reap on a registered PID succeeds without error
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: reap on a registered PID succeeds without error")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = process_table_alloc_pid()
process_table_register(pid, 4, 1)
# reap returns void; we verify by confirming lookup is None afterward
process_table_reap(pid)
val entry = process_table_lookup(pid)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-1: no resident fallback markers remain after reap

- Verify: AC-1: no resident fallback markers remain after reap
   - Expected: entry.is_some is true
   - Expected: entry.value.state equals `running`
   - Expected: reaped.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1 REQ-4
step("Verify: AC-1: no resident fallback markers remain after reap")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c217adfb0861570f0d3c5d453eae0c97fe6d29cfb7691241a2d2c5152d1796c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c217adfb0861570f0d3c5d453eae0c97fe6d29cfb7691241a2d2c5152d1796c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c217adfb0861570f0d3c5d453eae0c97fe6d29cfb7691241a2d2c5152d1796c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/wine/kernel_process_table_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/kernel_process_table_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/wine/kernel_process_table_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/wine/kernel_process_table_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/kernel_process_table_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
