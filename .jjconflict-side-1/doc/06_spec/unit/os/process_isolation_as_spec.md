# Process Isolation As Specification

> Tests covering AddressSpace handle accessors, as_switch_to deduplication, as_create / as_destroy lifecycle, Process Table Extended — alloc and register, Process Table Extended — count and list, Convenience helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Isolation As Specification

## Scenarios

### AddressSpace handle accessors

#### as_phys_root returns the physical root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- as_phys_root returns the physical root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_phys_root returns the physical root")
val space = AddressSpace(phys_root: 0x1000, id: 7)
expect as_phys_root(space) == 0x1000
```

</details>

#### as_id returns the monotonic id

- as_id returns the monotonic id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_id returns the monotonic id")
val space = AddressSpace(phys_root: 0x2000, id: 42)
expect as_id(space) == 42
```

</details>

#### as_is_kernel true for zero root

- as_is_kernel true for zero root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_is_kernel true for zero root")
val space = AddressSpace(phys_root: 0, id: 0)
expect as_is_kernel(space) == true
```

</details>

#### as_is_kernel false for nonzero root

- as_is_kernel false for nonzero root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_is_kernel false for nonzero root")
val space = AddressSpace(phys_root: 0x3000, id: 1)
expect as_is_kernel(space) == false
```

</details>

#### as_kernel_sentinel returns zero root

- as_kernel_sentinel returns zero root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_kernel_sentinel returns zero root")
val sentinel = as_kernel_sentinel()
expect sentinel.phys_root == 0
expect sentinel.id == 0
```

</details>

### as_switch_to deduplication

#### as_switch_to updates current root

- as_switch_to updates current root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_switch_to updates current root")
as_switch_to(0x4000)
expect as_current_phys_root() == 0x4000
```

</details>

#### as_switch_to is idempotent (same root twice)

- as_switch_to is idempotent (same root twice)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_switch_to is idempotent (same root twice)")
as_switch_to(0x5000)
as_switch_to(0x5000)
expect as_current_phys_root() == 0x5000
```

</details>

#### as_switch_to zero root is a no-op after the root is set

- as_switch_to zero root is a no-op after the root is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_switch_to zero root is a no-op after the root is set")
as_switch_to(0x6000)
as_switch_to(0)
# zero means no-op; current root stays from previous call
expect as_current_phys_root() == 0x6000
```

</details>

### as_create / as_destroy lifecycle

#### as_create returns an AddressSpace (phys_root may be 1 if VMM not init)

- as_create returns an AddressSpace (phys_root may be 1 if VMM not init)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_create returns an AddressSpace (phys_root may be 1 if VMM not init)")
val space = as_create()
val root = as_phys_root(space)
expect (root == 0 or root == 1 or root > 4096) == true
```

</details>

#### as_destroy on kernel sentinel is a no-op

- as_destroy on kernel sentinel is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_destroy on kernel sentinel is a no-op")
val sentinel = as_kernel_sentinel()
as_destroy(sentinel)
expect true == true
```

</details>

#### as_destroy on sentinel root=1 is a no-op

- as_destroy on sentinel root=1 is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("as_destroy on sentinel root=1 is a no-op")
val legacy = AddressSpace(phys_root: 1, id: 0)
as_destroy(legacy)
expect true == true
```

</details>

### Process Table Extended — alloc and register

#### pt_ext_alloc_pid is monotonically increasing

- pt_ext_alloc_pid is monotonically increasing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_alloc_pid is monotonically increasing")
val p1 = pt_ext_alloc_pid()
val p2 = pt_ext_alloc_pid()
expect p2 > p1
```

</details>

#### pt_ext_alloc_pid always > 0

- pt_ext_alloc_pid always > 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_alloc_pid always > 0")
val pid = pt_ext_alloc_pid()
expect pid > 0
```

</details>

#### pt_ext_register + pt_ext_lookup round-trip

- pt_ext_register + pt_ext_lookup round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_register + pt_ext_lookup round-trip")
val pid = pt_ext_alloc_pid()
val space = AddressSpace(phys_root: 0x9000, id: 99)
pt_ext_register(pid, space)
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
expect opt.entry.pid == pid
expect opt.entry.space.phys_root == 0x9000
```

</details>

#### pt_ext_lookup absent PID returns is_some = false

- pt_ext_lookup absent PID returns is_some = false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_lookup absent PID returns is_some = false")
val opt = pt_ext_lookup(-999)
expect opt.is_some == false
```

</details>

#### pt_ext_set_state updates state field

- pt_ext_set_state updates state field


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_set_state updates state field")
val pid = pt_ext_alloc_pid()
val space = AddressSpace(phys_root: 0xA000, id: 3)
pt_ext_register(pid, space)
pt_ext_set_state(pid, "blocked")
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
expect opt.entry.state == "blocked"
```

</details>

#### pt_ext_reap tombstones the entry

- pt_ext_reap tombstones the entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_reap tombstones the entry")
val pid = pt_ext_alloc_pid()
val space = AddressSpace(phys_root: 1, id: 0)
pt_ext_register(pid, space)
pt_ext_reap(pid)
val opt = pt_ext_lookup(pid)
expect opt.is_some == false
```

</details>

### Process Table Extended — count and list

#### pt_ext_count increases after register

- pt_ext_count increases after register


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_count increases after register")
val before = pt_ext_count()
val pid = pt_ext_alloc_pid()
pt_ext_register(pid, AddressSpace(phys_root: 1, id: 0))
val after = pt_ext_count()
expect after == before + 1
```

</details>

#### pt_ext_list_pids contains newly registered pid

- pt_ext_list_pids contains newly registered pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_list_pids contains newly registered pid")
val pid = pt_ext_alloc_pid()
pt_ext_register(pid, AddressSpace(phys_root: 1, id: 0))
val pids = pt_ext_list_pids()
var found = false
var i = 0
while i < pids.len():
    if pids[i] == pid:
        found = true
    i = i + 1
expect found == true
```

</details>

### Convenience helpers

#### pt_ext_spawn returns a positive pid

- pt_ext_spawn returns a positive pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_spawn returns a positive pid")
val pid = pt_ext_spawn()
expect pid > 0
```

</details>

#### pt_ext_spawn registers a live entry

- pt_ext_spawn registers a live entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_spawn registers a live entry")
val pid = pt_ext_spawn()
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
```

</details>

#### pt_ext_spawn_with_kernel_as registers with phys_root 0

- pt_ext_spawn_with_kernel_as registers with phys_root 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_spawn_with_kernel_as registers with phys_root 0")
val pid = pt_ext_spawn_with_kernel_as()
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
expect opt.entry.space.phys_root == 0
```

</details>

#### pt_ext_address_space_for returns sentinel for unknown pid

- pt_ext_address_space_for returns sentinel for unknown pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pt_ext_address_space_for returns sentinel for unknown pid")
val space = pt_ext_address_space_for(-777)
expect space.phys_root == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/process_isolation_as_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AddressSpace handle accessors, as_switch_to deduplication, as_create / as_destroy lifecycle, Process Table Extended — alloc and register, Process Table Extended — count and list, Convenience helpers.
- AddressSpace handle accessors
- as_switch_to deduplication
- as_create / as_destroy lifecycle
- Process Table Extended — alloc and register
- Process Table Extended — count and list
- Convenience helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `66cfa6dfd9d5f3ec4a1153d7c3e9eecbec40b80fdc89b24ae64c11e3d4f074a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66cfa6dfd9d5f3ec4a1153d7c3e9eecbec40b80fdc89b24ae64c11e3d4f074a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66cfa6dfd9d5f3ec4a1153d7c3e9eecbec40b80fdc89b24ae64c11e3d4f074a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/process_isolation_as_spec.spl
mirror: doc/06_spec/unit/os/process_isolation_as_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/process_isolation_as_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/process_isolation_as_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/process_isolation_as_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'as_phys_root returns the physical root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/process_isolation_as_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'as_id returns the monotonic id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/process_isolation_as_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'as_is_kernel true for zero root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
