# process_isolation_as_spec

> Verifies the process isolation as behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# process_isolation_as_spec

Verifies the process isolation as behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/process_isolation_as_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the process isolation as behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### AddressSpace handle accessors

#### as_phys_root returns the physical root

- Verify: as_phys_root returns the physical root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_phys_root returns the physical root")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val space = AddressSpace(phys_root: 0x1000, id: 7)
expect as_phys_root(space) == 0x1000
```

</details>

#### as_id returns the monotonic id

- Verify: as_id returns the monotonic id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_id returns the monotonic id")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val space = AddressSpace(phys_root: 0x2000, id: 42)
expect as_id(space) == 42
```

</details>

#### as_is_kernel true for zero root

- Verify: as_is_kernel true for zero root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_is_kernel true for zero root")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val space = AddressSpace(phys_root: 0, id: 0)
expect as_is_kernel(space) == true
```

</details>

#### as_is_kernel false for nonzero root

- Verify: as_is_kernel false for nonzero root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_is_kernel false for nonzero root")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val space = AddressSpace(phys_root: 0x3000, id: 1)
expect as_is_kernel(space) == false
```

</details>

#### as_kernel_sentinel returns zero root

- Verify: as_kernel_sentinel returns zero root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_kernel_sentinel returns zero root")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val sentinel = as_kernel_sentinel()
expect sentinel.phys_root == 0
expect sentinel.id == 0
```

</details>

### as_switch_to deduplication

#### as_switch_to updates current root

- Verify: as_switch_to updates current root


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_switch_to updates current root")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
as_switch_to(0x4000)
expect as_current_phys_root() == 0x4000
```

</details>

#### as_switch_to is idempotent (same root twice)

- Verify: as_switch_to is idempotent (same root twice)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_switch_to is idempotent (same root twice)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
as_switch_to(0x5000)
as_switch_to(0x5000)
expect as_current_phys_root() == 0x5000
```

</details>

#### as_switch_to zero root is a no-op after the root is set

- Verify: as_switch_to zero root is a no-op after the root is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_switch_to zero root is a no-op after the root is set")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
as_switch_to(0x6000)
as_switch_to(0)
# zero means no-op; current root stays from previous call
expect as_current_phys_root() == 0x6000
```

</details>

### as_create / as_destroy lifecycle

#### as_create returns an AddressSpace (phys_root may be 1 if VMM not init)

- Verify: as_create returns an AddressSpace (phys_root may be 1 if VMM not init)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_create returns an AddressSpace (phys_root may be 1 if VMM not init)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val space = as_create()
val root = as_phys_root(space)
expect (root == 0 or root == 1 or root > 4096) == true
```

</details>

#### as_destroy on kernel sentinel is a no-op

- Verify: as_destroy on kernel sentinel is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_destroy on kernel sentinel is a no-op")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val sentinel = as_kernel_sentinel()
as_destroy(sentinel)
expect as_phys_root(sentinel) == 0
```

</details>

#### as_destroy on sentinel root=1 is a no-op

- Verify: as_destroy on sentinel root=1 is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: as_destroy on sentinel root=1 is a no-op")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val legacy = AddressSpace(phys_root: 1, id: 0)
as_destroy(legacy)
expect as_phys_root(legacy) == 1
```

</details>

### Process Table Extended — alloc and register

#### pt_ext_alloc_pid is monotonically increasing

- Verify: pt_ext_alloc_pid is monotonically increasing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_alloc_pid is monotonically increasing")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val p1 = pt_ext_alloc_pid()
val p2 = pt_ext_alloc_pid()
expect p2 > p1
```

</details>

#### pt_ext_alloc_pid always > 0

- Verify: pt_ext_alloc_pid always > 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_alloc_pid always > 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = pt_ext_alloc_pid()
expect pid > 0
```

</details>

#### pt_ext_register + pt_ext_lookup round-trip

- Verify: pt_ext_register + pt_ext_lookup round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_register + pt_ext_lookup round-trip")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: pt_ext_lookup absent PID returns is_some = false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_lookup absent PID returns is_some = false")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val opt = pt_ext_lookup(-999)
expect opt.is_some == false
```

</details>

#### pt_ext_set_state updates state field

- Verify: pt_ext_set_state updates state field


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_set_state updates state field")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: pt_ext_reap tombstones the entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_reap tombstones the entry")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: pt_ext_count increases after register


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_count increases after register")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val before = pt_ext_count()
val pid = pt_ext_alloc_pid()
pt_ext_register(pid, AddressSpace(phys_root: 1, id: 0))
val after = pt_ext_count()
expect after == before + 1
```

</details>

#### pt_ext_list_pids contains newly registered pid

- Verify: pt_ext_list_pids contains newly registered pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_list_pids contains newly registered pid")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: pt_ext_spawn returns a positive pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_spawn returns a positive pid")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = pt_ext_spawn()
expect pid > 0
```

</details>

#### pt_ext_spawn registers a live entry

- Verify: pt_ext_spawn registers a live entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_spawn registers a live entry")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = pt_ext_spawn()
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
```

</details>

#### pt_ext_spawn_with_kernel_as registers with phys_root 0

- Verify: pt_ext_spawn_with_kernel_as registers with phys_root 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_spawn_with_kernel_as registers with phys_root 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val pid = pt_ext_spawn_with_kernel_as()
val opt = pt_ext_lookup(pid)
expect opt.is_some == true
expect opt.entry.space.phys_root == 0
```

</details>

#### pt_ext_address_space_for returns sentinel for unknown pid

- Verify: pt_ext_address_space_for returns sentinel for unknown pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-OS_PROCESS_ISOLATION_AS-001
step("Verify: pt_ext_address_space_for returns sentinel for unknown pid")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val space = pt_ext_address_space_for(-777)
expect space.phys_root == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7ce1a306883787ed85643ab62a3e9f7101a1bf77d10bcf4ae5416997f62c612b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ce1a306883787ed85643ab62a3e9f7101a1bf77d10bcf4ae5416997f62c612b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ce1a306883787ed85643ab62a3e9f7101a1bf77d10bcf4ae5416997f62c612b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/process_isolation_as_spec.spl
mirror: doc/06_spec/01_unit/os/process_isolation_as_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/process_isolation_as_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/process_isolation_as_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/process_isolation_as_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
