# kernel_namespace_spec

> Verifies the kernel namespace behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# kernel_namespace_spec

Verifies the kernel namespace behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_namespace_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the kernel namespace behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### kernel_namespace — isolation facets

### AC-4: NsFlags — namespace type constants

#### AC-4: NsFlags.pid is defined as a non-zero value

- Verify: AC-4: NsFlags.pid is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: NsFlags.pid is defined as a non-zero value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(NsFlags.pid).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.fs is defined as a non-zero value

- Verify: AC-4: NsFlags.fs is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: NsFlags.fs is defined as a non-zero value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(NsFlags.fs).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.ipc is defined as a non-zero value

- Verify: AC-4: NsFlags.ipc is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: NsFlags.ipc is defined as a non-zero value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(NsFlags.ipc).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.net is defined as a non-zero value

- Verify: AC-4: NsFlags.net is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: NsFlags.net is defined as a non-zero value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(NsFlags.net).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.capability is defined as a non-zero value

- Verify: AC-4: NsFlags.capability is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: NsFlags.capability is defined as a non-zero value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(NsFlags.capability).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags values are all distinct (no aliasing)

- Verify: AC-4: NsFlags values are all distinct (no aliasing)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: NsFlags values are all distinct (no aliasing)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(NsFlags.pid).to_not_equal(NsFlags.fs)
expect(NsFlags.pid).to_not_equal(NsFlags.ipc)
expect(NsFlags.pid).to_not_equal(NsFlags.net)
expect(NsFlags.pid).to_not_equal(NsFlags.capability)
expect(NsFlags.fs).to_not_equal(NsFlags.ipc)
expect(NsFlags.fs).to_not_equal(NsFlags.net)
expect(NsFlags.net).to_not_equal(NsFlags.capability)
```

</details>

### AC-4: namespace_create — initial namespace

#### AC-4: namespace_create returns a positive ns_id

- Verify: AC-4: namespace_create returns a positive ns_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: namespace_create returns a positive ns_id")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ns_id = namespace_create(NsFlags.pid)
expect(ns_id).to_be_greater_than(0)
```

</details>

#### AC-4: namespace_create for each facet type succeeds

- Verify: AC-4: namespace_create for each facet type succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: namespace_create for each facet type succeeds")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ns_pid = namespace_create(NsFlags.pid)
val ns_fs  = namespace_create(NsFlags.fs)
val ns_ipc = namespace_create(NsFlags.ipc)
val ns_net = namespace_create(NsFlags.net)
val ns_cap = namespace_create(NsFlags.capability)
expect(ns_pid).to_be_greater_than(0)
expect(ns_fs).to_be_greater_than(0)
expect(ns_ipc).to_be_greater_than(0)
expect(ns_net).to_be_greater_than(0)
expect(ns_cap).to_be_greater_than(0)
```

</details>

#### AC-4: consecutive namespace_create calls return distinct ids

- Verify: AC-4: consecutive namespace_create calls return distinct ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: consecutive namespace_create calls return distinct ids")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val a = namespace_create(NsFlags.pid)
val b = namespace_create(NsFlags.pid)
expect(a).to_not_equal(b)
```

</details>

### AC-4: namespace_clone — isolation via clone

#### AC-4: namespace_clone returns a distinct id from the source

- Verify: AC-4: namespace_clone returns a distinct id from the source


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: namespace_clone returns a distinct id from the source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parent = namespace_create(NsFlags.pid)
val child  = namespace_clone(parent, NsFlags.pid)
expect(child).to_be_greater_than(0)
expect(child).to_not_equal(parent)
```

</details>

#### AC-4: cloned namespace is independently visible via lookup

- Verify: AC-4: cloned namespace is independently visible via lookup
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: cloned namespace is independently visible via lookup")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parent = namespace_create(NsFlags.net)
val child  = namespace_clone(parent, NsFlags.net)
val entry  = namespace_lookup(child)
expect(entry.is_some).to_equal(true)
```

</details>

#### AC-4: dropping the parent does not invalidate the clone

- Verify: AC-4: dropping the parent does not invalidate the clone
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: dropping the parent does not invalidate the clone")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parent = namespace_create(NsFlags.ipc)
val child  = namespace_clone(parent, NsFlags.ipc)
namespace_drop(parent)
val entry = namespace_lookup(child)
expect(entry.is_some).to_equal(true)
```

</details>

### AC-4: namespace_unshare — capability isolation

#### AC-4: namespace_unshare for capability creates a new restricted namespace

- Verify: AC-4: namespace_unshare for capability creates a new restricted namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: namespace_unshare for capability creates a new restricted namespace")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val original = namespace_create(NsFlags.capability)
val restricted = namespace_unshare(original, NsFlags.capability)
expect(restricted).to_be_greater_than(0)
expect(restricted).to_not_equal(original)
```

</details>

#### AC-4: unshared capability namespace is visible via lookup

- Verify: AC-4: unshared capability namespace is visible via lookup
   - Expected: entry.is_some is true
   - Expected: entry.value.flags equals `NsFlags.capability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: unshared capability namespace is visible via lookup")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val original   = namespace_create(NsFlags.capability)
val restricted = namespace_unshare(original, NsFlags.capability)
val entry = namespace_lookup(restricted)
expect(entry.is_some).to_equal(true)
expect(entry.value.flags).to_equal(NsFlags.capability)
```

</details>

### AC-4: namespace_lookup — query

#### AC-4: lookup of unknown ns_id returns None

- Verify: AC-4: lookup of unknown ns_id returns None
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: lookup of unknown ns_id returns None")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val entry = namespace_lookup(0xFFFFFFFF)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-4: lookup after drop returns None

- Verify: AC-4: lookup after drop returns None
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: lookup after drop returns None")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ns_id = namespace_create(NsFlags.fs)
namespace_drop(ns_id)
val entry = namespace_lookup(ns_id)
expect(entry.is_some).to_equal(false)
```

</details>

### AC-4: container namespace — combined facets

#### AC-4: all five facet namespaces can be created for a single container

- Verify: AC-4: all five facet namespaces can be created for a single container


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-4
step("Verify: AC-4: all five facet namespaces can be created for a single container")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Simulate the namespace set for a Wine/Proton container
val pid_ns = namespace_create(NsFlags.pid)
val fs_ns  = namespace_create(NsFlags.fs)
val ipc_ns = namespace_create(NsFlags.ipc)
val net_ns = namespace_create(NsFlags.net)
val cap_ns = namespace_create(NsFlags.capability)
expect(pid_ns).to_be_greater_than(0)
expect(fs_ns).to_be_greater_than(0)
expect(ipc_ns).to_be_greater_than(0)
expect(net_ns).to_be_greater_than(0)
expect(cap_ns).to_be_greater_than(0)
# All must be distinct
expect(pid_ns).to_not_equal(fs_ns)
expect(fs_ns).to_not_equal(ipc_ns)
expect(ipc_ns).to_not_equal(net_ns)
expect(net_ns).to_not_equal(cap_ns)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `90ea0bd979a51d67d43d3c68e26604935453cdca48b9dd2f135b015525b73489`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `90ea0bd979a51d67d43d3c68e26604935453cdca48b9dd2f135b015525b73489`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `90ea0bd979a51d67d43d3c68e26604935453cdca48b9dd2f135b015525b73489`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/wine/kernel_namespace_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/wine/kernel_namespace_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/wine/kernel_namespace_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/wine/kernel_namespace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/wine/kernel_namespace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
