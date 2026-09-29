# Kernel Namespace Specification

> Tests covering kernel_namespace — isolation facets, AC-4: NsFlags — namespace type constants, AC-4: namespace_create — initial namespace, AC-4: namespace_clone — isolation via clone, AC-4: namespace_unshare — capability isolation, AC-4: namespace_lookup — query, AC-4: container namespace — combined facets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Namespace Specification

## Scenarios

### kernel_namespace — isolation facets

### AC-4: NsFlags — namespace type constants

#### AC-4: NsFlags.pid is defined as a non-zero value

- AC-4: NsFlags.pid is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: NsFlags.pid is defined as a non-zero value")
expect(NsFlags.pid).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.fs is defined as a non-zero value

- AC-4: NsFlags.fs is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: NsFlags.fs is defined as a non-zero value")
expect(NsFlags.fs).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.ipc is defined as a non-zero value

- AC-4: NsFlags.ipc is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: NsFlags.ipc is defined as a non-zero value")
expect(NsFlags.ipc).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.net is defined as a non-zero value

- AC-4: NsFlags.net is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: NsFlags.net is defined as a non-zero value")
expect(NsFlags.net).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags.capability is defined as a non-zero value

- AC-4: NsFlags.capability is defined as a non-zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: NsFlags.capability is defined as a non-zero value")
expect(NsFlags.capability).to_be_greater_than(0)
```

</details>

#### AC-4: NsFlags values are all distinct (no aliasing)

- AC-4: NsFlags values are all distinct (no aliasing)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: NsFlags values are all distinct (no aliasing)")
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

- AC-4: namespace_create returns a positive ns_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: namespace_create returns a positive ns_id")
val ns_id = namespace_create(NsFlags.pid)
expect(ns_id).to_be_greater_than(0)
```

</details>

#### AC-4: namespace_create for each facet type succeeds

- AC-4: namespace_create for each facet type succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: namespace_create for each facet type succeeds")
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

- AC-4: consecutive namespace_create calls return distinct ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: consecutive namespace_create calls return distinct ids")
val a = namespace_create(NsFlags.pid)
val b = namespace_create(NsFlags.pid)
expect(a).to_not_equal(b)
```

</details>

### AC-4: namespace_clone — isolation via clone

#### AC-4: namespace_clone returns a distinct id from the source

- AC-4: namespace_clone returns a distinct id from the source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: namespace_clone returns a distinct id from the source")
val parent = namespace_create(NsFlags.pid)
val child  = namespace_clone(parent, NsFlags.pid)
expect(child).to_be_greater_than(0)
expect(child).to_not_equal(parent)
```

</details>

#### AC-4: cloned namespace is independently visible via lookup

- AC-4: cloned namespace is independently visible via lookup
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: cloned namespace is independently visible via lookup")
val parent = namespace_create(NsFlags.net)
val child  = namespace_clone(parent, NsFlags.net)
val entry  = namespace_lookup(child)
expect(entry.is_some).to_equal(true)
```

</details>

#### AC-4: dropping the parent does not invalidate the clone

- AC-4: dropping the parent does not invalidate the clone
   - Expected: entry.is_some is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: dropping the parent does not invalidate the clone")
val parent = namespace_create(NsFlags.ipc)
val child  = namespace_clone(parent, NsFlags.ipc)
namespace_drop(parent)
val entry = namespace_lookup(child)
expect(entry.is_some).to_equal(true)
```

</details>

### AC-4: namespace_unshare — capability isolation

#### AC-4: namespace_unshare for capability creates a new restricted namespace

- AC-4: namespace_unshare for capability creates a new restricted namespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: namespace_unshare for capability creates a new restricted namespace")
val original = namespace_create(NsFlags.capability)
val restricted = namespace_unshare(original, NsFlags.capability)
expect(restricted).to_be_greater_than(0)
expect(restricted).to_not_equal(original)
```

</details>

#### AC-4: unshared capability namespace is visible via lookup

- AC-4: unshared capability namespace is visible via lookup
   - Expected: entry.is_some is true
   - Expected: entry.value.flags equals `NsFlags.capability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: unshared capability namespace is visible via lookup")
val original   = namespace_create(NsFlags.capability)
val restricted = namespace_unshare(original, NsFlags.capability)
val entry = namespace_lookup(restricted)
expect(entry.is_some).to_equal(true)
expect(entry.value.flags).to_equal(NsFlags.capability)
```

</details>

### AC-4: namespace_lookup — query

#### AC-4: lookup of unknown ns_id returns None

- AC-4: lookup of unknown ns_id returns None
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: lookup of unknown ns_id returns None")
val entry = namespace_lookup(0xFFFFFFFF)
expect(entry.is_some).to_equal(false)
```

</details>

#### AC-4: lookup after drop returns None

- AC-4: lookup after drop returns None
   - Expected: entry.is_some is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: lookup after drop returns None")
val ns_id = namespace_create(NsFlags.fs)
namespace_drop(ns_id)
val entry = namespace_lookup(ns_id)
expect(entry.is_some).to_equal(false)
```

</details>

### AC-4: container namespace — combined facets

#### AC-4: all five facet namespaces can be created for a single container

- AC-4: all five facet namespaces can be created for a single container


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-4: all five facet namespaces can be created for a single container")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/wine/kernel_namespace_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel_namespace — isolation facets, AC-4: NsFlags — namespace type constants, AC-4: namespace_create — initial namespace, AC-4: namespace_clone — isolation via clone, AC-4: namespace_unshare — capability isolation, AC-4: namespace_lookup — query, AC-4: container namespace — combined facets.
- kernel_namespace — isolation facets
- AC-4: NsFlags — namespace type constants
- AC-4: namespace_create — initial namespace
- AC-4: namespace_clone — isolation via clone
- AC-4: namespace_unshare — capability isolation
- AC-4: namespace_lookup — query
- AC-4: container namespace — combined facets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-4).`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4a823d704ff7a94a133df5b5df4b6e7336c05552dff89d0f94c05119963a040`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4a823d704ff7a94a133df5b5df4b6e7336c05552dff89d0f94c05119963a040`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4a823d704ff7a94a133df5b5df4b6e7336c05552dff89d0f94c05119963a040`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/kernel/wine/kernel_namespace_spec.spl
mirror: doc/06_spec/unit/os/kernel/wine/kernel_namespace_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/unit/os/kernel/wine/kernel_namespace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/wine/kernel_namespace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/wine/kernel_namespace_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/kernel/wine/kernel_namespace_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: NsFlags.pid is defined as a non-zero value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/wine/kernel_namespace_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: NsFlags.fs is defined as a non-zero value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/wine/kernel_namespace_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: NsFlags.ipc is defined as a non-zero value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
