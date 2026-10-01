# Container namespace enforcement at the LIVE VFS lookup site

> The `ContainerNamespaceView` model is covered elsewhere (the 32-attack escape suite). This spec covers something the model cannot: that the enforcement is actually **on the path a process really resolves through** — `VfsManager` in `src/os/services/vfs/vfs.spl`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Container namespace enforcement at the LIVE VFS lookup site

The `ContainerNamespaceView` model is covered elsewhere (the 32-attack escape suite). This spec covers something the model cannot: that the enforcement is actually **on the path a process really resolves through** — `VfsManager` in `src/os/services/vfs/vfs.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-CONTAINER #OS-VFS |
| Category | Security / Isolation |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `ContainerNamespaceView` model is covered elsewhere (the 32-attack escape
suite). This spec covers something the model cannot: that the enforcement is
actually **on the path a process really resolves through** —
`VfsManager` in `src/os/services/vfs/vfs.spl`.

Every path-taking VFS operation funnels through `enforce_lookup_grants`, which
is deny-wins over the ai-cli grant gate and the container namespace gate. The
namespace decision is delegated wholesale to the kernel primitive
`container_view_allows_path`; this spec proves the *wiring*, not the model.

The single most dangerous property here is the **non-container regression**: a
host-context manager (no view) must behave exactly as it did before container
enforcement existed. That is asserted first and asserted broadly.

## Scenarios

### host-context VFS is unaffected by container enforcement

#### resolves every path when no container view is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### does not enforce a namespace on a bare host manager

- The namespace gate itself allows anything in host context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The namespace gate itself allows anything in host context")
var vfs = mounted_vfs()
assert_true(vfs.enforce_container_namespace("stat", "/anything/../at/all").is_ok())
assert_true(vfs.enforce_lookup_grants("open", "/etc/shadow").is_ok())
```

</details>

### a container resolves only inside its own root

#### allows in-root lookups for the owning container

- Enter container A's namespace, rooted at /containers/a
- Paths at and below the root resolve


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter container A's namespace, rooted at /containers/a")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))
assert_true(vfs.in_container())

step("Paths at and below the root resolve")
assert_true(vfs.stat("/containers/a").is_ok())
assert_true(vfs.open("/containers/a/bin/app", read_flags()).is_ok())
assert_true(vfs.readdir("/containers/a/etc").is_ok())
assert_true(vfs.mkdir("/containers/a/tmp").is_ok())
```

</details>

#### refuses the SAME path for a container that does not own it

- Enter container B's namespace, rooted at /containers/b
- The path that resolved for A is refused for B


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter container B's namespace, rooted at /containers/b")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/b", [202u64]))

step("The path that resolved for A is refused for B")
val opened = vfs.open("/containers/a/bin/app", read_flags())
assert_true(opened.is_err())
assert_contains(opened.unwrap_err(), "container namespace denies")

assert_true(vfs.stat("/containers/a").is_err())
assert_true(vfs.readdir("/containers/a/etc").is_err())
assert_true(vfs.mkdir("/containers/a/tmp").is_err())
```

</details>

#### refuses host paths and traversal escapes from inside a container

- Enter container A
- Host paths are outside the view
- A traversal escape is REFUSED, never normalized


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter container A")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))

step("Host paths are outside the view")
assert_true(vfs.stat("/etc/shadow").is_err())
assert_true(vfs.open("/", read_flags()).is_err())

step("A traversal escape is REFUSED, never normalized")
assert_true(vfs.stat("/containers/a/../b/secret").is_err())
assert_true(vfs.open("/containers/a/../../etc/shadow", read_flags()).is_err())
```

</details>

#### restores host semantics when the container context is left

- Enter, then leave


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter, then leave")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))
assert_true(vfs.stat("/etc/shadow").is_err())

vfs.leave_container()
assert_false(vfs.in_container())
assert_true(vfs.stat("/etc/shadow").is_ok())
```

</details>

### a stopped container's lookups fail closed

#### resolves nothing under a rootless view

- Enter the view a stopped container holds
- Even the container's own former root is refused
- Nothing resolves, host paths included


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter the view a stopped container holds")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_rootless())
assert_true(vfs.in_container())

step("Even the container's own former root is refused")
assert_true(vfs.stat("/containers/a").is_err())
assert_true(vfs.open("/containers/a/bin/app", read_flags()).is_err())
assert_true(vfs.readdir("/containers/a").is_err())
assert_true(vfs.mkdir("/containers/a/tmp").is_err())
assert_true(vfs.unlink("/containers/a/f").is_err())

step("Nothing resolves, host paths included")
assert_true(vfs.stat("/").is_err())
assert_true(vfs.stat("/etc/shadow").is_err())
```

</details>

#### treats the explicit rootless entry point the same way

- enter_rootless_container is the same deny-everything state


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("enter_rootless_container is the same deny-everything state")
var vfs = mounted_vfs()
vfs.enter_rootless_container()
assert_true(vfs.stat("/containers/a").is_err())
assert_true(vfs.enforce_lookup_grants("open", "/containers/a").is_err())
```

</details>

### write-side operations obey the same gate

#### refuses a rename whose destination leaves the view

- Enter container A
- In-view to in-view is allowed
- In-view to OUT-of-view is refused
- OUT-of-view source is refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter container A")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))

step("In-view to in-view is allowed")
assert_true(vfs.rename("/containers/a/f", "/containers/a/g").is_ok())

step("In-view to OUT-of-view is refused")
assert_true(vfs.rename("/containers/a/f", "/containers/b/g").is_err())

step("OUT-of-view source is refused")
assert_true(vfs.rename("/etc/shadow", "/containers/a/g").is_err())
```

</details>

#### refuses a symlink that would point out of the view

- Enter container A


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter container A")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))

assert_true(vfs.symlink("/containers/a/t", "/containers/a/l").is_ok())
assert_true(vfs.symlink("/etc/shadow", "/containers/a/l").is_err())
assert_true(vfs.symlink("/containers/a/t", "/etc/l").is_err())
```

</details>

#### refuses unlink and rmdir outside the view

- Enter container A


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enter container A")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))

assert_true(vfs.unlink("/containers/a/f").is_ok())
assert_true(vfs.unlink("/containers/b/f").is_err())
assert_true(vfs.rmdir("/containers/a/d").is_ok())
assert_true(vfs.rmdir("/etc").is_err())
```

</details>

### the converged gate is deny-wins
_There is ONE gate on the lookup path, not two competing ones._

#### refuses when the namespace refuses, whatever else allows

- A container-context manager with no ai-cli manifest at all
- The ai-cli gate alone would allow this path
- The converged gate still refuses it


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A container-context manager with no ai-cli manifest at all")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))

step("The ai-cli gate alone would allow this path")
assert_true(vfs.enforce_ai_cli_file_grant("open", "/etc/shadow").is_ok())

step("The converged gate still refuses it")
val decision = vfs.enforce_lookup_grants("open", "/etc/shadow")
assert_true(decision.is_err())
assert_contains(decision.unwrap_err(), "container namespace denies")
```

</details>

#### names the operation in the refusal

- The refusal is attributable to the operation that caused it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The refusal is attributable to the operation that caused it")
var vfs = mounted_vfs()
vfs.enter_container_view(container_view_create("/containers/a", [101u64]))
assert_contains(vfs.enforce_lookup_grants("readdir", "/etc").unwrap_err(), "readdir")
assert_contains(vfs.enforce_lookup_grants("unlink", "/etc").unwrap_err(), "unlink")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `325157a5d749491a25256c9a11d5164850f4379313597d7b7140571203e24be8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `325157a5d749491a25256c9a11d5164850f4379313597d7b7140571203e24be8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `325157a5d749491a25256c9a11d5164850f4379313597d7b7140571203e24be8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl
mirror: doc/06_spec/01_unit/os/services/vfs/container_lookup_enforcement_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/vfs/container_lookup_enforcement_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/vfs/container_lookup_enforcement_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl:127:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'resolves every path when no container view is set' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not enforce a namespace on a bare host manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows in-root lookups for the owning container' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/container_lookup_enforcement_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses the SAME path for a container that does not own it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
