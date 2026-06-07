# Baremetal Method Dispatch Specification

> 1. var a: AmbigInitA = AmbigInitA new

<!-- sdn-diagram:id=baremetal_method_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_method_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_method_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_method_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Method Dispatch Specification

## Scenarios

### baremetal method dispatch — local-annotation type qualifier

#### annotated `var x: T = T.new()` receivers

#### dispatches `a.init()` to AmbigInitA.init even when receiver.ty is unnamed

1. var a: AmbigInitA = AmbigInitA new
2. a init


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Mirrors the desktop_e2e_entry.spl pattern that exposed the
# bug. With the Round-16 fix, MIR lowering recovers the
# `: AmbigInitA` annotation from the function's local table
# so `a.init()` qualifies as `AmbigInitA.init` and never
# dispatches to `AmbigInitB.init`.
var a: AmbigInitA = AmbigInitA.new()
a.init()
expect(a.last).to_be(101)
```

</details>

#### dispatches `b.init()` to AmbigInitB.init when both classes are in scope

1. var b: AmbigInitB = AmbigInitB new
2. b init


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b: AmbigInitB = AmbigInitB.new()
b.init()
expect(b.tag).to_be(202)
```

</details>

#### keeps each typed receiver's init body isolated

1. var a: AmbigInitA = AmbigInitA new
2. var b: AmbigInitB = AmbigInitB new
3. a init
4. b init


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: AmbigInitA = AmbigInitA.new()
var b: AmbigInitB = AmbigInitB.new()
a.init()
b.init()
expect(a.last).to_be(101)
expect(b.tag).to_be(202)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/baremetal_method_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- baremetal method dispatch — local-annotation type qualifier

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
