# Memory Capabilities Specification

> <details>

<!-- sdn-diagram:id=memory_capabilities_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=memory_capabilities_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

memory_capabilities_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=memory_capabilities_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Capabilities Specification

## Scenarios

### Memory Capabilities

#### RefCapability

#### maps to Lean names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(caps.RefCapability.Imm.to_lean_name()).to_equal("Shared")
expect(caps.RefCapability.Mut.to_lean_name()).to_equal("Exclusive")
expect(caps.RefCapability.Iso.to_lean_name()).to_equal("Isolated")
```

</details>

#### checks mutation and aliasing rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(caps.RefCapability.Mut.allows_mutation()).to_equal(true)
expect(caps.RefCapability.Imm.allows_mutation()).to_equal(false)
expect(caps.RefCapability.Imm.allows_aliasing()).to_equal(true)
expect(caps.RefCapability.Mut.allows_aliasing()).to_equal(false)
```

</details>

#### CapType

#### builds Lean syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(caps.CapType.imm_type("Int").to_lean()).to_equal("CapType.mk \"Int\" RefCapability.Shared")
expect(caps.CapType.mut_type("Int").to_lean()).to_equal("CapType.mk \"Int\" RefCapability.Exclusive")
expect(caps.CapType.iso_type("Int").to_lean()).to_equal("CapType.mk \"Int\" RefCapability.Isolated")
```

</details>

#### RefEnv

#### stores and consumes references

1. var env = caps RefEnv new
2. env add
   - Expected: env.is_available("x") is true
   - Expected: env.is_available("x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = caps.RefEnv.new()
env.add("x", caps.CapType.imm_type("Int"))

expect(env.is_available("x")).to_equal(true)
val _ = env.consume("x")
expect(env.is_available("x")).to_equal(false)
```

</details>

#### returns the stored reference

1. var env = caps RefEnv new
2. env add
   - Expected: env.get("y").? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var env = caps.RefEnv.new()
env.add("y", caps.CapType.iso_type("Nat"))
expect(env.get("y").?).to_equal(true)
```

</details>

#### Conversion rules

#### accepts the documented capability transitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(caps.can_convert(caps.RefCapability.Mut, caps.RefCapability.Mut)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Mut, caps.RefCapability.Imm)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Iso, caps.RefCapability.Mut)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Iso, caps.RefCapability.Imm)).to_equal(true)
expect(caps.can_convert(caps.RefCapability.Imm, caps.RefCapability.Mut)).to_equal(false)
expect(caps.can_convert(caps.RefCapability.Imm, caps.RefCapability.Iso)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/memory_capabilities_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Memory Capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
