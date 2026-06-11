# Callconv Bridge Specification

> <details>

<!-- sdn-diagram:id=callconv_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=callconv_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

callconv_bridge_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=callconv_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Callconv Bridge Specification

## Scenarios

### callconv_bridge

### callconv_from_string

#### maps C to C convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_from_string("C")
expect(result).to_equal("C")
```

</details>

#### maps Fastcall to Fastcall convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_from_string("Fastcall")
expect(result).to_equal("Fastcall")
```

</details>

#### maps Stdcall to Stdcall convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_from_string("Stdcall")
expect(result).to_equal("Stdcall")
```

</details>

#### maps Vectorcall to Vectorcall convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_from_string("Vectorcall")
expect(result).to_equal("Vectorcall")
```

</details>

#### maps Naked to Naked convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_from_string("Naked")
expect(result).to_equal("Naked")
```

</details>

#### maps Interrupt to Interrupt convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_from_string("Interrupt")
expect(result).to_equal("Interrupt")
```

</details>

#### maps unknown string to Simple fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_from_string("UnknownABI")
expect(result).to_equal("Simple")
```

</details>

### callconv_resolve_from_flags

#### naked flag resolves to Naked when no explicit callconv

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_resolve_from_flags(true, false, false, "")
expect(result).to_equal("Naked")
```

</details>

#### interrupt flag resolves to Interrupt when no explicit callconv

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_resolve_from_flags(false, true, false, "")
expect(result).to_equal("Interrupt")
```

</details>

#### explicit callconv C overrides naked flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_resolve_from_flags(true, false, true, "C")
expect(result).to_equal("C")
```

</details>

#### explicit callconv Fastcall overrides interrupt flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_resolve_from_flags(false, true, true, "Fastcall")
expect(result).to_equal("Fastcall")
```

</details>

#### no flags resolves to Simple default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_resolve_from_flags(false, false, false, "")
expect(result).to_equal("Simple")
```

</details>

### callconv_needs_prologue

#### Naked convention does not need prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_needs_prologue("Naked")
expect(result).to_equal(false)
```

</details>

#### C convention needs prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_needs_prologue("C")
expect(result).to_equal(true)
```

</details>

#### Simple convention needs prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_needs_prologue("Simple")
expect(result).to_equal(true)
```

</details>

#### Interrupt convention needs prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_needs_prologue("Interrupt")
expect(result).to_equal(true)
```

</details>

### callconv_is_interrupt_compat

#### Interrupt convention is interrupt compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_is_interrupt_compat("Interrupt")
expect(result).to_equal(true)
```

</details>

#### Naked convention is interrupt compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_is_interrupt_compat("Naked")
expect(result).to_equal(true)
```

</details>

#### C convention is not interrupt compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_is_interrupt_compat("C")
expect(result).to_equal(false)
```

</details>

#### Simple convention is not interrupt compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_is_interrupt_compat("Simple")
expect(result).to_equal(false)
```

</details>

#### Fastcall convention is not interrupt compatible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = spec_callconv_is_interrupt_compat("Fastcall")
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/callconv_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- callconv_bridge
- callconv_from_string
- callconv_resolve_from_flags
- callconv_needs_prologue
- callconv_is_interrupt_compat

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
