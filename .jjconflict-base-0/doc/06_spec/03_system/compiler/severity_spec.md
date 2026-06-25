# Severity Specification

> <details>

<!-- sdn-diagram:id=severity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=severity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

severity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=severity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Severity Specification

## Scenarios

### Diagnostic Severity Levels

#### gets severity name for Error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = Severity.Error
val name = error.name()
expect(name).to_equal("error")
```

</details>

#### gets severity color for Error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = Severity.Error
val color = error.color()
expect(color).to_equal("\x1b[1;31m")
```

</details>

#### gets severity color for Warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warning = Severity.Warning
val color = warning.color()
expect(color).to_equal("\x1b[1;33m")
```

</details>

#### gets severity color for Note

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val note = Severity.Note
val color = note.color()
expect(color).to_equal("\x1b[1;36m")
```

</details>

#### gets severity color for Help

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = Severity.Help
val color = help.color()
expect(color).to_equal("\x1b[1;32m")
```

</details>

#### gets severity color for Info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = Severity.Info
val color = info.color()
expect(color).to_equal("\x1b[1;34m")
```

</details>

#### gets reset color code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = Severity.reset_color()
expect(reset).to_equal("\x1b[0m")
```

</details>

#### formats colored severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warning = Severity.Warning
val colored = warning.colored()
expect(colored).to_equal("\x1b[1;33mwarning\x1b[0m")
```

</details>

#### checks if Error is an error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = Severity.Error
val result = error.is_error()
expect(result).to_equal(true)
```

</details>

#### checks if Warning is not an error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warning = Severity.Warning
val result = warning.is_error()
expect(result).to_equal(false)
```

</details>

#### checks if Warning is a warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warning = Severity.Warning
val result = warning.is_warning()
expect(result).to_equal(true)
```

</details>

#### checks if Error blocks compilation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = Severity.Error
val blocks = error.blocks_compilation()
expect(blocks).to_equal(true)
```

</details>

#### checks if Warning does not block compilation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warning = Severity.Warning
val blocks = warning.blocks_compilation()
expect(blocks).to_equal(false)
```

</details>

#### gets severity order for Error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = Severity.Error
val order = error.order()
expect(order).to_equal(0)
```

</details>

#### gets severity order for Warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warning = Severity.Warning
val order = warning.order()
expect(order).to_equal(1)
```

</details>

#### gets severity order for Info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = Severity.Info
val order = info.order()
expect(order).to_equal(4)
```

</details>

#### parses error string to severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "error"
val result = Severity.from_name(name)
expect(result.is_some()).to_equal(true)
val parsed = result.unwrap()
expect(parsed.is_error()).to_equal(true)
```

</details>

#### parses warning string to severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "warning"
val result = Severity.from_name(name)
expect(result.is_some()).to_equal(true)
val parsed = result.unwrap()
expect(parsed.is_warning()).to_equal(true)
```

</details>

#### parses invalid string to severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "invalid"
val result = Severity.from_name(name)
expect(result.is_none()).to_equal(true)
```

</details>

#### gets all severity levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = Severity.all()
expect(all.length()).to_equal(5)
expect(all[0].is_error()).to_equal(true)
expect(all[1].is_warning()).to_equal(true)
```

</details>

#### severity ordering for sorting

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = Severity.Error
val warning = Severity.Warning
val info = Severity.Info
expect(error.order() < warning.order()).to_equal(true)
expect(warning.order() < info.order()).to_equal(true)
```

</details>

#### all names are unique

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = Severity.all()
val names = [for s in all: s.name()]
expect(names.length()).to_equal(5)
expect(names.filter(_1 == "error").length()).to_equal(1)
expect(names.filter(_1 == "warning").length()).to_equal(1)
expect(names.filter(_1 == "note").length()).to_equal(1)
expect(names.filter(_1 == "help").length()).to_equal(1)
expect(names.filter(_1 == "info").length()).to_equal(1)
```

</details>

#### parse round-trip for all severities

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = Severity.all()
for severity in all:
    val name = severity.name()
    val parsed = Severity.from_name(name)
    expect(parsed.is_some()).to_equal(true)
    val round_trip = parsed.unwrap()
    expect(round_trip.name()).to_equal(name)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/severity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Diagnostic Severity Levels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
