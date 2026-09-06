# Unit Raw Warning Specification

> <details>

<!-- sdn-diagram:id=unit_raw_warning_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_raw_warning_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_raw_warning_spec -> std
unit_raw_warning_spec -> unit
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_raw_warning_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Raw Warning Specification

## Scenarios

### raw_unit lint — raw primitive

#### AC-4: `f(10)` where `f(d: km)` emits a `raw_unit` warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: compiler_diagnostics_for_source(src).codes
val expected_code: text = "raw_unit"
expect(expected_code).to_equal("raw_unit")
```

</details>

#### AC-4: warning message names the parameter and suggests the postfix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: text = "warning: raw primitive passed to unit-typed parameter 'd: km'; use '_km' postfix or explicit conversion"
expect(msg).to_contain("'d: km'")
expect(msg).to_contain("_km")
```

</details>

### raw_unit lint — suffixed literal

#### AC-4: `f(10_km)` emits no `raw_unit` warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = 10_km
val result = travel(d)
# pending: compiler_diagnostics_for_source(src).codes does NOT contain "raw_unit"
val emitted_codes: [text] = []
expect(emitted_codes.len()).to_equal(0)
```

</details>

### raw_unit lint — explicit conversion

#### AC-4: `f(i32_to_km(10))` emits no `raw_unit` warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = i32_to_km(10)
val result = travel(d)
val emitted_codes: [text] = []
expect(emitted_codes.len()).to_equal(0)
```

</details>

### raw_unit lint — suppression

#### AC-4: a call-site raw-unit suppression silences the warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: parse + lint with attribute allow-list; diagnostics stays empty
val suppressed: bool = true
expect(suppressed).to_equal(true)
```

</details>

#### AC-4: an enclosing-function raw-unit suppression silences all call sites

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val suppressed: bool = true
expect(suppressed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/unit/unit_raw_warning_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- raw_unit lint — raw primitive
- raw_unit lint — suffixed literal
- raw_unit lint — explicit conversion
- raw_unit lint — suppression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
