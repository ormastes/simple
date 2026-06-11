# Ffi Signature Specification

> 1. var m = FfiManifest create

<!-- sdn-diagram:id=ffi_signature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffi_signature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffi_signature_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffi_signature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Signature Specification

## Scenarios

### FfiManifest

#### starts empty

1. var m = FfiManifest create
   - Expected: m.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = FfiManifest.create()
expect(m.count()).to_equal(0)
```

</details>

#### adds entries

1. var m = FfiManifest create
2. m add
3. m add
   - Expected: m.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = FfiManifest.create()
m.add("T32_Init", 0, "i32")
m.add("T32_Config", 2, "i32")
expect(m.count()).to_equal(2)
```

</details>

#### retrieves by name

1. var m = FfiManifest create
2. m add
   - Expected: sig.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = FfiManifest.create()
m.add("T32_Ping", 0, "i32")
val sig = m.get("T32_Ping")
expect(sig.?).to_equal(true)
```

</details>

#### returns nil for unknown name

1. var m = FfiManifest create
2. m add
   - Expected: sig.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = FfiManifest.create()
m.add("T32_Ping", 0, "i32")
val sig = m.get("T32_NonExistent")
expect(sig.?).to_equal(false)
```

</details>

#### lists all names

1. var m = FfiManifest create
2. m add
3. m add
4. m add
   - Expected: names.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = FfiManifest.create()
m.add("A", 0, "i32")
m.add("B", 1, "i32")
m.add("C", 2, "i32")
val names = m.names()
expect(names.len()).to_equal(3)
```

</details>

### validation_summary

#### formats summary correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = FfiValidationResult(
    total: 10,
    found: 7,
    missing: ["A", "B", "C"],
    present: ["D", "E", "F", "G", "H", "I", "J"]
)
val summary = validation_summary(result)
expect(summary.contains("7/10")).to_equal(true)
expect(summary.contains("3 missing")).to_equal(true)
```

</details>

#### formats perfect result

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = FfiValidationResult(
    total: 5,
    found: 5,
    missing: [],
    present: ["A", "B", "C", "D", "E"]
)
val summary = validation_summary(result)
expect(summary.contains("5/5")).to_equal(true)
expect(summary.contains("0 missing")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ffi/ffi_signature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FfiManifest
- validation_summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
