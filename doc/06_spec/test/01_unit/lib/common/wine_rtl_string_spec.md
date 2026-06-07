# Wine Rtl String Specification

> <details>

<!-- sdn-diagram:id=wine_rtl_string_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_rtl_string_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_rtl_string_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_rtl_string_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Rtl String Specification

## Scenarios

### Wine RTL string bridge

#### lists the modeled RTL string calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = wine_rtl_string_required_calls()
expect(calls.len()).to_equal(3)
expect(calls[0]).to_equal("RtlInitUnicodeString")
expect(calls[2]).to_equal("RtlFreeAnsiString")
```

</details>

#### initializes and converts bounded Unicode strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initialized = wine_rtl_init_unicode_string("C:\\hello.exe")
val converted = wine_rtl_unicode_string_to_ansi_string(initialized.unicode, true)
val freed = wine_rtl_free_ansi_string(converted.ansi)

expect(initialized.ok).to_equal(true)
expect(initialized.unicode.length_bytes).to_equal(24)
expect(initialized.unicode.maximum_length_bytes).to_equal(26)
expect(converted.ok).to_equal(true)
expect(converted.ansi.buffer).to_equal("C:\\hello.exe")
expect(converted.ansi.length_bytes).to_equal(12)
expect(freed.ok).to_equal(true)
expect(freed.ansi.allocated).to_equal(false)
```

</details>

#### executes only the bounded RTL string sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_rtl_execute_string(
    ["RtlInitUnicodeString", "RtlUnicodeStringToAnsiString", "RtlFreeAnsiString"],
    "C:\\hello.exe"
)

expect(result.ok).to_equal(true)
expect(result.unicode.buffer).to_equal("C:\\hello.exe")
expect(result.ansi.allocated).to_equal(false)
expect(result.operations).to_equal("RtlInitUnicodeString RtlUnicodeStringToAnsiString RtlFreeAnsiString")

val out_of_order = wine_rtl_execute_string(
    ["RtlUnicodeStringToAnsiString", "RtlInitUnicodeString", "RtlFreeAnsiString"],
    "C:\\hello.exe"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("rtl-string-sequence-expected:RtlInitUnicodeString")

val wrong_family = wine_rtl_execute_string(
    ["RtlInitUnicodeString", "RtlUnicodeStringToAnsiString", "RtlFreeHeap"],
    "C:\\hello.exe"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:RtlFreeHeap")
```

</details>

#### rejects conversion and free calls with invalid destination state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initialized = wine_rtl_init_unicode_string("C:\\hello.exe")
val not_allocated = wine_rtl_unicode_string_to_ansi_string(initialized.unicode, false)
val freed = wine_rtl_free_ansi_string(not_allocated.ansi)

expect(not_allocated.ok).to_equal(false)
expect(not_allocated.error).to_equal("RtlUnicodeStringToAnsiString:destination-not-allocated")
expect(freed.ok).to_equal(false)
expect(freed.error).to_equal("RtlFreeAnsiString:not-allocated")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_rtl_string_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine RTL string bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
