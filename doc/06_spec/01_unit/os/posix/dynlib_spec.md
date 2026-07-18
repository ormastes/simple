# DynLibKind OOP Interface Specification

> Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE

<!-- sdn-diagram:id=dynlib_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynlib_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynlib_spec -> std
dynlib_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynlib_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DynLibKind OOP Interface Specification

Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/posix/dynlib_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the unified DynLibKind enum dispatch layer over ELF, SMF, and PE
dynamic library formats, including validity checks, format naming, path
extraction, and error handling for Invalid variants.

## Scenarios

### DynLibKind.Elf

#### reports valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Elf(state: ElfLibState(
    handle: 1,
    base: 0,
    path: "/lib/libtest.so"
))
expect(dynlib_is_valid(lib)).to_equal(true)
```

</details>

#### returns correct format name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Elf(state: ElfLibState(
    handle: 1,
    base: 0,
    path: "/lib/libtest.so"
))
expect(dynlib_format_name(lib)).to_equal("ELF")
```

</details>

#### returns correct path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Elf(state: ElfLibState(
    handle: 1,
    base: 0,
    path: "/lib/libtest.so"
))
expect(dynlib_path(lib)).to_equal("/lib/libtest.so")
```

</details>

### DynLibKind.Smf

#### reports valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Smf(state: SmfLibState(
    handle: 2,
    path: "/lib/plugin.smf",
    stub_entry: 0
))
expect(dynlib_is_valid(lib)).to_equal(true)
```

</details>

#### returns correct format name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Smf(state: SmfLibState(
    handle: 2,
    path: "/lib/plugin.smf",
    stub_entry: 0
))
expect(dynlib_format_name(lib)).to_equal("SMF")
```

</details>

#### returns correct path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Smf(state: SmfLibState(
    handle: 2,
    path: "/lib/plugin.smf",
    stub_entry: 0
))
expect(dynlib_path(lib)).to_equal("/lib/plugin.smf")
```

</details>

### DynLibKind.Pe

#### reports valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Pe(state: PeLibState(
    handle: 3,
    path: "kernel32.dll",
    base: 0,
    image_size: 0
))
expect(dynlib_is_valid(lib)).to_equal(true)
```

</details>

#### returns correct format name

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Pe(state: PeLibState(
    handle: 3,
    path: "kernel32.dll",
    base: 0,
    image_size: 0
))
expect(dynlib_format_name(lib)).to_equal("PE")
```

</details>

#### returns correct path

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Pe(state: PeLibState(
    handle: 3,
    path: "kernel32.dll",
    base: 0,
    image_size: 0
))
expect(dynlib_path(lib)).to_equal("kernel32.dll")
```

</details>

### DynLibKind.Invalid

#### reports not valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Invalid
expect(dynlib_is_valid(lib)).to_equal(false)
```

</details>

#### returns empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Invalid
expect(dynlib_path(lib)).to_equal("")
```

</details>

#### returns Invalid format name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Invalid
expect(dynlib_format_name(lib)).to_equal("Invalid")
```

</details>

#### dynlib_symbol returns negative for Invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Invalid
val result = dynlib_symbol(lib, "anything")
expect(result < 0).to_equal(true)
```

</details>

#### dynlib_symbol_is_process_callable returns false for Invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Invalid
expect(dynlib_symbol_is_process_callable(lib, "anything")).to_equal(false)
```

</details>

#### dynlib_close returns negative for Invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = DynLibKind.Invalid
val result = dynlib_close(lib)
expect(result < 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
