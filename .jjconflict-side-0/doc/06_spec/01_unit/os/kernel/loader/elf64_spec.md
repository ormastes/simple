# ELF64 parser

> Verifies magic validation and header parsing of the minimal ELF64 loader.

<!-- sdn-diagram:id=elf64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elf64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elf64_spec -> std
elf64_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elf64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ELF64 parser

Verifies magic validation and header parsing of the minimal ELF64 loader.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10 |
| Category | Kernel loader |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/elf64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies magic validation and header parsing of the minimal ELF64 loader.

## Scenarios

### elf64_parse_header
_Header validation corner cases._

#### rejects a truncated buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = elf64_parse_header(_truncated())
expect h.is_nil().to_equal(true)
```

</details>

#### rejects a buffer with non-ELF magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = elf64_parse_header(_bad_magic())
expect h.is_nil().to_equal(true)
```

</details>

#### exposes the ELF64 magic bytes as expected constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ELF64_MAGIC_0.to_equal(0x7Fu8)
expect ELF64_MAGIC_1.to_equal(0x45u8)
expect ELF64_MAGIC_2.to_equal(0x4Cu8)
expect ELF64_MAGIC_3.to_equal(0x46u8)
```

</details>

#### EHDR size is the canonical 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect ELF64_EHDR_SIZE.to_equal(64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
