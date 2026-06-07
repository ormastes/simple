# Dtb Cpu Walker Specification

> 1. dtb scan init from bytes

<!-- sdn-diagram:id=dtb_cpu_walker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dtb_cpu_walker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dtb_cpu_walker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dtb_cpu_walker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dtb Cpu Walker Specification

## Scenarios

### DTB CPU Walker

### count_okay_cpus — valid FDT

#### AC-1: returns 1 for single hart with no status (defaults to okay)

1. dtb scan init from bytes
   - Expected: count equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [HartDesc(id: 0u32, status: "", isa: "rv64gc")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val count = cached_cpu_count()
expect(count).to_equal(1u32)
```

</details>

#### AC-1: returns 2 for two harts both status=okay

1. HartDesc
2. HartDesc
3. dtb scan init from bytes
   - Expected: count equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val count = cached_cpu_count()
expect(count).to_equal(2u32)
```

</details>

#### AC-1: returns 4 for four-hart SMP FDT

1. HartDesc
2. HartDesc
3. HartDesc
4. HartDesc
5. dtb scan init from bytes
   - Expected: cached_cpu_count() equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 2u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 3u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cpu_count()).to_equal(4u32)
```

</details>

### count_okay_cpus — status=disabled filter

#### AC-1: excludes hart with status=disabled

1. HartDesc
2. HartDesc
3. dtb scan init from bytes
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "disabled", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

#### AC-1: all disabled harts returns fallback of 1

1. HartDesc
2. HartDesc
3. dtb scan init from bytes
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDesc(id: 0u32, status: "disabled", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "disabled", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

### count_okay_cpus — missing or invalid DTB

#### AC-1: null FDT pointer returns fallback of 1

1. dtb scan init from bytes
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dtb_scan_init_from_bytes(make_fdt_null())
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

#### AC-1: bad magic returns fallback of 1

1. dtb scan init from bytes
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dtb_scan_init_from_bytes(make_fdt_bad_magic())
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

### cached_cbom_block_size — from DTB riscv,cbom-block-size property

#### AC-5: returns DTB-advertised block size when present

1. dtb scan init from bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc_zicbom")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val sz = cached_cbom_block_size()
expect(sz).to_be_greater_than(0u32)
```

</details>

#### AC-5: returns default 64 when DTB has no riscv,cbom-block-size

1. dtb scan init from bytes
   - Expected: cached_cbom_block_size() equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cbom_block_size()).to_equal(64u32)
```

</details>

### cached_isa_string — Zicbom substring detection

#### AC-3: isa string containing _zicbom signals Zicbom support

1. dtb scan init from bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc_zicbom_zicboz")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val isa = cached_isa_string(0u32)
expect(isa).to_contain("_zicbom")
```

</details>

#### AC-3: isa string without _zicbom correctly absent

1. dtb scan init from bytes
   - Expected: isa equals `rv64gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val isa = cached_isa_string(0u32)
expect(isa).to_equal("rv64gc")
```

</details>

### memoization — dtb_scan_init is idempotent

#### AC-1: second call with same blob does not change cached count

1. HartDesc
2. HartDesc
3. dtb scan init from bytes
4. dtb scan init from bytes
   - Expected: count_second equals `count_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val count_first = cached_cpu_count()
dtb_scan_init_from_bytes(fdt)
val count_second = cached_cpu_count()
expect(count_second).to_equal(count_first)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DTB CPU Walker
- count_okay_cpus — valid FDT
- count_okay_cpus — status=disabled filter
- count_okay_cpus — missing or invalid DTB
- cached_cbom_block_size — from DTB riscv,cbom-block-size property
- cached_isa_string — Zicbom substring detection
- memoization — dtb_scan_init is idempotent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
