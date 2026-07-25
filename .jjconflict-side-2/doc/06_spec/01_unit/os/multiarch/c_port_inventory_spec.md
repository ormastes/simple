# C Port Inventory Specification

> <details>

<!-- sdn-diagram:id=c_port_inventory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=c_port_inventory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

c_port_inventory_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=c_port_inventory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Port Inventory Specification

## Scenarios

### AC-1 — C → Simple inventory artefact

#### inventory file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(INVENTORY_PATH)).to_equal(true)
```

</details>

#### inventory file is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(INVENTORY_PATH)
expect(body.length() > 0).to_equal(true)
```

</details>

#### inventory lists the runtime_minimal critical-path entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(INVENTORY_PATH)
expect(body.contains("runtime_minimal")).to_equal(true)
```

</details>

#### inventory lists simpleos_crt0 and simpleos_setjmp

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(INVENTORY_PATH)
expect(body.contains("simpleos_crt0")).to_equal(true)
expect(body.contains("simpleos_setjmp")).to_equal(true)
```

</details>

#### inventory documents the EXCLUDED vendor + bootstrap allow-list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(INVENTORY_PATH)
expect(body.contains("vendor")).to_equal(true)
```

</details>

### AC-2 — zero owned-code .c compiles for SimpleOS

#### owned-C compile report exists after a SimpleOS build

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(OWNED_C_REPORT)).to_equal(true)
```

</details>

#### owned-C report shows zero entries outside the allow-list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report: text = file_read(OWNED_C_REPORT)
expect(report.contains("\"violations\": []")).to_equal(true)
```

</details>

#### report explicitly names the documented allow-list paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report: text = file_read(OWNED_C_REPORT)
expect(report.contains("vendor")).to_equal(true)
expect(report.contains("miniaudio")).to_equal(true)
expect(report.contains("stb_image")).to_equal(true)
expect(report.contains("stb_truetype")).to_equal(true)
```

</details>

#### no new owned .c file appears outside the locked allow-list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report: text = file_read(OWNED_C_REPORT)
expect(report.contains("\"residual_c_count\": 0")).to_equal(true)
```

</details>

### AC-1/AC-2 cross-link to architecture doc

#### architecture doc references the inventory file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(ARCH_DOC_PATH)
expect(body.contains("c_to_simple_inventory")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/multiarch/c_port_inventory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-1 — C → Simple inventory artefact
- AC-2 — zero owned-code .c compiles for SimpleOS
- AC-1/AC-2 cross-link to architecture doc

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
