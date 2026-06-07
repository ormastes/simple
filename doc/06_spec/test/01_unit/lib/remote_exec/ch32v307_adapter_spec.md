# CH32V307 Adapter Host-Side Specification

> <details>

<!-- sdn-diagram:id=ch32v307_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ch32v307_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ch32v307_adapter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ch32v307_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CH32V307 Adapter Host-Side Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/remote_exec/ch32v307_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Ch32V307Adapter helpers

#### maps PC to the CH32 DPC register id

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ch32v307_register_id(32)).to_equal(0x7B1)
```

</details>

#### keeps general purpose registers mapped by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ch32v307_register_id(10)).to_equal(10)
expect(ch32v307_register_id(2)).to_equal(2)
```

</details>

#### parses dpc pc values from regs output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = parse_ch32v307_register_value(SAMPLE_REGS, 32)
expect(value).to_equal(0x2000011A)
```

</details>

#### parses general register values from regs output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = parse_ch32v307_register_value(SAMPLE_REGS, 10)
expect(value).to_equal(0x2A)
```

</details>

#### returns -1 when a register is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = parse_ch32v307_register_value(SAMPLE_REGS, 31)
expect(value).to_equal(-1)
```

</details>

#### parses byte dumps in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = parse_ch32v307_dump_bytes(SAMPLE_DUMP, 8)
expect(bytes.len()).to_equal(8)
expect(bytes[0]).to_equal(0xB7)
expect(bytes[3]).to_equal(0x08)
expect(bytes[7]).to_equal(0x00)
```

</details>

#### truncates dump parsing to the requested size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = parse_ch32v307_dump_bytes(SAMPLE_DUMP, 5)
expect(bytes.len()).to_equal(5)
expect(bytes[4]).to_equal(0x67)
```

</details>

#### removes ANSI escape sequences from output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cleaned = strip_ansi_escape("\u001b[31merror\u001b[0m")
expect(cleaned).to_equal("error")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
