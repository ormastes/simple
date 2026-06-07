# Reader Specification

> <details>

<!-- sdn-diagram:id=reader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reader_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reader Specification

## Scenarios

### SemihostReader

#### defines semihost transport, string table, and reader state

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/semihost/reader.spl")

expect(src).to_contain("enum FormatType:")
expect(src).to_contain("class StringInternEntry:")
expect(src).to_contain("class StringInternTable:")
expect(src).to_contain("static fn with_test_handles() -> StringInternTable:")
expect(src).to_contain("enum TransportType:")
expect(src).to_contain("struct Transport:")
expect(src).to_contain("class SemiHostReader:")
expect(src).to_contain("static fn new(smf_root: text, transport: Transport) -> SemiHostReader:")
```

</details>

#### defines frame parsing, formatting, and CLI entrypoint contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/semihost/reader.spl")
val init = rt_file_read_text("src/app/semihost/__init__.spl")

expect(src).to_contain("struct SemihostFrame:")
expect(src).to_contain("val PROTO_MAGIC = 0xAB")
expect(src).to_contain("val PROTO_VERSION = 0x01")
expect(src).to_contain("fn parse_serial_frame(buffer: [u8]) -> Result<(SemihostFrame, u32), text>:")
expect(src).to_contain("fn format_interned_string(fmt_str: text, types: [FormatType], params: [i64]) -> text:")
expect(src).to_contain("fn format_param(value: i64, fmt_type: FormatType) -> text:")
expect(src).to_contain("fn read_u32_le(data: [u8], offset: u32) -> u32:")
expect(src).to_contain("fn run_reader(args: [text]) -> i32:")
expect(src).to_contain("fn print_help():")
expect(init).to_contain("export run_reader, parse_serial_frame, format_interned_string")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/semihost/reader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SemihostReader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
