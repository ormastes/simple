# Parser Specification

> 1. fn run

<!-- sdn-diagram:id=parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Specification

## Scenarios

### extract_number_before

#### extracts bytes from ASan leak line

1. fn run
   - Expected: result equals `128`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val line = "Direct leak of 128 byte(s) in 1 object(s) allocated from:"
    val result = extract_number_before(line, " byte(s)")
    expect(result).to_equal(128)
run()
```

</details>

#### extracts objects from ASan leak line

1. fn run
   - Expected: result equals `3`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val line = "Direct leak of 128 byte(s) in 3 object(s) allocated from:"
    val result = extract_number_before(line, " object(s)")
    expect(result).to_equal(3)
run()
```

</details>

#### returns 0 when keyword not found

1. fn run
   - Expected: result equals `0`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val result = extract_number_before("no match here", " byte(s)")
    expect(result).to_equal(0)
run()
```

</details>

### extract_number_after

#### extracts number after keyword

1. fn run
   - Expected: result equals `256`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val line = "definitely lost: 256 bytes in 2 blocks"
    val result = extract_number_after(line, "definitely lost:")
    expect(result).to_equal(256)
run()
```

</details>

#### handles comma-separated numbers

1. fn run
   - Expected: result equals `1024`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val line = "definitely lost: 1,024 bytes in 2 blocks"
    val result = extract_number_after(line, "definitely lost:")
    expect(result).to_equal(1024)
run()
```

</details>

#### returns 0 when keyword not found

1. fn run
   - Expected: result equals `0`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val result = extract_number_after("no match", "missing:")
    expect(result).to_equal(0)
run()
```

</details>

### strip_valgrind_prefix

#### strips ==PID== prefix

1. fn run
   - Expected: result equals `LEAK SUMMARY:`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val line = "==12345== LEAK SUMMARY:"
    val result = strip_valgrind_prefix(line)
    expect(result).to_equal("LEAK SUMMARY:")
run()
```

</details>

#### leaves non-valgrind lines unchanged

1. fn run
   - Expected: result equals `normal line`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val line = "normal line"
    val result = strip_valgrind_prefix(line)
    expect(result).to_equal("normal line")
run()
```

</details>

### parse_asan_output

#### returns empty report for clean output

1. fn run
   - Expected: report.definitely_lost_bytes equals `0`
   - Expected: report.leaks.len() equals `0`
   - Expected: report.tool equals `asan`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val output = "program output\nno leaks here"
    val report = parse_asan_output(output)
    expect(report.definitely_lost_bytes).to_equal(0)
    expect(report.leaks.len()).to_equal(0)
    expect(report.tool).to_equal("asan")
run()
```

</details>

#### parses a single direct leak without double-counting

1. fn run
   - Expected: report.leaks.len() equals `1`
   - Expected: report.definitely_lost_bytes equals `64`
   - Expected: report.leaks[0].category equals `definitely_lost`
   - Expected: report.leaks[0].bytes equals `64`
   - Expected: report.leaks[0].stack_frames.len() equals `2`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val output = "Direct leak of 64 byte(s) in 1 object(s) allocated from:\n    #0 0xABCD in malloc\n    #1 0x1234 in main test.c:10\n\nSUMMARY: AddressSanitizer: 64 byte(s) leaked in 1 allocation(s)."
    val report = parse_asan_output(output)
    expect(report.leaks.len()).to_equal(1)
    expect(report.definitely_lost_bytes).to_equal(64)
    expect(report.leaks[0].category).to_equal("definitely_lost")
    expect(report.leaks[0].bytes).to_equal(64)
    expect(report.leaks[0].stack_frames.len()).to_equal(2)
run()
```

</details>

### parse_valgrind_output

#### parses LEAK SUMMARY section

1. fn run
   - Expected: report.tool equals `valgrind`
   - Expected: report.definitely_lost_bytes equals `128`
   - Expected: report.possibly_lost_bytes equals `64`
   - Expected: report.still_reachable_bytes equals `32`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val output = "==1234== LEAK SUMMARY:\n==1234==    definitely lost: 128 bytes in 2 blocks\n==1234==    indirectly lost: 0 bytes in 0 blocks\n==1234==    possibly lost: 64 bytes in 1 blocks\n==1234==    still reachable: 32 bytes in 1 blocks\n==1234== "
    val report = parse_valgrind_output(output)
    expect(report.tool).to_equal("valgrind")
    expect(report.definitely_lost_bytes).to_equal(128)
    expect(report.possibly_lost_bytes).to_equal(64)
    expect(report.still_reachable_bytes).to_equal(32)
run()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/leak_check/parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- extract_number_before
- extract_number_after
- strip_valgrind_prefix
- parse_asan_output
- parse_valgrind_output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
