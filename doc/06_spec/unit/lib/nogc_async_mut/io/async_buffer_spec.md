# Async Buffer Specification

> Tests covering AsyncBufferedReader, AsyncBufferedWriter, Async Buffer Composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Buffer Specification

## Scenarios

### AsyncBufferedReader

#### construction

#### documents default construction

- documents default construction


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents default construction")
# val raw = await AsyncFileHandle.read_file("data.csv")?
# val reader = AsyncBufferedReader.new(raw)
# expect reader.buf_size == 8192
pass
```

</details>

#### documents custom capacity

- documents custom capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents custom capacity")
# val raw = await AsyncFileHandle.read_file("data.csv")?
# val reader = AsyncBufferedReader.with_capacity(raw, 16384)
# expect reader.buf_size == 16384
pass
```

</details>

#### reading

#### documents read_text

- documents read_text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents read_text")
# val raw = await AsyncFileHandle.read_file("data.txt")?
# val reader = AsyncBufferedReader.new(raw)
# val content = await reader.read_text()?
pass
```

</details>

#### documents read_line

- documents read_line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents read_line")
# val raw = await AsyncFileHandle.read_file("data.csv")?
# val reader = AsyncBufferedReader.new(raw)
# val header = await reader.read_line()?
# val row1 = await reader.read_line()?
pass
```

</details>

#### documents read_all

- documents read_all


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents read_all")
# val raw = await AsyncFileHandle.read_file("data.bin")?
# val reader = AsyncBufferedReader.new(raw)
# val data = await reader.read_all()?
pass
```

</details>

#### close

#### documents async close

- documents async close


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents async close")
# val raw = await AsyncFileHandle.read_file("data.txt")?
# val reader = AsyncBufferedReader.new(raw)
# await reader.close()?
pass
```

</details>

### AsyncBufferedWriter

#### construction

#### documents default construction

- documents default construction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents default construction")
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.new(raw)
pass
```

</details>

#### documents custom capacity

- documents custom capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents custom capacity")
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.with_capacity(raw, 32768)
pass
```

</details>

#### writing

#### documents buffered write + flush

- documents buffered write + flush


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents buffered write + flush")
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.new(raw)
# await writer.write_text("line 1\\n")?
# await writer.write_text("line 2\\n")?
# await writer.flush()?
pass
```

</details>

#### close flushes

#### documents close auto-flush

- documents close auto-flush


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents close auto-flush")
# val raw = await AsyncFileHandle.create("output.log")?
# val writer = AsyncBufferedWriter.new(raw)
# await writer.write_text("auto-flushed\\n")?
# await writer.close()?  # flushes then closes inner
pass
```

</details>

### Async Buffer Composition

#### wrapping AsyncFileHandle

#### documents file buffering

- documents file buffering


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents file buffering")
# val fh = await AsyncFileHandle.read_file("big.csv")?
# val reader = AsyncBufferedReader.new(fh)
# while true:
#     val line = await reader.read_line()?
#     if line.is_empty(): break
#     process(line)
pass
```

</details>

#### wrapping AsyncTcpStream

#### documents network buffering

- documents network buffering


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents network buffering")
# val stream = await AsyncTcpStream.connect("127.0.0.1:8080")?
# val reader = AsyncBufferedReader.new(stream)
# val header = await reader.read_line()?
pass
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/io/async_buffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AsyncBufferedReader, AsyncBufferedWriter, Async Buffer Composition.
- AsyncBufferedReader
- AsyncBufferedWriter
- Async Buffer Composition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22da624be9a6b638ca2685cf3b8fa4d8fffe19ef432cf80b35cd6e0163e16f1d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22da624be9a6b638ca2685cf3b8fa4d8fffe19ef432cf80b35cd6e0163e16f1d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22da624be9a6b638ca2685cf3b8fa4d8fffe19ef432cf80b35cd6e0163e16f1d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/nogc_async_mut/io/async_buffer_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/io/async_buffer_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/lib/nogc_async_mut/io/async_buffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/io/async_buffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/io/async_buffer_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/lib/nogc_async_mut/io/async_buffer_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents default construction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/io/async_buffer_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents custom capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/io/async_buffer_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents read_text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
