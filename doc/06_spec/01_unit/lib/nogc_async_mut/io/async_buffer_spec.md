# Async Buffer Specification

> Tests covering AsyncBufferedReader byte conversion, AsyncBufferedReader, AsyncBufferedWriter, Async Buffer Composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Buffer Specification

## Scenarios

### AsyncBufferedReader byte conversion

#### decodes text without text.from_bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes text without text.from_bytes
   - Expected: text_value equals `ok?`
   - Expected: err.message equals ``
   - Expected: "pending" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes text without text.from_bytes")
val raw = AsyncMemoryReader.new([111u8, 107u8, 255u8])
val reader = AsyncBufferedReader.with_capacity(raw, 2)
match reader.read_text().poll():
    Poll.Ready(result):
        match result:
            Ok(text_value):
                expect(text_value).to_equal("ok?")
            Err(err):
                expect(err.message).to_equal("")
    Poll.Pending:
        expect("pending").to_equal("")
```

</details>

#### preserves line controls while decoding buffered lines

- preserves line controls while decoding buffered lines
   - Expected: text_value equals `ok\n`
   - Expected: err.message equals ``
   - Expected: "pending" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves line controls while decoding buffered lines")
val raw = AsyncMemoryReader.new([111u8, 107u8, 10u8])
val reader = AsyncBufferedReader(inner: raw, buf: [111u8, 107u8, 10u8], buf_size: 4, pos: 0, filled: 3)
match reader.read_line().poll():
    Poll.Ready(result):
        match result:
            Ok(text_value):
                expect(text_value).to_equal("ok\n")
            Err(err):
                expect(err.message).to_equal("")
    Poll.Pending:
        expect("pending").to_equal("")
```

</details>

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
| Source | `test/01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AsyncBufferedReader byte conversion, AsyncBufferedReader, AsyncBufferedWriter, Async Buffer Composition.
- AsyncBufferedReader byte conversion
- AsyncBufferedReader
- AsyncBufferedWriter
- Async Buffer Composition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `9c255aae43313b7fe66b78fae5777631d40719309bb12a9c494a7532c93de155`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c255aae43313b7fe66b78fae5777631d40719309bb12a9c494a7532c93de155`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c255aae43313b7fe66b78fae5777631d40719309bb12a9c494a7532c93de155`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/io/async_buffer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/io/async_buffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/io/async_buffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes text without text.from_bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves line controls while decoding buffered lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents default construction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
