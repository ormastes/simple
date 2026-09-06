# Libc Stdio Specification

> Tests covering FileBuf buffered stdio model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Libc Stdio Specification

## Scenarios

### FileBuf buffered stdio model

#### fbuf_open creates empty buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = fbuf_open([], "r")
expect(fbuf_len(f)).to_equal(0i64)
expect(fbuf_eof(f)).to_equal(true)
```

</details>

#### fbuf_write appends bytes and returns new buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = fbuf_open([], "w")
val hello = "hello".bytes()
val f2 = fbuf_write(f, hello)
expect(fbuf_len(f2)).to_equal(5i64)
expect(fbuf_eof(f2)).to_equal(false)
```

</details>

#### fbuf_write+flush round-trips bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = fbuf_open([], "w")
val data = [72i64, 105i64]
val f2 = fbuf_write(f, data)
val flushed = fbuf_flush(f2)
expect(flushed.len()).to_equal(2i64)
expect(flushed[0i64]).to_equal(72i64)
expect(flushed[1i64]).to_equal(105i64)
```

</details>

#### fbuf_read returns first n bytes from pos

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [65i64, 66i64, 67i64, 68i64]
val f = fbuf_open(initial, "r")
val bytes2 = fbuf_read(f, 2i64)
expect(bytes2.len()).to_equal(2i64)
expect(bytes2[0i64]).to_equal(65i64)
expect(bytes2[1i64]).to_equal(66i64)
```

</details>

#### fbuf_read respects pos offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [65i64, 66i64, 67i64, 68i64]
val f = fbuf_open(initial, "r")
val f2 = fbuf_read_advance(f, 2i64)
val bytes2 = fbuf_read(f2, 2i64)
expect(bytes2[0i64]).to_equal(67i64)
expect(bytes2[1i64]).to_equal(68i64)
```

</details>

#### fbuf_read_advance then read continues from new pos

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [49i64, 50i64, 51i64, 52i64]
val f = fbuf_open(initial, "r")
val f2 = fbuf_read_advance(f, 1i64)
val f3 = fbuf_read_advance(f2, 1i64)
val bytes = fbuf_read(f3, 2i64)
expect(bytes.len()).to_equal(2i64)
expect(bytes[0i64]).to_equal(51i64)
expect(bytes[1i64]).to_equal(52i64)
```

</details>

#### fbuf_gets returns bytes up to and including newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [72i64, 105i64, 10i64]
val f = fbuf_open(initial, "r")
val line = fbuf_gets(f)
expect(line.len()).to_equal(3i64)
expect(line[0i64]).to_equal(72i64)
expect(line[1i64]).to_equal(105i64)
expect(line[2i64]).to_equal(10i64)
```

</details>

#### fbuf_gets without newline returns to end

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [72i64, 105i64]
val f = fbuf_open(initial, "r")
val line = fbuf_gets(f)
expect(line.len()).to_equal(2i64)
expect(line[0i64]).to_equal(72i64)
expect(line[1i64]).to_equal(105i64)
```

</details>

#### fbuf_gets from offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [65i64, 10i64, 66i64, 10i64]
val f = fbuf_open(initial, "r")
val f2 = fbuf_read_advance(f, 2i64)
val line = fbuf_gets(f2)
expect(line.len()).to_equal(2i64)
expect(line[0i64]).to_equal(66i64)
expect(line[1i64]).to_equal(10i64)
```

</details>

#### fbuf_eof is true after reading all

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [88i64]
val f = fbuf_open(initial, "r")
val f2 = fbuf_read_advance(f, 1i64)
expect(fbuf_eof(f2)).to_equal(true)
```

</details>

#### fbuf_eof is false while data remains

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [88i64, 89i64]
val f = fbuf_open(initial, "r")
expect(fbuf_eof(f)).to_equal(false)
val f2 = fbuf_read_advance(f, 1i64)
expect(fbuf_eof(f2)).to_equal(false)
```

</details>

#### fbuf_len returns data length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [1i64, 2i64, 3i64]
val f = fbuf_open(initial, "r")
expect(fbuf_len(f)).to_equal(3i64)
val f2 = fbuf_write(f, [4i64])
expect(fbuf_len(f2)).to_equal(4i64)
```

</details>

#### fbuf_read does not mutate original buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = [1i64, 2i64, 3i64]
val f = fbuf_open(initial, "r")
val _ = fbuf_read(f, 2i64)
expect(fbuf_eof(f)).to_equal(false)
expect(fbuf_len(f)).to_equal(3i64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_stdio_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FileBuf buffered stdio model.
- FileBuf buffered stdio model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `278edbe8bca6cbd2bb73c2a992d168f65f3ff11bf1c07f8c98cd981f533ae0e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `278edbe8bca6cbd2bb73c2a992d168f65f3ff11bf1c07f8c98cd981f533ae0e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `278edbe8bca6cbd2bb73c2a992d168f65f3ff11bf1c07f8c98cd981f533ae0e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/libc/libc_stdio_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_stdio_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=60 oracle=100
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/01_unit/os/libc/libc_stdio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_stdio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/libc/libc_stdio_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/libc/libc_stdio_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/libc/libc_stdio_spec.spl:11:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'fbuf_open creates empty buffer' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdio_spec.spl:16:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'fbuf_write appends bytes and returns new buffer' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdio_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'fbuf_write+flush round-trips bytes' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdio_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'fbuf_read returns first n bytes from pos' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
