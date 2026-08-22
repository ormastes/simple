# libc_stdio_spec

> Verifies the libc stdio behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# libc_stdio_spec

Verifies the libc stdio behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_stdio_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the libc stdio behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### FileBuf buffered stdio model

#### fbuf_open creates empty buffer

- Verify: fbuf_open creates empty buffer
   - Expected: fbuf_len(f) equals `0i64`
   - Expected: fbuf_eof(f) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_open creates empty buffer")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val f = fbuf_open([], "r")
expect(fbuf_len(f)).to_equal(0i64)
expect(fbuf_eof(f)).to_equal(true)
```

</details>

#### fbuf_write appends bytes and returns new buffer

- Verify: fbuf_write appends bytes and returns new buffer
   - Expected: fbuf_len(f2) equals `5i64`
   - Expected: fbuf_eof(f2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_write appends bytes and returns new buffer")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val f = fbuf_open([], "w")
val hello = "hello".bytes()
val f2 = fbuf_write(f, hello)
expect(fbuf_len(f2)).to_equal(5i64)
expect(fbuf_eof(f2)).to_equal(false)
```

</details>

#### fbuf_write+flush round-trips bytes

- Verify: fbuf_write+flush round-trips bytes
   - Expected: flushed.len() equals `2i64`
   - Expected: flushed[0i64] equals `72i64`
   - Expected: flushed[1i64] equals `105i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_write+flush round-trips bytes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: fbuf_read returns first n bytes from pos
   - Expected: bytes2.len() equals `2i64`
   - Expected: bytes2[0i64] equals `65i64`
   - Expected: bytes2[1i64] equals `66i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_read returns first n bytes from pos")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val initial = [65i64, 66i64, 67i64, 68i64]
val f = fbuf_open(initial, "r")
val bytes2 = fbuf_read(f, 2i64)
expect(bytes2.len()).to_equal(2i64)
expect(bytes2[0i64]).to_equal(65i64)
expect(bytes2[1i64]).to_equal(66i64)
```

</details>

#### fbuf_read respects pos offset

- Verify: fbuf_read respects pos offset
   - Expected: bytes2[0i64] equals `67i64`
   - Expected: bytes2[1i64] equals `68i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_read respects pos offset")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val initial = [65i64, 66i64, 67i64, 68i64]
val f = fbuf_open(initial, "r")
val f2 = fbuf_read_advance(f, 2i64)
val bytes2 = fbuf_read(f2, 2i64)
expect(bytes2[0i64]).to_equal(67i64)
expect(bytes2[1i64]).to_equal(68i64)
```

</details>

#### fbuf_read_advance then read continues from new pos

- Verify: fbuf_read_advance then read continues from new pos
   - Expected: bytes.len() equals `2i64`
   - Expected: bytes[0i64] equals `51i64`
   - Expected: bytes[1i64] equals `52i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_read_advance then read continues from new pos")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: fbuf_gets returns bytes up to and including newline
   - Expected: line.len() equals `3i64`
   - Expected: line[0i64] equals `72i64`
   - Expected: line[1i64] equals `105i64`
   - Expected: line[2i64] equals `10i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_gets returns bytes up to and including newline")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: fbuf_gets without newline returns to end
   - Expected: line.len() equals `2i64`
   - Expected: line[0i64] equals `72i64`
   - Expected: line[1i64] equals `105i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_gets without newline returns to end")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val initial = [72i64, 105i64]
val f = fbuf_open(initial, "r")
val line = fbuf_gets(f)
expect(line.len()).to_equal(2i64)
expect(line[0i64]).to_equal(72i64)
expect(line[1i64]).to_equal(105i64)
```

</details>

#### fbuf_gets from offset

- Verify: fbuf_gets from offset
   - Expected: line.len() equals `2i64`
   - Expected: line[0i64] equals `66i64`
   - Expected: line[1i64] equals `10i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_gets from offset")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: fbuf_eof is true after reading all
   - Expected: fbuf_eof(f2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_eof is true after reading all")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val initial = [88i64]
val f = fbuf_open(initial, "r")
val f2 = fbuf_read_advance(f, 1i64)
expect(fbuf_eof(f2)).to_equal(true)
```

</details>

#### fbuf_eof is false while data remains

- Verify: fbuf_eof is false while data remains
   - Expected: fbuf_eof(f) is false
   - Expected: fbuf_eof(f2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_eof is false while data remains")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val initial = [88i64, 89i64]
val f = fbuf_open(initial, "r")
expect(fbuf_eof(f)).to_equal(false)
val f2 = fbuf_read_advance(f, 1i64)
expect(fbuf_eof(f2)).to_equal(false)
```

</details>

#### fbuf_len returns data length

- Verify: fbuf_len returns data length
   - Expected: fbuf_len(f) equals `3i64`
   - Expected: fbuf_len(f2) equals `4i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_len returns data length")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val initial = [1i64, 2i64, 3i64]
val f = fbuf_open(initial, "r")
expect(fbuf_len(f)).to_equal(3i64)
val f2 = fbuf_write(f, [4i64])
expect(fbuf_len(f2)).to_equal(4i64)
```

</details>

#### fbuf_read does not mutate original buffer

- Verify: fbuf_read does not mutate original buffer
   - Expected: fbuf_eof(f) is false
   - Expected: fbuf_len(f) equals `3i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LIBC_LIBC_STDIO-001
step("Verify: fbuf_read does not mutate original buffer")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val initial = [1i64, 2i64, 3i64]
val f = fbuf_open(initial, "r")
val _ = fbuf_read(f, 2i64)
expect(fbuf_eof(f)).to_equal(false)
expect(fbuf_len(f)).to_equal(3i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd43e8221c7af155f4f22c6db7bf0e291ab3bf163bf8efe6f677bbee0b3b74d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd43e8221c7af155f4f22c6db7bf0e291ab3bf163bf8efe6f677bbee0b3b74d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd43e8221c7af155f4f22c6db7bf0e291ab3bf163bf8efe6f677bbee0b3b74d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/libc/libc_stdio_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_stdio_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/libc/libc_stdio_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/libc/libc_stdio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_stdio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
