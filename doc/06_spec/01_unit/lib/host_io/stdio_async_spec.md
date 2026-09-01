# Stdio Async Specification

> Tests covering host_io.stdio — sync write, host_io.stdio — async future shapes, host_io.stdio — subprocess stdin round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stdio Async Specification

## Scenarios

### host_io.stdio — sync write

#### write_async returns a ready HostFuture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- write_async returns a ready HostFuture
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("write_async returns a ready HostFuture")
val fut: HostFuture<()> = write_async("x")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### write_line_async returns a ready HostFuture

- write_line_async returns a ready HostFuture
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("write_line_async returns a ready HostFuture")
val fut: HostFuture<()> = write_line_async("test line")
expect(fut.is_ready()).to_equal(true)
```

</details>

### host_io.stdio — async future shapes

#### HostFuture.ready for text is immediately ready

- HostFuture.ready for text is immediately ready
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("HostFuture.ready for text is immediately ready")
val fut: HostFuture<text> = HostFuture.ready("sentinel")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_line_async function is importable

- read_line_async function is importable
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("read_line_async function is importable")
# Confirm the symbol resolves — we just check the write path
# which exercises the same import group.
val fut: HostFuture<()> = write_async("probe")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_char_async function is importable

- read_char_async function is importable
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("read_char_async function is importable")
val fut: HostFuture<text> = HostFuture.ready("c")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_bytes_async function is importable

- read_bytes_async function is importable
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("read_bytes_async function is importable")
val fut: HostFuture<text> = HostFuture.ready("abc")
expect(fut.is_ready()).to_equal(true)
```

</details>

### host_io.stdio — subprocess stdin round-trip

#### echo_stdin fixture echoes one line exactly

- echo_stdin fixture echoes one line exactly
   - Expected: out equals `hello world\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("echo_stdin fixture echoes one line exactly")
val out = run_cmd("printf 'hello world\\n' | bin/simple run test/fixtures/host_io/echo_stdin.spl")
expect(out).to_equal("hello world\n")
```

</details>

#### echo_stdin fixture echoes a line with spaces and digits

- echo_stdin fixture echoes a line with spaces and digits
   - Expected: out equals `foo bar 123\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("echo_stdin fixture echoes a line with spaces and digits")
val out = run_cmd("printf 'foo bar 123\\n' | bin/simple run test/fixtures/host_io/echo_stdin.spl")
expect(out).to_equal("foo bar 123\n")
```

</details>

#### echo_stdin fixture returns empty output on EOF

- echo_stdin fixture returns empty output on EOF
   - Expected: out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("echo_stdin fixture returns empty output on EOF")
val out = run_cmd("printf '' | bin/simple run test/fixtures/host_io/echo_stdin.spl")
expect(out).to_equal("")
```

</details>

#### echo_stdin fixture exits 0 on normal completion

- echo_stdin fixture exits 0 on normal completion
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("echo_stdin fixture exits 0 on normal completion")
val code = run_cmd_exit("printf 'ok\\n' | bin/simple run test/fixtures/host_io/echo_stdin.spl")
expect(code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/host_io/stdio_async_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host_io.stdio — sync write, host_io.stdio — async future shapes, host_io.stdio — subprocess stdin round-trip.
- host_io.stdio — sync write
- host_io.stdio — async future shapes
- host_io.stdio — subprocess stdin round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d2c7e72a5e83a877859deb506a703e5a5b307979aa9efefed73dc5ece595ea9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2c7e72a5e83a877859deb506a703e5a5b307979aa9efefed73dc5ece595ea9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2c7e72a5e83a877859deb506a703e5a5b307979aa9efefed73dc5ece595ea9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/host_io/stdio_async_spec.spl
mirror: doc/06_spec/01_unit/lib/host_io/stdio_async_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/host_io/stdio_async_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/host_io/stdio_async_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/host_io/stdio_async_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/host_io/stdio_async_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'write_async returns a ready HostFuture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/host_io/stdio_async_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'write_line_async returns a ready HostFuture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/host_io/stdio_async_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HostFuture.ready for text is immediately ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
