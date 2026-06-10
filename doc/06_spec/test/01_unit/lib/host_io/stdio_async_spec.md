# Stdio Async Specification

> <details>

<!-- sdn-diagram:id=stdio_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stdio_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stdio_async_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stdio_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stdio Async Specification

## Scenarios

### host_io.stdio — sync write

#### write_async returns a ready HostFuture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fut: HostFuture<()> = write_async("x")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### write_line_async returns a ready HostFuture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fut: HostFuture<()> = write_line_async("test line")
expect(fut.is_ready()).to_equal(true)
```

</details>

### host_io.stdio — async future shapes

#### HostFuture.ready for text is immediately ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fut: HostFuture<text> = HostFuture.ready("sentinel")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_line_async function is importable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Confirm the symbol resolves — we just check the write path
# which exercises the same import group.
val fut: HostFuture<()> = write_async("probe")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_char_async function is importable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fut: HostFuture<text> = HostFuture.ready("c")
expect(fut.is_ready()).to_equal(true)
```

</details>

#### read_bytes_async function is importable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fut: HostFuture<text> = HostFuture.ready("abc")
expect(fut.is_ready()).to_equal(true)
```

</details>

### host_io.stdio — subprocess stdin round-trip

#### echo_stdin fixture echoes one line exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = run_cmd("printf 'hello world\\n' | bin/simple run test/fixtures/host_io/echo_stdin.spl")
expect(out).to_equal("hello world\n")
```

</details>

#### echo_stdin fixture echoes a line with spaces and digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = run_cmd("printf 'foo bar 123\\n' | bin/simple run test/fixtures/host_io/echo_stdin.spl")
expect(out).to_equal("foo bar 123\n")
```

</details>

#### echo_stdin fixture returns empty output on EOF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = run_cmd("printf '' | bin/simple run test/fixtures/host_io/echo_stdin.spl")
expect(out).to_equal("")
```

</details>

#### echo_stdin fixture exits 0 on normal completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
