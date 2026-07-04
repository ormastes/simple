# Primitive API Types Spec — Canonical Wrapper Types

> Tests that the canonical wrapper types in `src/lib/common/types.spl` (existing and new ones added by Team W in Phase 0) can be constructed and have their inner value accessed.  Existing wrappers should pass today; new wrappers (ExitCode, Handle, ErrorCode, MemAddr, DurationMs) will FAIL until Team W extends types.spl.

<!-- sdn-diagram:id=primitive_api_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=primitive_api_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

primitive_api_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=primitive_api_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive API Types Spec — Canonical Wrapper Types

Tests that the canonical wrapper types in `src/lib/common/types.spl` (existing and new ones added by Team W in Phase 0) can be constructed and have their inner value accessed.  Existing wrappers should pass today; new wrappers (ExitCode, Handle, ErrorCode, MemAddr, DurationMs) will FAIL until Team W extends types.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-primitive-api-suppressions |
| Category | Tooling |
| Difficulty | 1/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/primitive_api_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the canonical wrapper types in `src/lib/common/types.spl` (existing
and new ones added by Team W in Phase 0) can be constructed and have their
inner value accessed.  Existing wrappers should pass today; new wrappers
(ExitCode, Handle, ErrorCode, MemAddr, DurationMs) will FAIL until Team W
extends types.spl.

## Scenarios

### canonical wrapper types — existing (types.spl)

#### AC-1: ActorId wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = ActorId(value: 42)
expect(id.value).to_equal(42)
```

</details>

#### AC-1: MessageId wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = MessageId(value: 7)
expect(id.value).to_equal(7)
```

</details>

#### AC-1: ProcessId wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = ProcessId(value: 1)
expect(id.value).to_equal(1)
```

</details>

#### AC-1: ByteSize wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sz = ByteSize(value: 4096)
expect(sz.value).to_equal(4096)
```

</details>

#### AC-1: Capacity wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = Capacity(value: 128)
expect(cap.value).to_equal(128)
```

</details>

#### AC-1: Count wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Count(value: 10)
expect(c.value).to_equal(10)
```

</details>

#### AC-1: Millis wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = Millis(value: 500)
expect(ms.value).to_equal(500)
```

</details>

#### AC-1: Nanos wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = Nanos(value: 1000000)
expect(ns.value).to_equal(1000000)
```

</details>

#### AC-1: Offset wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val off = Offset(value: 64)
expect(off.value).to_equal(64)
```

</details>

#### AC-1: Length wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val len = Length(value: 32)
expect(len.value).to_equal(32)
```

</details>

#### AC-1: LineNumber wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ln = LineNumber(value: 1)
expect(ln.value).to_equal(1)
```

</details>

#### AC-1: ColumnNumber wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col = ColumnNumber(value: 0)
expect(col.value).to_equal(0)
```

</details>

#### AC-1: PortNumber wraps i32 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PortNumber(value: 8080)
expect(p.value).to_equal(8080)
```

</details>

### canonical wrapper types — Team W new additions (types.spl)

#### AC-1: ExitCode wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ec = ExitCode(value: 0)
expect(ec.value).to_equal(0)
```

</details>

#### AC-1: Handle wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = Handle(value: 3)
expect(h.value).to_equal(3)
```

</details>

#### AC-1: ErrorCode wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ErrorCode(value: 22)
expect(err.value).to_equal(22)
```

</details>

#### AC-1: MemAddr wraps i64 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = MemAddr(value: 0xdeadbeef)
expect(addr.value).to_equal(0xdeadbeef)
```

</details>

#### AC-1: DurationMs wraps i32 and exposes .value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dur = DurationMs(value: 250)
expect(dur.value).to_equal(250)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
