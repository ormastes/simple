# MDSOC+ ECS Advisory Lint Rule Specification

> Tests the `mdsoc_plus_ecs_advisory` lint rule (`check_mdsoc_plus_001`) that scans source text for structs with >= 7 fields in MDSOC+ userland paths (`src/os/services/**`, `src/os/apps/**`) that do not import any ECS module.

<!-- sdn-diagram:id=mdsoc_plus_ecs_advisory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mdsoc_plus_ecs_advisory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mdsoc_plus_ecs_advisory_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mdsoc_plus_ecs_advisory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MDSOC+ ECS Advisory Lint Rule Specification

Tests the `mdsoc_plus_ecs_advisory` lint rule (`check_mdsoc_plus_001`) that scans source text for structs with >= 7 fields in MDSOC+ userland paths (`src/os/services/**`, `src/os/apps/**`) that do not import any ECS module.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MDSOC-PLUS-001 |
| Category | Compiler \| Semantics \| Lint |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/spec/lint/mdsoc_plus_ecs_advisory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `mdsoc_plus_ecs_advisory` lint rule (`check_mdsoc_plus_001`) that
scans source text for structs with >= 7 fields in MDSOC+ userland paths
(`src/os/services/**`, `src/os/apps/**`) that do not import any ECS module.

## Key Concepts

| Concept | Description |
|---------|-------------|
| MDSOC_PLUS_001 | Struct with >= 7 fields in os/services or os/apps without ECS import |
| MdsocPlusEcsWarning | Struct: code, severity, message, hint, line_num, file_path |
| check_mdsoc_plus_001 | Entry-point: (source: text, path: text) -> [MdsocPlusEcsWarning] |

## Scenarios

### mdsoc_plus_ecs_advisory — MDSOC_PLUS_001 fires

#### src/os/services/ path with 8-field struct and no ECS import

#### emits at least one MDSOC_PLUS_001 warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("SchedulerState")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_be_greater_than(0)
```

</details>

#### warning code is MDSOC_PLUS_001

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("SchedulerState")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws[0].code).to_equal("MDSOC_PLUS_001")
```

</details>

#### warning severity is WARNING

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("SchedulerState")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws[0].severity).to_equal("WARNING")
```

</details>

#### warning file_path matches the supplied path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("SchedulerState")
val path = services_path()
val ws = check_mdsoc_plus_001(src, path)
expect(ws[0].file_path).to_equal(path)
```

</details>

#### src/os/apps/ path with 8-field struct and no ECS import

#### emits at least one MDSOC_PLUS_001 warning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("AppState")
val ws = check_mdsoc_plus_001(src, apps_path())
expect(ws.len()).to_be_greater_than(0)
```

</details>

#### warning code is MDSOC_PLUS_001

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("AppState")
val ws = check_mdsoc_plus_001(src, apps_path())
expect(ws[0].code).to_equal("MDSOC_PLUS_001")
```

</details>

### mdsoc_plus_ecs_advisory — excluded paths produce no warnings

#### src/os/kernel/ path

#### emits no warnings for kernel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("PageTable")
val ws = check_mdsoc_plus_001(src, kernel_path())
expect(ws.len()).to_equal(0)
```

</details>

#### src/os/drivers/ path

#### emits no warnings for drivers path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("VirtioNetState")
val ws = check_mdsoc_plus_001(src, drivers_path())
expect(ws.len()).to_equal(0)
```

</details>

### mdsoc_plus_ecs_advisory — ECS import suppresses the warning

#### file imports std.ecs.*

#### emits no warnings when std.ecs.world is imported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "use std.ecs.world\n" + make_large_struct("ServiceState")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

#### emits no warnings when std.ecs.component is imported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "use std.ecs.component\n" + make_large_struct("ServiceState")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

### mdsoc_plus_ecs_advisory — struct-level exemptions

#### @repr(\

#### emits no warnings for repr-C struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "@repr(\"C\")\nstruct FfiLayout:\n    a: i64\n    b: i64\n    c: i64\n    d: i64\n    e: i64\n    f: i64\n    g: i64\n    h: i64\n"
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

#### struct name ends in Action

#### emits no warnings for DTO-suffix Action

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("SpawnAction")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

#### struct name ends in Message

#### emits no warnings for DTO-suffix Message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("BootMessage")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

#### struct name ends in Request

#### emits no warnings for DTO-suffix Request

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("AllocRequest")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

#### struct name ends in Reply

#### emits no warnings for DTO-suffix Reply

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("AllocReply")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

#### struct name ends in Event

#### emits no warnings for DTO-suffix Event

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("TimerEvent")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

### mdsoc_plus_ecs_advisory — small structs are exempt

#### struct with 4 fields in services path

#### emits no warnings for small struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_small_struct("TinyState")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws.len()).to_equal(0)
```

</details>

#### struct with exactly 6 fields in apps path

#### emits no warnings for 6-field struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "struct SixField:\n    a: i64\n    b: i64\n    c: i64\n    d: i64\n    e: i64\n    f: i64\n"
val ws = check_mdsoc_plus_001(src, apps_path())
expect(ws.len()).to_equal(0)
```

</details>

### MdsocPlusEcsWarning — struct fields

#### warning produced for large struct in services

#### hint field is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("LargeService")
val ws = check_mdsoc_plus_001(src, services_path())
val hint = ws[0].hint
expect(hint.len()).to_be_greater_than(0)
```

</details>

#### message contains the struct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("LargeService")
val ws = check_mdsoc_plus_001(src, services_path())
expect(ws[0].message).to_contain("LargeService")
```

</details>

#### fmt() includes the warning code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = make_large_struct("LargeService")
val ws = check_mdsoc_plus_001(src, services_path())
val formatted = ws[0].fmt()
expect(formatted).to_contain("MDSOC_PLUS_001")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
