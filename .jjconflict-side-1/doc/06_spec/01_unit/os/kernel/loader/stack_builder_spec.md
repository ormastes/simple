# Stack Builder Specification

> _Image-size-to-stack-size scaling._

<!-- sdn-diagram:id=stack_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stack_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stack_builder_spec -> std
stack_builder_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stack_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stack Builder Specification

## Scenarios

### kernel.loader.stack_builder.compute_stack_size
_Image-size-to-stack-size scaling._

#### returns 8 MB for zero-sized images

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sz = compute_stack_size(0)
expect(sz).to_equal(DEFAULT_USER_STACK_SIZE)
```

</details>

#### returns 8 MB (floor) for small images

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sz = compute_stack_size(1024)
expect(sz).to_equal(DEFAULT_USER_STACK_SIZE)
```

</details>

#### caps at 128 MB for huge images (clang-class binaries)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sz = compute_stack_size(1_000_000_000 as u64)
expect(sz).to_equal(MAX_USER_STACK_SIZE)
```

</details>

#### scales by image_size/8 between the floor and the cap

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 80 MB binary -> 10 MB stack (above 8 MB floor, below 128 MB cap)
val sz = compute_stack_size(80 * 1024 * 1024)
expect(sz).to_equal(10 * 1024 * 1024)
```

</details>

### kernel.loader.stack_builder.build_initial_stack
_SysV initial stack frame layout._

#### writes argc=1 as the first u64 for a one-arg invocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], [])
val argc = _read_u64_le(result.bytes, 0)
expect(argc).to_equal(1 as u64)
```

</details>

#### aligns sp to 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], [])
expect(result.sp & 0xf).to_equal(0 as u64)
```

</details>

#### places argv pointers in ascending address order

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# argv[0]=a (2 bytes), argv[1]=bb (3 bytes), argv[2]=ccc (4 bytes).
# argv[0] is deposited highest in the string pool, argv[N-1] lowest.
val result = build_initial_stack(STACK_TOP, ["a", "bb", "ccc"], [], [])
val argc = _read_u64_le(result.bytes, 0)
expect(argc).to_equal(3 as u64)
val ptr0 = _read_u64_le(result.bytes, 8)
val ptr1 = _read_u64_le(result.bytes, 16)
val ptr2 = _read_u64_le(result.bytes, 24)
val nullptr = _read_u64_le(result.bytes, 32)
expect(ptr0 > ptr1).to_be_true()
expect(ptr1 > ptr2).to_be_true()
expect(nullptr).to_equal(0 as u64)
# All three pointers must fall inside the serialized blob region,
# which spans [sp, STACK_TOP).
expect(ptr0 < STACK_TOP).to_be_true()
expect(ptr2 >= result.sp).to_be_true()
```

</details>

#### terminates argv and envp with NULL and auxv with AT_NULL

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], [])
# Layout: argc, argv[0], argv_null, envp_null, aux[0].type ...
val argv_null = _read_u64_le(result.bytes, 16)
val envp_null = _read_u64_le(result.bytes, 24)
expect(argv_null).to_equal(0 as u64)
expect(envp_null).to_equal(0 as u64)
```

</details>

#### honors caller-supplied auxv entries before AT_NULL

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extra: [AuxEntry] = [AuxEntry(aux_type: 9 as u64, val: 0xdead as u64)]
val result = build_initial_stack(STACK_TOP, ["/bin/x"], [], extra)
# The blob must contain the 0xdead value somewhere in the aux region.
var found: bool = false
var off: i64 = 0
val n = result.bytes.len()
while off + 8 <= n:
    if _read_u64_le(result.bytes, off) == (0xdead as u64):
        found = true
    off = off + 8
expect(found).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/stack_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel.loader.stack_builder.compute_stack_size
- kernel.loader.stack_builder.build_initial_stack

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
