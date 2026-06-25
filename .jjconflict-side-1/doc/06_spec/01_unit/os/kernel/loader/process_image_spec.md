# Process Image Specification

> <details>

<!-- sdn-diagram:id=process_image_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_image_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_image_spec -> std
process_image_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_image_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Image Specification

## Scenarios

### process image builder

#### builds an x86_64 user image from executable bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_x86_64_exec()
val image = build_user_process_image("/usr/bin/x86_exec_probe", bytes, Architecture.X86_64, [], [])
expect(image.is_ok()).to_equal(true)
val built = image.unwrap()
expect(built.entry).to_equal(0x400000)
expect(built.stack_top).to_equal(X86_64_USER_STACK_TOP)
expect(built.stack_size).to_equal(0x800000)
expect(built.segment_count).to_equal(1)
expect(built.argv.len()).to_equal(1)
expect(built.argv[0]).to_equal("/usr/bin/x86_exec_probe")
expect(built.envp.len()).to_equal(0)
```

</details>

#### builds an x86_32 user image from executable bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_x86_32_exec()
val image = build_user_process_image("/usr/bin/x86_32_exec_probe", bytes, Architecture.X86, [], [])
expect(image.is_ok()).to_equal(true)
val built = image.unwrap()
expect(built.entry).to_equal(0x8048000)
expect(built.stack_top).to_equal(X86_32_USER_STACK_TOP)
expect(built.stack_size).to_equal(0x800000)
expect(built.segment_count).to_equal(1)
expect(built.segments[0].virt_addr).to_equal(0x8048000)
```

</details>

#### builds an x86_64 user image from an SMF-wrapped executable stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_smf_wrapped_x86_64_exec()
val image = build_user_process_image("/usr/bin/smf_x86_exec_probe", bytes, Architecture.X86_64, [], [])
expect(image.is_ok()).to_equal(true)
val built = image.unwrap()
expect(built.entry).to_equal(0x400000)
expect(built.stack_top).to_equal(X86_64_USER_STACK_TOP)
expect(built.stack_size).to_equal(0x800000)
expect(built.segment_count).to_equal(1)
expect(built.file_bytes[0]).to_equal(0x7F.to_u8())
```

</details>

#### builds an x86_64 user image from multi-PT_LOAD app bytes and owns the copies

- var bytes = make multi pt load x86 64 exec
   - Expected: image.is_ok() is true
   - Expected: built.entry equals `0x400000`
   - Expected: built.stack_top equals `X86_64_USER_STACK_TOP`
   - Expected: built.stack_size equals `0x800000`
   - Expected: built.segments.len() equals `2`
   - Expected: built.segment_count equals `2`
   - Expected: built.segments[0].data.len() equals `4`
   - Expected: built.segments[0].data[0] equals `0xC3.to_u8()`
   - Expected: built.segments[1].file_size equals `0`
   - Expected: built.segments[1].mem_size equals `0x1000`
   - Expected: built.segments[1].data.len() equals `0`
   - Expected: built.file_bytes[0] equals `0x7F.to_u8()`
   - Expected: built.file_bytes[0xC0] equals `0xC3.to_u8()`
- bytes[0] = 0x00 to u8
- bytes[0xC0] = 0x00 to u8
   - Expected: built.file_bytes[0] equals `0x7F.to_u8()`
   - Expected: built.segments[0].data[0] equals `0xC3.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes = make_multi_pt_load_x86_64_exec()
val image = build_user_process_image("/sys/apps/browser_demo", bytes, Architecture.X86_64, [], [])
expect(image.is_ok()).to_equal(true)
val built = image.unwrap()

expect(built.entry).to_equal(0x400000)
expect(built.stack_top).to_equal(X86_64_USER_STACK_TOP)
expect(built.stack_size).to_equal(0x800000)
expect(built.segments.len()).to_equal(2)
expect(built.segment_count).to_equal(2)
expect(built.segments[0].data.len()).to_equal(4)
expect(built.segments[0].data[0]).to_equal(0xC3.to_u8())
expect(built.segments[1].file_size).to_equal(0)
expect(built.segments[1].mem_size).to_equal(0x1000)
expect(built.segments[1].data.len()).to_equal(0)
expect(built.file_bytes[0]).to_equal(0x7F.to_u8())
expect(built.file_bytes[0xC0]).to_equal(0xC3.to_u8())

bytes[0] = 0x00.to_u8()
bytes[0xC0] = 0x00.to_u8()

expect(built.file_bytes[0]).to_equal(0x7F.to_u8())
expect(built.segments[0].data[0]).to_equal(0xC3.to_u8())
```

</details>

#### preserves explicit argv and envp in the built image

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_x86_64_exec()
val image = build_user_process_image(
    "/usr/bin/x86_exec_probe",
    bytes,
    Architecture.X86_64,
    ["clang", "--version"],
    ["PWD=/work", "TERM=simple"]
)
expect(image.is_ok()).to_equal(true)
val built = image.unwrap()
expect(built.argv.len()).to_equal(2)
expect(built.argv[0]).to_equal("clang")
expect(built.argv[1]).to_equal("--version")
expect(built.envp.len()).to_equal(2)
expect(built.envp[0]).to_equal("PWD=/work")
expect(built.envp[1]).to_equal("TERM=simple")
expect(built.initial_stack_bytes.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/process_image_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- process image builder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
