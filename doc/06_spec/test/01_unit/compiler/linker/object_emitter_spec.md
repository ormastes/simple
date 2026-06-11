# Object Emitter Specification

> 1.   = shell

<!-- sdn-diagram:id=object_emitter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=object_emitter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

object_emitter_spec -> compiler
object_emitter_spec -> app
object_emitter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=object_emitter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Object Emitter Specification

## Scenarios

### object_emitter

#### writes ELF64 object without clang fallback

1.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = host_arch()
# Use a minimal 'ret' instruction per arch
val code = if arch == "aarch64":
    # AArch64: ret -> 0xd65f03c0 little endian bytes
    [0xC0, 0x03, 0x5F, 0xD6]
else:
    # x86_64: ret
    [0xC3]

val code_unit = make_object_code_unit("test_fn", code)
val obj_path = "/tmp/object_emitter_test.o"

val res = assemble_code_units([code_unit], obj_path, false)
expect(res.is_ok()).to_equal(true)
expect(file_exists(obj_path)).to_equal(true)
expect(file_size(obj_path) > 0).to_equal(true)

# cleanup
_ = shell("rm -f '{obj_path}' '{obj_path}.S'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/object_emitter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- object_emitter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
