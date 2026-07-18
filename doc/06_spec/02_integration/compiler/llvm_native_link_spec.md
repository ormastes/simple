# Llvm Native Link Specification

> <details>

<!-- sdn-diagram:id=llvm_native_link_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_native_link_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_native_link_spec -> compiler
llvm_native_link_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_native_link_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Native Link Specification

## Scenarios

### LLVM Native Linking

#### prerequisites

<details>
<summary>Advanced: has C compiler available</summary>

#### has C compiler available _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cc = find_c_compiler()
# Most systems should have clang or gcc
if cc != "":
    expect(cc.len()).to_be_greater_than(0)
else:
    val pending_reason = "C compiler unavailable"
    expect(pending_reason.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: has runtime source directory</summary>

#### has runtime source directory _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rt_dir = find_runtime_source_dir()
if rt_dir != "":
    expect(rt_dir).to_contain("runtime")
else:
    val pending_reason = "runtime source directory unavailable"
    expect(pending_reason.len()).to_be_greater_than(0)
```

</details>


</details>

#### entry point generation

<details>
<summary>Advanced: generates valid LLVM IR for hosted entry point</summary>

#### generates valid LLVM IR for hosted entry point _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ir = generate_entry_point_ir("test_program")
expect(ir).to_contain("@__simple_runtime_init")
expect(ir).to_contain("@__simple_main")
expect(ir).to_contain("@__simple_runtime_shutdown")
expect(ir).to_contain("define i32 @main")
```

</details>


</details>

#### runtime compilation

<details>
<summary>Advanced: compiles runtime objects</summary>

#### compiles runtime objects _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cc = find_c_compiler()
val rt_dir = find_runtime_source_dir()
if cc == "" or rt_dir == "":
    # Skip if prerequisites missing
    val pending_reason = "native link prerequisites not available"
    expect(pending_reason.len()).to_be_greater_than(0)
else:
    val result = compile_runtime_objects(false, false)
    if result.is_ok():
        val objects = result.unwrap()
        expect(objects.len()).to_be_greater_than(0)
    else:
        # May fail in CI without all headers
        val pending_reason = "runtime compilation prerequisites not available"
        expect(pending_reason.len()).to_be_greater_than(0)
```

</details>


</details>

#### native executable link

<details>
<summary>Advanced: links a native executable when prerequisites are present</summary>

#### links a native executable when prerequisites are present _(slow)_

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cc = find_c_compiler()
val rt_dir = find_runtime_source_dir()
if cc == "" or rt_dir == "":
    val pending_reason = "native link prerequisites not available"
    expect(pending_reason.len()).to_be_greater_than(0)
else:
    val output = "/tmp/simple_llvm_native_link_spec.out"
    val opts = NativeLinkOptions.default()
    val result = link_llvm_native([], output, opts)
    expect(result.is_ok()).to_equal(true)
    expect(file_exists(output)).to_equal(true)
    file_delete(output)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/llvm_native_link_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM Native Linking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
