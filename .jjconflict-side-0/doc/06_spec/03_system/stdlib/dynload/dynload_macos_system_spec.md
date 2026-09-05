# Dynload Macos System Specification

> 1. dylib registry reset for test

<!-- sdn-diagram:id=dynload_macos_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynload_macos_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynload_macos_system_spec -> std
dynload_macos_system_spec -> os
dynload_macos_system_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynload_macos_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynload Macos System Specification

## Scenarios

### Dynload macOS System

### ELF cross-load via registry

#### registers and resolves ELF64 on macOS

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_close(handle) equals `0`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/cross.so", make_elf64_exec())
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
    expect(dylib_registry_close(handle)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: macOS ELF cross-load (not on macOS)")
```

</details>

#### resolves main entry symbol on macOS

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "main") equals `0x400000`
   - Expected: dylib_registry_close(handle) equals `0`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/mac.so", make_elf64_exec())
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "main")).to_equal(0x400000)
    expect(dylib_registry_close(handle)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: macOS symbol resolve (not on macOS)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/dynload/dynload_macos_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dynload macOS System
- ELF cross-load via registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
