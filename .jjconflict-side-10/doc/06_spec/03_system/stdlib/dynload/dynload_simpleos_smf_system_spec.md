# Dynload Simpleos Smf System Specification

> 1. dylib registry reset for test

<!-- sdn-diagram:id=dynload_simpleos_smf_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynload_simpleos_smf_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynload_simpleos_smf_system_spec -> std
dynload_simpleos_smf_system_spec -> os
dynload_simpleos_smf_system_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynload_simpleos_smf_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynload Simpleos Smf System Specification

## Scenarios

### Dynload SimpleOS SMF System

### SMF library loading

#### registers SMF library and resolves entry via ELF stub

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(handle, "main") equals `0x400000`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val smf = make_smf_wrapped_elf64_exec()
    val handle = dylib_registry_register("/sys/apps/demo.smf", smf)
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
    expect(dylib_registry_symbol(handle, "main")).to_equal(0x400000)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_simpleos_smf requires Linux")
```

</details>

#### registers multiple SMF libraries independently

1. dylib registry reset for test
   - Expected: h1 == h2 is false
   - Expected: dylib_registry_symbol(h1, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(h2, "main") equals `0x400000`
   - Expected: dylib_registry_close(h1) equals `0`
   - Expected: dylib_registry_close(h2) equals `0`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val smf = make_smf_wrapped_elf64_exec()
    val h1 = dylib_registry_register("/sys/apps/lib_a.smf", smf)
    val h2 = dylib_registry_register("/sys/apps/lib_b.smf", smf)
    expect(h1).to_be_greater_than(0)
    expect(h2).to_be_greater_than(0)
    expect(h1 == h2).to_equal(false)
    expect(dylib_registry_symbol(h1, "_start")).to_equal(0x400000)
    expect(dylib_registry_symbol(h2, "main")).to_equal(0x400000)
    expect(dylib_registry_close(h1)).to_equal(0)
    expect(dylib_registry_close(h2)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_simpleos_smf requires Linux")
```

</details>

### error handling

#### rejects SMF with invalid ELF stub

1. dylib registry reset for test
2. var bad smf: [u8] = [1 to u8
3. bad smf push
4. bad smf push
5. bad smf push
6. bad smf push
7. bad smf push
8. bad smf = push u64 le
9. bad smf = push u32 le
10. bad smf = push u32 le
11. bad smf push
   - Expected: dylib_registry_register("/sys/bad.smf", bad_smf) equals `0 - ENOEXEC as i64`
12. dylib registry reset for test
13. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    # Build an SMF trailer with garbage as the "ELF stub"
    var bad_smf: [u8] = [1.to_u8(), 2.to_u8(), 3.to_u8(), 4.to_u8()]
    # SMF magic "SMF\0"
    bad_smf.push(83.to_u8())
    bad_smf.push(77.to_u8())
    bad_smf.push(70.to_u8())
    bad_smf.push(0.to_u8())
    # Pad to offset 44 within trailer
    var j = 4
    while j < 44:
        bad_smf.push(0.to_u8())
        j = j + 1
    # Entry point
    bad_smf = push_u64_le(bad_smf, 0x400000)
    # stub_offset and stub_size
    bad_smf = push_u32_le(bad_smf, 4)
    bad_smf = push_u32_le(bad_smf, 4)
    # Pad to 128-byte trailer
    while bad_smf.len() < 132:
        bad_smf.push(0.to_u8())
    expect(dylib_registry_register("/sys/bad.smf", bad_smf)).to_equal(0 - ENOEXEC as i64)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_simpleos_smf requires Linux")
```

</details>

### mixed format registry

#### handles mixed ELF and SMF in the same registry

1. dylib registry reset for test
   - Expected: h_elf == h_smf is false
   - Expected: dylib_registry_symbol(h_elf, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(h_smf, "_start") equals `0x400000`
   - Expected: dylib_registry_close(h_elf) equals `0`
   - Expected: dylib_registry_close(h_smf) equals `0`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val h_elf = dylib_registry_register("/lib/native.so", make_elf64_exec())
    val h_smf = dylib_registry_register("/sys/apps/app.smf", make_smf_wrapped_elf64_exec())
    expect(h_elf).to_be_greater_than(0)
    expect(h_smf).to_be_greater_than(0)
    expect(h_elf == h_smf).to_equal(false)
    expect(dylib_registry_symbol(h_elf, "_start")).to_equal(0x400000)
    expect(dylib_registry_symbol(h_smf, "_start")).to_equal(0x400000)
    expect(dylib_registry_close(h_elf)).to_equal(0)
    expect(dylib_registry_close(h_smf)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_simpleos_smf requires Linux")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/dynload/dynload_simpleos_smf_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dynload SimpleOS SMF System
- SMF library loading
- error handling
- mixed format registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
