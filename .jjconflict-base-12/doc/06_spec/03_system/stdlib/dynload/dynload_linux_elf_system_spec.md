# Dynload Linux Elf System Specification

> 1. dylib registry reset for test

<!-- sdn-diagram:id=dynload_linux_elf_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynload_linux_elf_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynload_linux_elf_system_spec -> std
dynload_linux_elf_system_spec -> os
dynload_linux_elf_system_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynload_linux_elf_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynload Linux Elf System Specification

## Scenarios

### Dynload Linux ELF System

### library registration and loading

#### registers an ELF64 .so and opens it by path

1. dylib registry reset for test
   - Expected: opened equals `handle`
2. dylib registry close
3. dylib registry close
4. dylib registry reset for test
5. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val elf = make_elf64_exec()
    val handle = dylib_registry_register("/lib/system_test.so", elf)
    expect(handle).to_be_greater_than(0)
    val opened = dylib_registry_open("/lib/system_test.so")
    expect(opened).to_equal(handle)
    dylib_registry_close(handle)
    dylib_registry_close(opened)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

#### resolves _start and main entry symbols

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(handle, "main") equals `0x400000`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/entry_test.so", make_elf64_exec())
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
    expect(dylib_registry_symbol(handle, "main")).to_equal(0x400000)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

### symbol resolution

#### resolves arbitrary dynsym symbols via slow path

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(handle, "hello") equals `0xBEEF`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/dynsym_test.so", make_elf64_with_dynsym())
    expect(handle).to_be_greater_than(0)
    # Fast path: entry symbols
    expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
    # Slow path: .dynsym lookup
    expect(dylib_registry_symbol(handle, "hello")).to_equal(0xBEEF)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

#### returns ENOENT for missing symbols

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "nonexistent") equals `0 - ENOENT as i64`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/missing_sym.so", make_elf64_exec())
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "nonexistent")).to_equal(0 - ENOENT as i64)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

### error handling

#### rejects empty path with EINVAL

1. dylib registry reset for test
   - Expected: result equals `0 - EINVAL as i64`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val result = dylib_registry_register("", make_elf64_exec())
    expect(result).to_equal(0 - EINVAL as i64)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

#### rejects invalid byte blob with ENOEXEC

1. dylib registry reset for test
2. invalid push
3. invalid push
4. invalid push
   - Expected: result equals `0 - ENOEXEC as i64`
5. dylib registry reset for test
6. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    var invalid: [u8] = []
    invalid.push(1.to_u8())
    invalid.push(2.to_u8())
    invalid.push(3.to_u8())
    val result = dylib_registry_register("/lib/bad.so", invalid)
    expect(result).to_equal(0 - ENOEXEC as i64)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

#### returns ENOENT for unregistered path

1. dylib registry reset for test
   - Expected: result equals `0 - ENOENT as i64`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val result = dylib_registry_open("/lib/not_registered.so")
    expect(result).to_equal(0 - ENOENT as i64)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

#### returns EBADF for invalid handle on symbol lookup

1. dylib registry reset for test
   - Expected: result equals `0 - EBADF as i64`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val result = dylib_registry_symbol(-1, "anything")
    expect(result).to_equal(0 - EBADF as i64)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

### lifecycle

#### supports refcount-based close and reopen

1. dylib registry reset for test
   - Expected: opened equals `handle`
   - Expected: dylib_registry_close(handle) equals `0`
   - Expected: dylib_registry_symbol(opened, "main") equals `0x400000`
   - Expected: dylib_registry_close(opened) equals `0`
   - Expected: dylib_registry_symbol(handle, "main") equals `0 - EBADF as i64`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/refcount.so", make_elf64_exec())
    # Open increases refcount
    val opened = dylib_registry_open("/lib/refcount.so")
    expect(opened).to_equal(handle)
    # First close decrements refcount
    expect(dylib_registry_close(handle)).to_equal(0)
    # Symbol still works (second ref still open)
    expect(dylib_registry_symbol(opened, "main")).to_equal(0x400000)
    # Second close fully releases
    expect(dylib_registry_close(opened)).to_equal(0)
    # After full close, symbol lookup fails
    expect(dylib_registry_symbol(handle, "main")).to_equal(0 - EBADF as i64)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

#### handles multiple libraries with independent handles

1. dylib registry reset for test
   - Expected: h1 == h2 is false
   - Expected: dylib_registry_symbol(h1, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(h2, "hello") equals `0xBEEF`
   - Expected: dylib_registry_close(h1) equals `0`
   - Expected: dylib_registry_close(h2) equals `0`
2. dylib registry reset for test
3. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_linux():
    dylib_registry_reset_for_test()
    val h1 = dylib_registry_register("/lib/a.so", make_elf64_exec())
    val h2 = dylib_registry_register("/lib/b.so", make_elf64_with_dynsym())
    expect(h1).to_be_greater_than(0)
    expect(h2).to_be_greater_than(0)
    expect(h1 == h2).to_equal(false)
    expect(dylib_registry_symbol(h1, "_start")).to_equal(0x400000)
    expect(dylib_registry_symbol(h2, "hello")).to_equal(0xBEEF)
    expect(dylib_registry_close(h1)).to_equal(0)
    expect(dylib_registry_close(h2)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: dynload_linux_elf requires Linux")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/dynload/dynload_linux_elf_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dynload Linux ELF System
- library registration and loading
- symbol resolution
- error handling
- lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
