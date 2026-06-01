# Dylib Registry Specification

## Scenarios

### dylib_registry

#### registers an ELF64 library and resolves entry symbols

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(handle, "main") equals `0x400000`
   - Expected: dylib_registry_symbol(handle, "missing") equals `0 - ENOENT as i64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val handle = dylib_registry_register("/lib/demo.so", make_elf64_exec())
expect(handle).to_be_greater_than(0)
expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
expect(dylib_registry_symbol(handle, "main")).to_equal(0x400000)
expect(dylib_registry_symbol(handle, "missing")).to_equal(0 - ENOENT as i64)
```

</details>

#### registers an SMF wrapper that carries an ELF stub

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val handle = dylib_registry_register("/lib/demo.smf", make_smf_wrapped_elf64_exec())
expect(handle).to_be_greater_than(0)
expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
```

</details>

#### reuses the same handle for path-backed opens and closes by refcount

1. dylib registry reset for test
   - Expected: opened equals `handle`
   - Expected: dylib_registry_close(handle) equals `0`
   - Expected: dylib_registry_symbol(opened, "main") equals `0x400000`
   - Expected: dylib_registry_close(opened) equals `0`
   - Expected: dylib_registry_symbol(opened, "main") equals `0 - EBADF as i64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val handle = dylib_registry_register("/lib/demo.so", make_elf64_exec())
val opened = dylib_registry_open("/lib/demo.so")
expect(opened).to_equal(handle)

expect(dylib_registry_close(handle)).to_equal(0)
expect(dylib_registry_symbol(opened, "main")).to_equal(0x400000)

expect(dylib_registry_close(opened)).to_equal(0)
expect(dylib_registry_symbol(opened, "main")).to_equal(0 - EBADF as i64)
```

</details>

#### rejects missing paths and invalid byte blobs

1. dylib registry reset for test
   - Expected: dylib_registry_open("/lib/missing.so") equals `0 - ENOENT as i64`
   - Expected: dylib_registry_register("", make_elf64_exec()) equals `0 - EINVAL as i64`

2. invalid push

3. invalid push

4. invalid push
   - Expected: dylib_registry_register("/lib/bad.so", invalid) equals `0 - ENOEXEC as i64`

5. var invalid smf: [u8] = [1 to u8

6. invalid smf push

7. invalid smf push

8. invalid smf push

9. invalid smf push

10. invalid smf push

11. invalid smf = push u64 le

12. invalid smf = push u32 le

13. invalid smf = push u32 le

14. invalid smf push
   - Expected: dylib_registry_register("/lib/bad.smf", invalid_smf) equals `0 - ENOEXEC as i64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
expect(dylib_registry_open("/lib/missing.so")).to_equal(0 - ENOENT as i64)
expect(dylib_registry_register("", make_elf64_exec())).to_equal(0 - EINVAL as i64)

var invalid: [u8] = []
invalid.push(1.to_u8())
invalid.push(2.to_u8())
invalid.push(3.to_u8())
expect(dylib_registry_register("/lib/bad.so", invalid)).to_equal(0 - ENOEXEC as i64)

var invalid_smf: [u8] = [1.to_u8(), 2.to_u8(), 3.to_u8(), 4.to_u8()]
invalid_smf.push(83.to_u8())
invalid_smf.push(77.to_u8())
invalid_smf.push(70.to_u8())
invalid_smf.push(0.to_u8())
var j = 4
while j < 44:
    invalid_smf.push(0.to_u8())
    j = j + 1
invalid_smf = push_u64_le(invalid_smf, 0x400000)
invalid_smf = push_u32_le(invalid_smf, 4)
invalid_smf = push_u32_le(invalid_smf, 4)
while invalid_smf.len() < 132:
    invalid_smf.push(0.to_u8())
expect(dylib_registry_register("/lib/bad.smf", invalid_smf)).to_equal(0 - ENOEXEC as i64)
```

</details>

#### resolves arbitrary symbols via slow path

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_symbol(handle, "hello") equals `0xBEEF`
   - Expected: dylib_registry_symbol(handle, "missing") equals `0 - ENOENT as i64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val handle = dylib_registry_register("/lib/dynsym.so", make_elf64_with_dynsym())
expect(handle).to_be_greater_than(0)
# Fast path
expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
# Slow path — symbol from .dynsym
expect(dylib_registry_symbol(handle, "hello")).to_equal(0xBEEF)
# Slow path — missing symbol
expect(dylib_registry_symbol(handle, "missing")).to_equal(0 - ENOENT as i64)
```

</details>

#### does not claim registry symbols are process-callable

1. dylib registry reset for test
   - Expected: dylib_registry_symbol(handle, "hello") equals `0xBEEF`
   - Expected: dylib_registry_symbol_is_process_callable(handle, "hello") is false
   - Expected: dylib_registry_symbol_is_process_callable(handle, "missing") is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val handle = dylib_registry_register("/lib/dynsym.smf", make_elf64_with_dynsym())
expect(handle).to_be_greater_than(0)
expect(dylib_registry_symbol(handle, "hello")).to_equal(0xBEEF)
expect(dylib_registry_symbol_is_process_callable(handle, "hello")).to_equal(false)
expect(dylib_registry_symbol_is_process_callable(handle, "missing")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/dylib_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dylib_registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

