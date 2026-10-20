# Native build: imported function used as a value calls through NULL; C `rt_array_extend_i64` corrupts packed bytes

- **Date:** 2026-10-20
- **Status:** worked around at the two linker sites; the codegen root cause is open
- **Found by:** native-building `test/05_perf/compiler/linker/internal_link_spec_driver.spl`
  (seed `b37262fb`, cranelift, `SIMPLE_NATIVE_BUILD_RUST=1`, core-c-bootstrap runtime)

## 1. Imported function as a value: NULL call (open)

`elf_operation_bindings.spl` stored `Some(file_read_bytes_result)` and `Some(elf_exec_plan)`.
Both functions are defined in another unit. Calling the stored `fn` value jumped to
address 0.

Backtrace, frame #1:
`compiler__backend__linker__elf__elf_operation_bindings__ElfSealedOperationsV1_dot_read_bytes`

Functions defined in the same unit (`_elf_builtin_relocate`, `_elf_builtin_write`) get a
`$boxed` thunk in `nm`. The imported ones get none.

Workaround: local one-line thunks, `_elf_builtin_read_bytes` and `_elf_builtin_layout`.
Fix wanted: codegen should emit (or reference) a `$boxed` thunk for a cross-unit
function taken as a value, instead of a NULL slot.

## 2. C runtime `rt_array_extend_i64` on `[u8]` (fixed)

`src/runtime/runtime_native.c` copied element by element as
`rt_array_push(d, rt_array_get(s, i))`. For a byte array, `rt_array_get` returns the raw
byte, but `rt_array_push` decodes its argument as a tagged value. Every byte that is a
multiple of 8 was therefore divided by 8. A CIE length of 0x10 became 0x02 in a linked
`.eh_frame`, and 0x78 became 0x0f.

Fix: packed byte arrays now copy raw bytes with `memmove`, matching the Rust runtime
(`collections.rs rt_array_extend_i64`). A packed/unpacked mix is refused, as Rust does.
The source is re-read after reserve, so self-extend is safe.

## Verification

The native driver's output is byte-identical to the interpreted driver
(`cmp`) for `hello_libc_a64.o` (exit 42) and `wide_str_a64.o` (exit 44).

| driver | link time |
|---|---|
| native | 13-20 ms |
| interpreted | 760 ms |
