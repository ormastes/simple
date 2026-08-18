# Loader: interpreter cannot invoke a raw i64 code address (segment mapper positive control stays red)

Date: 2026-08-18. Lane: aspect-dynload.
Binary: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59645008, 2026-08-18 10:12:23.164167908 +0000 (identical before and after every run below).

## Symptom

`test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl` — 8 examples,
7 pass, 1 fails, honestly and deliberately left red:

```
POSITIVE CONTROL: the mapped code still executes correctly
  x calls each symbol and gets that symbol's own value back
    assert_equal failed: expected 33, got 0
```

## What was actually wrong first (FIXED)

`src/compiler/99.loader/smf_mmap_native.spl` was a **Dict-simulated fake**
despite a header claiming otherwise: `_g_fake_memory: Dict<i64, [u8]>`, and
`native_call_function_0` unconditionally `return 0`. Both `segment_mapper.spl`
and `module_loader_compat.spl` resolve `compiler.loader.smf_mmap_native` to this
top-level file, so the entire "mapped" path was simulated. That fake `return 0`
is exactly the observed `expected 33, got 0`.

Fixed by routing `native_alloc_exec_memory` / `native_write_exec_memory` /
`native_make_executable` / `native_make_rw` / `native_free_exec_memory` /
`native_reloc_write_i32` / `native_reloc_write_i64` / `native_mmap_read_bytes`
to real `rt_mmap_raw` / `rt_mprotect` / `rt_ptr_write_u8` / `rt_ptr_read_u8`
SFFI calls — the same externs already proven under `bin/simple test` by
`native_mmap_byte_read_spec.spl`.

## What remains, and why it is an ENGINE gap not a mapper bug

There is no supported mechanism in this interpreter to invoke a raw `i64` code
address as a function: no working pointer cast (`unsafe: addr as *u8` /
`fn_ptr as fn()->i64` fails to COMPILE under this seed with
`unsupported cast target type: Pointer`), and no `rt_call_*` extern in the C
runtime. An intermediate attempt at the cast form regressed the file from 1/8
to 6/8 failing and was reverted.

This matches an already-documented limitation: `test/02_integration/app/loader_exec_memory_spec.spl:30`
carries `# skip: native exec memory functions require compiled mode (not interpreter)`.

## Why the assertion was NOT weakened

The positive control is the only example proving the loader still produces
RUNNING code rather than merely correct-looking arithmetic. The other 7 examples
(symbol placement at base+offset, three distinct addresses from one mapping,
out-of-segment refusal, negative offset, over-page alignment, one-free-per-segment
unmap, stable segment key) all pass and all test arithmetic or lifecycle. A green
obtained by deleting or skipping the positive control would destroy the only
evidence that matters. Per `.claude/rules/testing.md`, left red.

## Consequence to state plainly

The lane's headline claim — ONE mmap per SEGMENT instead of one per SYMBOL — is
proven as arithmetic and as mapping lifecycle, and the native layer beneath it is
now real rather than simulated, but **execution of the mapped code is NOT proven
in interpreter mode**. It requires a compiled-mode run to verify.

## Fix options

1. Add an `rt_call_ptr_0(addr: i64) -> i64` extern to the C runtime and use it.
2. Make the pointer/fn cast compile so the sibling `loader/smf_mmap_native.spl`
   approach works.
3. Run this spec under compiled mode in a lane that has a compiled binary.
