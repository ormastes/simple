# Bug: `rt_mem_attr_set_owner` owner name dropped under JIT/native engine

**Found:** 2026-07-29, while writing `test/03_system/check/mem_attr_report_spec.spl`
**Status:** RESOLVED same day.

## Resolution

Root cause: the extern was declared `*const c_char` (NUL-terminated C string),
but native codegen passes `text` extern arguments as a raw `(ptr, len)`
byte-span pair — the same convention `rt_file_exists`/`rt_env_get` use — so
`CStr::from_ptr` read an empty/garbage string. Fix: signature changed to
`(name_ptr: *const u8, name_len: u64)` decoded via `from_raw_parts` +
`from_utf8` (heap.rs), plus the matching `text_arg_indices` entry in
`codegen/instr/calls.rs` and `RuntimeFuncSpec` row in `codegen/runtime_sffi.rs`.
The interpreter wrapper (`interpreter_extern/memory.rs`) calls
`set_current_owner` directly and was never affected. Verified: JIT probe shows
the owner row with real byte counts; interpreter unchanged; spec 2/2.

## Summary

`rt_mem_attr_set_owner(name: text)` (`src/compiler_rust/runtime/src/value/heap.rs`,
registered via `insert_simple!` in `interpreter_extern/mod.rs`) correctly
registers the owner name when the interpreter engine runs the call
(`SIMPLE_EXECUTION_MODE=interpreter`), but the owner name is **dropped** (empty
string) when the same `.spl` program runs under the default engine used by
`bin/simple run` (Cranelift JIT / native). Byte/alloc counting itself still
works under that engine — only the name is lost.

## Repro

```
extern fn rt_mem_attr_set_owner(name: text)
extern fn rt_mem_attr_report(n: i64) -> text

fn main() -> i64:
    rt_mem_attr_set_owner("attr_spec_owner")
    print rt_mem_attr_report(8)
    0
```

- `SIMPLE_MEM_ATTR=1 SIMPLE_EXECUTION_MODE=interpreter <bin> run repro.spl`
  → report row: `attr_spec_owner\t0\t0\t0` (name correct, byte counting is 0
  because small interpreter string allocations don't route through the
  counted allocator — separate, lower-severity gap)
- `SIMPLE_MEM_ATTR=1 <bin> run repro.spl` (default engine, JIT/native)
  → report row: `\t252\t252\t6` (name is **empty**, byte/alloc counts are
  real and nonzero)

Reproduced on `src/compiler_rust/target/debug/simple` (debug build of the
Rust seed with the M1 attribution externs).

## Suspected cause

`rt_mem_attr_set_owner`'s Rust-level entry point exists in two forms:
1. `interpreter_extern::memory::rt_mem_attr_set_owner(args: &[Value])` —
   value-based, used by the tree-walk interpreter. Reads `Value::Str` directly;
   correct.
2. `heap::rt_mem_attr_set_owner(name: *const c_char)` — raw C-ABI `extern "C"`
   entry point, used when JIT/native-compiled code calls the extern directly.
   Expects a NUL-terminated C string via `CStr::from_ptr`.

Simple's native `text` value representation is very likely a
length-prefixed/fat-pointer string, not a NUL-terminated C string. When JIT
codegen calls path (2) directly, the pointer handed to `CStr::from_ptr` is
either misinterpreted or points at something that reads as an empty/garbage
string before finding a NUL byte — dropping the intended owner name while the
allocation-counting side effects (which don't depend on decoding the name)
continue to work correctly.

## Impact

Low-to-moderate: the P1 per-owner-attribution feature
(`doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md`)
is unusable for its stated purpose ("which module/owner is allocating") under
the JIT/native engine — the default engine for `bin/simple run` and ordinary
compiled programs — because every owner collapses into rows with a blank
name. It still works correctly under the interpreter engine (`bin/simple
test`'s default engine), and the `spec` acceptance criterion ("Works under
interpreter AND native (both backends)") is not yet met for the *name*
half of attribution, only the *byte-counting* half.

## Workaround used in the spec

`test/03_system/check/mem_attr_report_spec.spl` forces
`SIMPLE_EXECUTION_MODE=interpreter` on its child-process fixture run so the
owner name resolves correctly; it does not assert on byte counts (which are
legitimately 0 under the interpreter for the reason above).
