# Bug: rt_process_run_with_limits Arg-Count Mismatch and Missing JIT Expansion
## Resolved 2026-11-25 — both defects fixed in current source (see verification note)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-31  
**Status:** Resolved 2026-11-25 (was: Dormant/unreachable; defects now repaired at all three layers)  
**Severity:** High (when activated)

## Defect Summary

`rt_process_run_with_limits` in `src/compiler_rust/runtime/src/value/sffi/env_process.rs` carries two independent defects that prevent correct compilation to native code or JIT:

### Defect 1: Arg-Count Mismatch

**Location:** `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`  
**Current spec:** `RuntimeFuncSpec::new("rt_process_run_with_limits", &[I64, I64, I64, I64, I64], &[I64])`  
**Declared args:** 5 I64  
**Actual Rust signature:** 8 parameters

**Rust signature** (`src/compiler_rust/runtime/src/value/sffi/env_process.rs`, line ~1231):
```rust
pub unsafe extern "C" fn rt_process_run_with_limits(
    cmd_ptr: *const u8,      // 1
    cmd_len: u64,            // 2
    args: RuntimeValue,      // 3
    timeout_ms: i64,         // 4
    memory_bytes: i64,       // 5
    cpu_seconds: i64,       // 6
    max_fds: i64,           // 7
    max_procs: i64,         // 8
) -> RuntimeValue
```

The spec declares 5 I64 args but the Rust function has 8 parameters. The spec's comment is outdated: `rt_process_run_with_limits(cmd_ptr, cmd_len, args, timeout_ms, memory_mb)` — it only mentions 5 args but forgets `cpu_seconds`, `max_fds`, `max_procs`.

### Defect 2: Missing from JIT Text-Expansion Table

**Location:** `src/compiler_rust/compiler/src/codegen/instr/calls.rs`, line ~48  
**Function:** `process_c_runtime_arg_indices()`

The function is **missing from the ptr/len expansion table**. Its siblings are all present:
- `rt_process_run` — ✓ present
- `rt_process_run_inherit` — ✓ present
- `rt_process_spawn` — ✓ present
- `rt_process_spawn_async` — ✓ present
- `rt_process_spawn_guarded` — ✓ present
- `rt_process_execute` — ✓ present
- `rt_process_run_timeout` — ✓ present
- `rt_process_run_bounded` — ✓ present
- `rt_process_run_with_limits` — **✗ MISSING**

This table handles expanding `String` arguments to `(ptr, len)` pairs in JIT-compiled calls to SFFI functions. Without this entry, if a call were lowered to JIT, it would pass a single String RuntimeValue where the native code expects two separate `(ptr, len)` values, producing silent memory corruption.

## Why It Is Dormant

**No call-site lowering in the compiler frontend.** A cross-repo grep confirms:
- Referenced only in: runtime stubs (`elf_utils.rs`), SFFI specs (metadata), comments, and the function's own definition
- **Zero occurrences** in any compiler-layer call-lowering path
- The Simple-level SFFI wrappers in `src/lib/nogc_sync_mut/sffi/system.spl` do not call this function
- The incomplete signature in that wrapper (`extern fn rt_process_run_with_limits(cmd: text, args: [text], timeout_ms: i64, memory_mb: i64)`) further isolates it — it's missing the last three parameters that the Rust function requires

No Simple code calls this function today, so neither the JIT expansion miss nor the arity mismatch causes a runtime failure.

## Why It Cannot Be "Fixed" Incrementally

Adding a one-line entry to `process_c_runtime_arg_indices` would be **wrong** because:

1. The RuntimeFuncSpec declares 5 args but the Rust function has 8 parameters
2. The entry would claim to expand a (ptr, len) pair for the command, but the remaining 6 args would still be mismatched
3. A call site that appears to work after adding the table entry would silently miscompile, with arguments shifted or lost

**Correct fix order:**
1. Update the RuntimeFuncSpec to declare the actual 8 parameters (or 7 if cmd stays as 1 String and gets expanded): `&[I64, I64, I64, I64, I64, I64, I64, I64]` for the expanded form
2. Update the spec/comment in both `runtime_sffi.rs` and the SFFI metadata to match the real signature
3. Only then add the entry to `process_c_runtime_arg_indices`
4. Update Simple-level SFFI wrappers to match

Whoever wires up a call site owns fixing both defects before landing the change.

## Cross-Reference

See also: `doc/08_tracking/bug/rt_process_spawn_async_jit_missing_ptr_len_expansion_2026-07-31.md` — the live sibling defect that prompted this audit.


## Verification 2026-11-25 (release/1.0.0 @ 4c6024f8271) — fixed in source

All three layers named in "Why It Cannot Be Fixed Incrementally" now agree,
verified by source inspection (the Rust runtime cannot be rebuilt on this
host, but both defects were source-level spec/table mismatches, decidable by
reading the source):

1. **Arity:** `RuntimeFuncSpec::new("rt_process_run_with_limits", &[I64; 8],
   &[I64])` at `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1769`
   now declares 8 I64 args, with a comment requiring an exact match to the
   Rust definition. The Rust signature
   (`src/compiler_rust/runtime/src/value/sffi/env_process.rs:1702`) still has
   the 8 parameters — spec and definition match.
2. **JIT ptr/len expansion:** `rt_process_run_with_limits` is now present in
   `process_c_runtime_arg_indices` (`src/compiler_rust/compiler/src/codegen/
   instr/calls.rs:3414`, `Some(&[0])` — cmd expands to (ptr, len)).
3. **Simple-level wrapper:** `src/lib/nogc_sync_mut/sffi/system_hosted_extras.spl:8`
   now declares all 8 parameters (`cpu_seconds`, `max_fds`, `max_procs`
   included). The pure-Simple extern-ABI table
   (`src/compiler/50.mir/text_extern_abi.spl:110`) also lists the function
   with the same (ptr, len) treatment.

The doc's stated fix order (spec first, then table entry, then wrappers) is
exactly what the current tree reflects. No Rust rebuild or native execution
was possible here, so this is a static verification; the mismatch class it
guards against is fully decidable at source level.
