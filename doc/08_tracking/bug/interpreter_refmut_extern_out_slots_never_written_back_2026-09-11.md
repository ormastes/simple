# Interpreter `&mut` on an extern argument never wrote back to the variable

- **Status:** FIXED 2026-09-11
- **Lane:** `.spipe/chrome_dynlib_vulkan_render` (R3, bounded OUT-byte-buffer facade)
- **Severity:** silent wrong answer; interpreter and native lanes disagreed on the same source

## Symptom

`spl_wffi_call_i64_into_bytes(..., &mut buf, ..., &mut out_len, ...)` returned the
provider's real status and the provider demonstrably wrote through the pointers it was
given (`reported=19` captured in the runtime), yet in Simple `out_len` was still `-1` and
`buf` still held its pre-call sentinel. A caller could not tell "the provider refused"
from "the provider filled my buffer".

## Root cause

`UnaryOp::RefMut` evaluates its operand to a **copy** and wraps that copy:

- `src/compiler_rust/compiler/src/interpreter/expr/ops.rs:1575`
- `src/compiler_rust/compiler/src/interpreter/expr/ops.rs:1660`

both `Value::BorrowMut(BorrowMutValue::new(val))`. `BorrowMutValue` shares an
`Arc<RwLock<Value>>`, so a callee's write is visible *through that borrow* — but nothing
ever published it back to the named variable's slot in the environment. `&mut` was
therefore decorative in interpreter mode, and every extern out slot was silently dead
there, including `spl_wffi_try_call_i64_out`'s `*mut i64` (which is why
`src/lib/nogc_sync_mut/sffi/dynamic.spl` carries a `_sffi_out_slot_supported` hedge).

The native lane never had this gap: there `&mut i64` is a real pointer and a `[u8]` is a
heap `RuntimeArray` mutated in place by `byte_array_write`.

## Fix

`call_extern_function` (`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`) now
publishes the borrow back after the call: for each argument whose expression is
`Unary { RefMut, Identifier }` and whose value is `Value::BorrowMut`, the borrow's current
inner value is assigned to that variable. Only `&mut <identifier>` is written back — a
borrow of a temporary has no slot to write to — and nothing else is touched.

## Specs

- `test/01_unit/lib/sffi/wffi_into_bytes_spec.spl` — 5 examples, 0 failures. Drives a real
  loaded provider (the stub `libsimple_chrome_render`) and asserts the bytes and `out_len`
  that come back, the untouched sentinel past the declared capacity, the zero-capacity
  case, and the fail-closed refusal of a window past the allocation.
- `src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs` tests
  `bounded_out_buffer_*` — 6 tests, including the `(k * 7) & 0xff` fill pattern, the
  capacity bound, the offset window, and the refusal of an unborrowed out buffer.

Sabotage (green/red/green): making the interpreter hand the provider the whole allocation
length instead of the declared `capacity` turns the spec red at 2 of 5 examples
("writes nothing at all when the capacity is zero", "never writes past the declared
capacity"); restoring `capacity` returns it to 5/5.

## Not verified here

The native lane's lowering of a `&mut [u8]` extern parameter. The spec above runs under
`SIMPLE_EXECUTION_MODE=interpreter` only.
