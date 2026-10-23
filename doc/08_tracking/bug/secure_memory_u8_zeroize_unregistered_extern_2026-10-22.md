# `secure_memory.secure_zero_u8_slots` dies in the seed interpreter: unregistered extern `rt_array_data_ptr_text`
## Open 2026-10-22 — filed by cipher-b lane (key session lane, SQLCipher 4 codec)

- Date: 2026-10-22
- Status: **OPEN** — lane-local workaround in place; canonical owner unchanged
- Severity: medium — secret-zeroization API is unusable in `bin/simple test`
  (interpreter mode) for every `[u8]` caller; the `[i64]` path is unaffected

## Symptom

Any Simple code path that calls
`std.common.crypto.secure_memory.secure_zero_u8_slots` (or
`secure_zero_u8_range`) under the seed interpreter fails at runtime with:

```
semantic: unknown extern function: rt_array_data_ptr_text
```

Observed while landing the SQLCipher 4 key-session lane
(`src/lib/nogc_sync_mut/database/codec/sqlcipher4_keys.spl`): 9 of 18 spec
examples failed with exactly this error the moment session `close()`
reached the zeroization owner.

## Root cause

`src/lib/common/crypto/secure_memory.spl:10` declares

```simple
extern fn rt_array_data_ptr_text(collection: [u8]) -> i64
```

and `secure_zero_u8_range` (line 74) calls it to obtain the buffer's data
pointer for the volatile write/readback loop.

The seed interpreter's extern registry
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`) registers the
generic twin only:

```rust
insert_simple!("rt_array_data_ptr", memory::rt_array_data_ptr);   // line 2007
```

`memory::rt_array_data_ptr` already accepts `Value::ByteArray` and returns
the real data pointer (`interpreter_extern/memory.rs:1859-1867`), so the
`_text` variant is redundant in the interpreter — but `secure_memory.spl`
calls the unregistered name. `rt_array_data_ptr_text` exists only in the
native link symbol tables (`common/src/runtime_symbols.rs:143`, and the
runtime_sffi spec at `compiler/src/codegen/runtime_sffi.rs:869`), so the
`[u8]` zeroization path presumably works only in native-linked builds and
has no interpreter-mode test coverage at this base — which is why the gap
was not caught.

The `[i64]` path (`secure_zero_i64_slots`) calls the registered
`rt_array_data_ptr` and is unaffected.

## Impact

- Every interpreter-mode caller of the `[u8]` zeroization API fails closed
  (loud error, no wipe performed). Failing closed is safe for correctness
  but blocks secret-hygiene features in exactly the mode used by
  `bin/simple test`.
- Native/SMF builds are unaffected (symbol present in the link tables).

## Workaround (lane-local, minimal)

The cipher-b key-session lane does not call the broken owner. It implements
overwrite-with-readback verification over plain element stores
(`_sqlcipher4_zeroize_u8` in `sqlcipher4_keys.spl`) — the same idiom
`x25519_mlkem768/raw_workload_binding.spl::_raw_wipe` already uses. This is
portable (interpreter + native) but not MMIO-volatile; the readback loop
makes every write observable. When this bug is fixed, the lane should switch
back to the canonical owner `secure_memory.secure_zero_u8_slots`.

## Suggested fix (compiler owner)

Register the alias in the interpreter extern table, or repoint
`secure_memory.spl` at the already-registered `rt_array_data_ptr` (which
accepts `Value::ByteArray`):

```rust
insert_simple!("rt_array_data_ptr_text", memory::rt_array_data_ptr);
```

and add an interpreter-mode unit test that wipes a non-empty `[u8]` buffer
and asserts `SecureZeroReport.verified()`.
