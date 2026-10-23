# `rt_array_set_len_known` interpreter binding is a no-op stub: arrays never shrink
## Open 2026-10-22 — filed by cipher-b lane (key session lane, SQLCipher 4 codec)

- Date: 2026-10-22
- Status: **OPEN** — lane-local workaround in place
- Severity: low-medium — any Simple code relying on in-place array truncation
  silently keeps the full buffer in the seed interpreter (`bin/simple test`)

## Symptom

`std.common.crypto.secure_memory.secure_set_u8_length(bytes, 0)` returns
`true`, but `bytes.len()` is unchanged afterwards. Minimal repro
(interpreter mode):

```simple
use std.common.crypto.secure_memory.{secure_set_u8_length}
val b: [u8] = [7u8, 8u8]
secure_set_u8_length(b, 0)   # -> true
# b.len() == 2, expected 0
```

Observed while landing the SQLCipher 4 key-session lane
(`src/lib/nogc_sync_mut/database/codec/sqlcipher4_keys.spl`): the session
`close()` truncate step reported success yet the buffers stayed 32 bytes.

## Root cause

The interpreter extern registry
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:690`) maps
`rt_array_set_len_known` to `sffi_array::rt_array_set_len_known_fn`, whose
entire body is:

```rust
pub fn rt_array_set_len_known_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1))
}
```

(`src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs:75-77`)

The arguments are ignored: no length is mutated, and the unconditional
`Int(1)` reports success. The native runtime symbol does perform the
mutation (`common/src/runtime_symbols.rs:1532`), so native-linked builds
behave correctly — the gap is interpreter-only, which is why no
interpreter-mode test caught it.

Related gap, same owner module: the `[u8]` zeroization path
(`secure_zero_u8_slots`) is unusable in the interpreter because it calls the
unregistered extern `rt_array_data_ptr_text` — see
`secure_memory_u8_zeroize_unregistered_extern_2026-10-22.md`.

## Impact

- Callers that truncate a secret buffer after zeroizing it (the documented
  secure-memory usage pattern) silently keep the full allocation alive in
  interpreter mode. Content is still zeroed, but the "release the buffer"
  step is a no-op.
- Anything else using `rt_array_set_len_known` / `rt_array_set_len_known_text`
  in the interpreter is similarly affected.

## Workaround (lane-local, minimal)

The cipher-b key-session lane does not depend on truncation: `close()`
replaces the wiped key fields with fresh empty arrays
(`self.page_key = []`), which releases the reference in every runtime. When
this stub is implemented, the lane can additionally call
`secure_set_u8_length` for in-place shrink if desired.

## Suggested fix (compiler owner)

Implement `rt_array_set_len_known_fn` for the interpreter: extract the array
and length arguments, apply `Arc::make_mut` + `Vec::truncate`/`resize`, and
return `1` only when the new length fits the current capacity (or define and
document the growth semantics). Add an interpreter-mode unit test that
truncates a 2-element `[u8]` to 0 and asserts the length.
