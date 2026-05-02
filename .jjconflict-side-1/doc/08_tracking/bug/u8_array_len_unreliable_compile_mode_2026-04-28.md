# Bug: `[u8].len()` returns 0 on push-built arrays in compile mode

**Date:** 2026-04-28
**Severity:** correctness — silently truncates byte arrays in baremetal Cranelift builds
**Discovered by:** TLS live-lane bisection (`/dev tls_live_bug_fix_restart`, round 2)

## Symptom

In compile-mode (Cranelift bare-metal `x86_64-unknown-none`), calling `.len()` on a push-built `[u8]` array returns 0 (or some unreliable small value), even when the array has been populated correctly.

Example, simplified from the original A2 reproduction:

```
var abc: [u8] = []
abc.push(0x61u8)
abc.push(0x62u8)
abc.push(0x63u8)
# abc now contains [0x61, 0x62, 0x63] semantically
val len = abc.len()  # returns 0 in compile mode (expected 3)
```

When `.len()` returns 0, downstream loops over `data_len = abc.len()` execute zero iterations, silently producing empty/wrong outputs. This is what kept HKDF-Expand returning `sha256("")` instead of the RFC-correct value.

## Reproduction

Any compile-mode test that:
1. Builds a `[u8]` via `var x: [u8] = []` then `x.push(byte)` calls
2. Calls `x.len()` to drive a loop or pass a length parameter

Particularly visible in `sha256(data)` → `sha256_with_len(data, data.len().to_u64())` — `data.len()` returns 0 for push-built `data`.

## Root cause hypothesis (not confirmed)

`.len()` in compile-mode probably calls `rt_len(RuntimeValue) -> RuntimeValue` (defined in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c:892`). For runtime-allocated arrays (returned by `_tls_runtime_array_from_bytes` etc.), the header `RuntimeArray->len` is correctly set. For Simple-side push-built arrays, the runtime header may not be properly maintained, or the unbox/tag handling of `rt_len`'s return value fails.

In contrast, `.len()` works correctly on arrays that came back from C externs (verified — `fast_inner.len()` reads the right value when `fast_inner` is from `rt_tls13_aes128_gcm_decrypt`).

## Workaround in tree (2026-04-28)

- Pass explicit lengths as separate `data_len: u64` parameters wherever possible.
- `_record_unpack_inner_with_len(inner, inner_len)` in `src/os/tls13/record13.spl` accepts an explicit length.
- Use runtime-allocated arrays from C externs whenever the result needs `.len()` later (`rt_tls13_sha256`, `rt_tls13_record_decrypt_compact`, etc., all return runtime-allocated arrays with correct headers).
- Avoid `.len()` on push-built arrays in compile-mode-critical paths.

## Why root-cause fix matters

Forces every `.len()`-using algorithm in baremetal to be rewritten with explicit lengths or to round-trip through C externs. Adds API friction. Any pure-Simple data-structure work in compile mode is at risk of silently broken length tracking.

## Investigation pointers

Look at:
- `rt_array_new_with_cap` allocation path
- Push-arr `len` field maintenance in compile-mode codegen
- `MirInst::ArrayPush` lowering and the resulting Cranelift code
- The interaction between `rt_len` extern and the tagged-int unbox at the call site
