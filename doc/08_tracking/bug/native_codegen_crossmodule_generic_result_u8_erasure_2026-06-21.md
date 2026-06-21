# Native codegen: cross-module `Result<[u8], E>` payload type-erasure crashes

**Filed:** 2026-06-21 (Round 9)
**Status:** Open — root cause precisely located; needs a self-hosted backend
codegen fix + `bin/simple` rebuild (deferred; not deployable this round).
**Priority:** P1
**Blocks:** un-gating the svllm FS byte-value tests
(`test/01_unit/lib/nogc_async_mut/svllm/nvfs_client/std_fs_transport_spec.spl`,
`test/03_system/tools/svllm_fs_loader_system_spec.spl`).
**Related:** `native_sffi_file_byte_io_u8_marshalling_2026-06-20.md` (the rt_file
byte primitives themselves are fixed/proven; this is the downstream generic
codegen gap that doc's "Remaining" section pointed at).

## Summary

Under native AOT (`bin/simple test --compile`, the self-hosted backend), values
of type `[u8]` that pass through a **cross-module** generic `Result<[u8], E>`
lose their static element type. The backend then lowers operations on the
recovered payload through a dynamic path whose helpers are unlinked, producing
`call 0x0` SIGSEGVs and `function not found` runtime errors. The interpreter
path is correct; the direct, same-module, statically-typed `[u8]` path is
correct (it inlines to direct byte loads — see the passing
`test/01_unit/lib/nogc_sync_mut/sffi/native_byte_io_spec.spl`).

Three distinct manifestations, all from the same erasure root, observed to be
**compilation-unit-dependent** (they appear once enough cross-module generic
instantiations coexist in one `--compile` unit; they do not reproduce in a
minimal isolated unit):

1. **Erased payload index → null convert.** `match r: Ok(d) => d[0] as i64`
   on a cross-module `Result<[u8], NvfsError>` crashes. Disassembly:
   `rt_enum_payload` (extract Ok payload, returns a type-erased value) →
   `rt_index_get` (generic boxed index) → `call *[0x407f78]` where that
   `_DYNAMIC` GOT slot holds **NULL**. The post-index integer-convert/unbox
   helper was never linked. `.len()` on the same payload works; only the index
   crashes. Re-typing the payload first — `var d2: [u8] = d; d2[0]` — restores
   the static, inlined byte load and works (the array data is intact; this is a
   lowering-selection bug, not data corruption).

2. **Cross-module `Result` method dispatch mis-resolves.** `r.is_ok()` /
   `r.is_err()` / `r.unwrap()` on a cross-module `Result<[u8], NvfsError>` print
   `Simple runtime error: function not found: is_err` and return garbage
   (observed `is_err()` → `3`) or `call 0x0`, in large units. The same methods
   resolve correctly in small units and on `Result<text, _>` /
   `Result<Struct, _>` — i.e. the method instance for the `[u8]` payload
   instantiation is dropped from the registry depending on unit content
   (monomorphization registration gap).

3. **Array-data-pointer corruption through the streaming path.** After the
   `Result<[u8]>` payload is `match`-bound and `push`ed into a typed
   `[[u8]]` container and consumed by the streaming loader, the inline byte
   load in `streamer.stream_pack` (`movzbq (%rax,%rsi,1)`, data ptr from
   `0x18(%r11)`) faults — the chunk buffer's data pointer is invalid. So the
   re-type-through-container trick that fixes (1) in a leaf expression does
   **not** fully rehabilitate the buffer once it crosses module + generic +
   container + a second cross-module consumer.

## Reproduction

Minimal (manifestation 1), under `--compile --force-rebuild`:

```
fn wrap(p: text) -> Result<[u8], i64>: Ok(file_read_bytes(p))   # same-module: OK
# cross-module StdFsNvfsClient.read_bytes(...) -> Result<[u8], NvfsError>:
val r = client.read_bytes(path)
match r:
    Ok(d) => d[0] as i64    # SIGSEGV (call *[null]); d.len() is fine
    Err(_) => 0
```

Full production happy path (manifestations 2 + 3): drive
`load_model_from_pack_fs(client, pack_root, 0)` against a valid on-disk pack
(manifest + non-empty `data-000.bin`) under `--compile`. Before the Round-9
transport hardening it crashed on `is_err`; after it, it reaches
`stream_pack` and faults there (manifestation 3).

Backtrace (manifestation 3):
`stream_pack` ← `load_model_from_pack_streamed` ← `load_model_from_pack_fs` ←
`spl_main`.

## Round-9 mitigation (landed)

`src/lib/nogc_async_mut/svllm/nvfs_client/std_fs_transport.spl` —
`load_model_from_pack_fs` rewritten to destructure every `Result` with `match`
instead of `is_err()` / `unwrap()`, eliminating manifestation 2 from the
production transport. Logic is equivalent (early-out on first failed chunk via a
`chunk_failed` flag + loop guard); chunk payloads land in the typed `[[u8]]`
container. Verified non-regressive: error-path tests 17/0 and the FS loader
system spec 6/0 still pass under `--compile`. This is pure library Simple source
(recompiled per build) — **no bootstrap**.

This does **not** unblock the byte-value tests: manifestations 1 and 3 are
backend codegen bugs that require the self-hosted backend to preserve the
`[u8]` element type across enum-payload extraction (so index lowers to the
inlined static load) and to register the cross-module generic method/convert
instances. Those byte tests stay gated (`native_u8_fixed = 0`) with a pointer
here.

## Proposed fix (deferred — needs backend + `bin/simple` rebuild)

In the self-hosted backend (`src/compiler/70.backend`, with the type info from
`src/compiler/30.types`): when extracting a generic enum payload
(`rt_enum_payload`) whose monomorphized type is a concrete array (`[u8]`),
carry that static type to the use sites so index/convert lower to the same
inlined path the direct `[u8]` case uses, and ensure the per-instantiation
method/convert symbols are emitted+linked for cross-module generic
`Result<[u8], E>`. Rebuild + deploy `bin/simple`; re-verify by flipping
`native_u8_fixed` to `1` in both gated specs and the happy-path driver.
Note: full bootstrap currently fails Stage-3 self-host (separate tracked issue),
so this fix must validate its rebuild/deploy path first.
