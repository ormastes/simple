# Seed interpreter: `&mut` out-param writeback loss and `[u8].data_ptr()` pointing at boxed value cells

- **Filed:** 2026-08-31
- **Status:** FIXED 2026-11-06 — gap 1 already fixed upstream, gap 2 fixed in `work/seed-interp-batch2-20261106` (see "Resolution"); re-verified 2026-11-11 (lane interp12) on fresh seed 46fe8f6b6def, both gaps green (see "Addendum 2026-11-11"); originally: two distinct seed-interpreter ABI gaps,
  in-tree workarounds landed at the two call sites that blocked the UI showcase
- **Platform:** aarch64-apple-darwin (likely all platforms; untested elsewhere)
- **Found during:** UI showcase real-launch sweep (2d / 2d-metal / web / gui / wm)

## Gap 1 — `&mut` out-param writeback lost for extern fns

**Symptom:** `spl_dlopen_checked(path, &mut handle)` returns status 0 (success)
while `handle` stays 0. The Rust-side `Value::BorrowMut` write in
`wsffi::spl_dlopen_checked` never reaches the caller's Simple `var`.

**Repro:** declare the two externs, call them on any loadable dylib:
`spl_dlopen(path)` returns a valid handle; `spl_dlopen_checked(path, &mut h)`
returns `status=0 handle=0`.

**Workaround (landed):** `src/lib/nogc_sync_mut/sffi/dynamic.spl`
(`_sffi_dlopen_checked`, `_sffi_dlsym_checked`) detects the writeback-loss
signature (`status == 0` with out-param still 0 — unreachable from a genuine
success) and falls back to the direct-return `spl_dlopen` / `spl_dlsym` ABI,
which works in both lanes. Compiled-mode behavior is unchanged.

**Proper fix direction:** argument writeback for `&mut` parameters on the
extern-call path (Priority-1 `call_extern_function` in
`src/compiler_rust/compiler/src/interpreter_call/mod.rs`): the evaluated
`&mut x` argument must alias the caller's env slot, not a temporary.

## Gap 2 — `[u8].data_ptr()` is not a packed-byte pointer in the interpreter

**Symptom:** `[u8].data_ptr()` returns an address whose first bytes read back
as tagged value cells (e.g. `0x8000000000000001`), not the packed byte
payload. Any kernel/FFI consumer of that pointer reads garbage and — for
Metal compute kernels whose parameter struct starts with validity guards —
silently no-ops while every status reports success.

**Repro:** `val a: [u8] = [1u8, 2u8, 3u8, 4u8]` then read the first i64 at
`a.data_ptr()` via `rt_ptr_read_i64`: observed `0x8000000000000001` (tagged
cell), not `0x0000000004030201` (packed bytes). `handle_byte_array_methods`
in `interpreter_method/collections.rs` has no `data_ptr` arm, so the call
widens to the `Vec<Value>` array handler and returns `Vec::as_ptr()` — a
pointer to boxed `Value` cells.

**Observed consequence:** the Metal font-atlas composite kernel
(`simple_font_atlas_composite_v1_u32`) received garbage params, every guard
fell through, and TTF text never reached the framebuffer while
`drawn=true`/`device_readback` were all reported.

**Workaround (landed):** `src/lib/nogc_sync_mut/io/metal_sffi.spl`
(`metal_sffi_run_compute_frame`) marshals `params: [u8]` into a real
`rt_alloc` host buffer (i32 LE packing via `rt_ptr_write_i32`) and frees it
after submission — the same pattern `backend_metal.spl` already uses for its
hand-rolled dispatches. NOTE for future editors: Simple `or` is boolean, not
bitwise — an early version of the marshal wrote `true` for every nonzero
word; use `|` for byte packing.

**Proper fix direction:** give `Value::ByteArray` / `FrozenByteArray` a real
`data_ptr` that returns the packed `Vec<u8>` pointer (and decide the
contract for `Value::Array`, where no packed form exists — currently it
silently returns a `Vec<Value>` pointer, which is equally invalid as a byte
buffer).

## Related landed fixes from the same sweep

- `interpreter_call/mod.rs` overload scoring: trait-impl-aware type match via
  `TRAIT_IMPLS`, `Any` matches any value, `ByteArray` matches `[u8]` params,
  defaulted parameters are optional in the arity check. These unblocked every
  `no caller-authorized overload of … matches the supplied arguments` failure
  (`showcase_run`, `compute_layout`, `mutex_new`, …).
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`: four Metal sites bound the
  whole `MetalBackend?` Option and re-wrapped it (`self.metal_backend =
  Some(metal)` with `metal` already `Some(..)`), producing `Some(Some(..))`
  per call and eventual `'session' on Option` failures; converted to the
  destructure idiom the Vulkan twin documents.
- Seed Metal feature chain: `simple-driver/metal` ->
  `simple-compiler/metal` -> `simple-runtime/metal`; plus registration of the
  `rt_metal_buffer_upload_raw` / `rt_metal_buffer_download_raw` /
  `rt_metal_set_bytes_raw` externs.
- `src/app/ui_showcase/showcase_core.spl`: `_actionable_target` now arms
  clicks on menubar items (Text-kind children of the toolbar), so the
  toolbar is clickable as the design intends and the hosts spec's
  `click 20,10` contract holds.

## Resolution (2026-11-06)

Measured with `test/fixtures/seed_interp/mut_out_param_and_data_ptr_repro.spl`
(Windows, `SIMPLE_EXECUTION_MODE=interpret`, loads `kernel32.dll`).

- **Gap 1 — already fixed.** On a seed built from `release/1.0.0` @
  `ecb705896a4` the base prints `out_param status=0 handle_nonzero=true`:
  the extern's `&mut` write reaches the caller's `var`. The fallback in
  `src/lib/nogc_sync_mut/sffi/dynamic.spl` stays: it also covers the
  separate JIT out-slot defect
  (`jit_refmut_extern_out_param_passes_value_not_address_2026-10-05.md`).
- **Gap 2 — fixed.** `interpreter_method/collections.rs`
  `handle_byte_array_methods` now answers `ptr` / `data_ptr` from the packed
  fast path with the `Arc<Vec<u8>>` payload pointer (the same address
  `rt_array_data_ptr` returns), instead of widening to `Vec<Value>` and
  returning that temporary's cell pointer. The contract for a boxed
  `Value::Array` (no packed form) is unchanged and remains an owner decision.
  Before: `data_ptr word=3455309644288` (not the bytes; the widened buffer
  was already freed). After: `data_ptr word=67305985` (`0x04030201`).
  Rust test
  `interpreter_method::collections::byte_array_metadata_fast_path_tests::byte_array_data_ptr_addresses_the_packed_payload`:
  FAILED before (`data_ptr must return the packed byte pointer`, left/right
  differ), ok after. The `metal_sffi.spl` host-buffer marshal is not
  reverted here (no Metal host to verify it on).


## Addendum 2026-11-11 (lane interp12) — re-verified FIXED on fresh seed 46fe8f6b6def

**Verification actually run** (worktree simple-p3-interp12-20261111, seed-smoke):

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe SIMPLE_EXECUTION_MODE=interpret \
  ./bin/simple.exe run test/fixtures/seed_interp/mut_out_param_and_data_ptr_repro.spl --no-cache
# out_param status=0 handle_nonzero=true
# data_ptr word=67305985        (rc=0)
```

Gap 1 (`&mut` extern out-param writeback reaches the caller's `var`) and gap 2
(`[u8].data_ptr()` addresses the packed bytes, `0x04030201`) both print the
documented fixed values on the current tracked seed. Verdict: STALE (fix
previously landed; no new code change this lane). Note: `simple run` selects
the engine via `SIMPLE_EXECUTION_MODE`, not a `--mode` flag — passing
`--mode=interpreter` to `run` leaves the default hybrid lane and reproduces a
spurious `Array.data_ptr not found`; that routing artifact is not this bug.
