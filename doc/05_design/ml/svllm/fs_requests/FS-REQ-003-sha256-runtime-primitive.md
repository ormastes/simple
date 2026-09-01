# FS-REQ-003: working SHA-256 runtime primitive

- **Date:** 2026-04-18
- **svllm phase:** A2
- **Triggering code:** `src/lib/gc_async_mut/svllm/model_executor/model_loader/tensor_pack.spl:sha256_chunk`,
  `src/app/svllm_pack/main.spl:_do_pack`
- **Need (API or semantic):** a runtime-side `rt_sha256_bytes(bytes: [u8]) -> [u8]`
  (or `rt_sha256_hex(bytes: [u8]) -> text`) extern that returns a correct
  SHA-256 digest in both interpreter and compiled modes. Current options:
  - `std.common.crypto.sha256.sha256_bytes` (pure Simple): **broken under the
    Rust-seed interpreter**; returns a deterministic-but-wrong 32-byte list
    (e.g. `0x11, 0x11, 0x11, ...`) for any input. Likely an i32 vs i64 bit-op
    issue in the `rotr32`/`sigma` helpers when the interpreter infers i64.
  - `rt_file_hash_sha256(path)` extern: **stub only** — returns a 16-char
    string, not a real digest.
- **Current workaround:** `svllm_pack` shells out to `sha256sum <path>` via
  `rt_process_run`. Adds a per-chunk subprocess fork (~1ms) and assumes
  `sha256sum` is on $PATH (Linux/macOS ok; Windows needs a shim). Unusable
  in SimpleOS userland where fork is unavailable.
- **Measured impact:** adds ≈2–5ms of process-spawn overhead per chunk during
  pack. Blocks A3 load-side verify + any in-SimpleOS packing.
- **Proposed mapping:** wire `rt_sha256_bytes` in `src/runtime/runtime.c`
  backed by OpenSSL (when linked) or the pure-C fallback the SimpleOS kernel
  already ships. Expose under `std.nogc_sync_mut.ffi.crypto`.
- **Priority:** P1 (A2 works but is not portable; A3 will need correct
  per-chunk verify at load time).
- **Status:** open
