# svllm NvfsClient transport for load_model_from_pack

**Filed:** 2026-06-20
**Updated:** 2026-06-20 (in-memory transport landed)
**Status:** partial — in-memory adapter done; read-capable std.fs/native adapter pending
**Priority:** P2

## Summary

The Phase A3 streaming-loader **logic** is implemented and tested:
`load_model_from_pack_streamed(pack_root, manifest_text, granule, chunk_data)`
parses the manifest, builds the `TensorPack`, plans the aligned read schedule
(`plan_stream`), and gathers per-tensor bytes (`stream_pack`).

What is still deferred is the **transport** that feeds it: the bare entry
`load_model_from_pack(pack_root)` returns `Err(LoaderError.NvfsUnavailable)`
because there is no wired `NvfsClient` adapter to:

1. open the pack root and `manifest.sdn` object,
2. `read_range` the manifest bytes → `manifest_text`,
3. open each chunk object and `read_range` its bytes into registered buffers →
   `chunk_data`,

and then delegate to `load_model_from_pack_streamed`.

## Root Cause

`NvfsClient` is a trait (`std.*.svllm.nvfs_client`) with no concrete adapter
selected here. The FAT32 bring-up adapter and the canonical nvfs adapter live
in the parallel nvfs design; the loader intentionally does not pick one so it
stays portable (see `model_loader/__init__.spl` header).

## Fix Options

1. Add `load_model_from_pack_with_client(client: NvfsClient, pack_root)` that
   performs steps 1–3 above and calls `load_model_from_pack_streamed`. Test it
   with an in-memory `NvfsClient` adapter (also useful for bring-up).
2. Wire the bare `load_model_from_pack` to a default std.fs adapter once the
   nvfs FAT32 bring-up adapter is stable.

## Status

Partial. Streaming logic complete (`streamer.spl`, `loader.spl`). The **in-memory
transport** is now implemented (`transport.spl`): `MemNvfsClient` +
`load_model_from_pack_via` fetch the manifest text + chunk bytes off an in-memory
image and drive the streaming loader end to end (Option 1, in-memory variant).

Remaining: a **read-capable std.fs / native adapter**. The std.fs bring-up
adapter's `read_range` returns `Unsupported`, and the real `NvfsClient` contract
reads ranges into registered `BufHandle` buffers — a *different* entry shape than
`MemNvfsClient`'s `read_text`/`read_bytes`, so it needs its own transport entry
(not a drop-in). That adapter + entry is the open work.
