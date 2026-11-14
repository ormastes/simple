# Slang prefix cache gave back reuse on CPU-only llama.cpp (offload misdetect)

Date: 2026-11-14. Status: fixed in the same change (`src/runtime/slang_ggml_shim.c`).

## Symptom

On a CPU-only llama.cpp (Windows, llvm-mingw build, no GPU backend), an exact
repeat of a 988-token prompt re-prefilled **512** tokens instead of 1, so the
snapshot cache that should save ~40x saved 1.8x.

## Cause

`slang_ggml_model_load` set `g_model_offloaded = mp.n_gpu_layers != 0`. The
engine asks for `-1` (all layers) on every host, so the flag was true even
where nothing can be offloaded. That armed the CUDA first-micro-batch
workaround (`slang_request_first_ubatch`, added for the 2026-11-12 GB10 Xid 31
fault): a restore gave reuse back until its suffix was one full `n_ubatch`
(512).

## Fix

`g_model_offloaded = mp.n_gpu_layers != 0 && llama_supports_gpu_offload();`
On a GPU-capable llama.cpp the flag is unchanged by construction. That is
covered only by the mock; no GPU host was run for this change. The mock gained `llama_supports_gpu_offload`
and `test/02_integration/lib/slang_prefix_cache_shim_contract_test.shs` now
has a no-GPU case (`-1` load, full reuse, no throwaway decode). The old shim
fails that case at `prefix_cache_test.c:315`; the fixed one passes.

## Evidence (Qwen2.5-1.5B-Instruct Q4_K_M, n_ctx 2048, seed `bin/simple.exe` sha256 `e1128889...58c5`)

| shim | exact_repeat prompt tokens off -> on | on_ms / off_ms |
|---|---|---|
| before (HEAD) | 988 -> 512 | 27942 / 51170 (1.83x) |
| after | 988 -> 1 | 1344 / 53540 (39.83x), 1193 / 53138 (44.54x) |

## Not covered

`slang_kv_cache_live_spec.spl` does not pin the 1-token figure: on a GPU host
512 is still the correct value by design, and the spec has no offload signal
to tell the two apart. The contract test is the regression. Side effect: with
the fix a CPU hit now recomputes a 1-7 token suffix, which exposes
batch-shape output drift, see
`slang_prefix_cache_hit_output_drift_2026-11-14.md`.
