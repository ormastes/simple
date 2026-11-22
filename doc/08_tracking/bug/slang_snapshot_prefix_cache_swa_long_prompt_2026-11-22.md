# slang snapshot prefix cache reuses nothing on an SWA model once the prompt passes the window

Date: 2026-11-22. Status: open. Found by the system spec
`test/03_system/lib/slang/feature/slang_system_all_kinds_live_spec.spl`, which now keeps
its KV prompt under the window.

## Symptom
Model: Gemma-3-270m-it (`n_swa = 512`). Setup: Vulkan, shim `slang_ggml`, snapshot mode
(default). A 618-token chat prompt is sent twice with the cache on. Both requests show
`hits=0` and `reused_tokens=0`, and `restore_failures` goes up by one on every repeat.
The answers are still correct.
Log: `C:/dev/slang-logs/systest/run1.log`, `C:/dev/slang-logs/systest/probe.txt`.
The 2026-11-19 tree-cache record already saw 4-5 `restore_failures` per run on Gemma-3.

## Mechanism
1. The context is built with a full-size SWA cache (`llama_kv_cache_iswa: using
   full-size SWA cache`), so admission sees positions 0..617 and stores a snapshot.
2. `llama_state_seq_get_data(ctx, ..., seq 0)` leaves out every SWA-masked cell, even
   with `swa_full` (llama.cpp 99b9548, `llama-kv-cache.cpp` around line 2094). The
   snapshot's SWA layers keep only positions `>= token_count - n_swa`.
3. `slang_request_prefix_prepare_locked` gives reuse back to `tok_len - n_ubatch` (the
   first-micro-batch workaround for a fresh, offloaded context). It then calls
   `slang_request_kv_holds(reuse)`, which needs `seq_pos_min == 0`. The iSWA
   `seq_pos_min` reports the SWA cache, which no longer starts at 0, so the restore is
   refused and the entry is marked unavailable.
4. Refusing is the correct outcome. Decoding from `tok_len - n_ubatch` would need SWA
   cells that the snapshot does not hold.

For an SWA model, a snapshot can only resume at `token_count - 1`. That conflicts with
the give-back on every fresh offloaded context, because each router request opens a new
context.

## Effect
- Exact repeats of prompts longer than `n_swa` on SWA models (Gemma-2/3 and others)
  never hit.
- Each such request still admits a snapshot (about 10 MB here) that can never be
  restored.

## Open
Pick one fix and add a mock test that fails on today's code:
- skip admission when `llama_model_n_swa(model) > 0 && tok_len > n_swa`; or
- warm the fresh context before the restore and resume at `token_count - 1`, accepting
  the throwaway micro-batch; or
- route SWA models to the tree mode-3 cache.

Any restore fix must also prove output stays byte-equal to cache-off. Attention shape
caused drift before: `slang_shim_tree_kv_unified_modes_not_exact_2026-11-19.md`.

## Related finding: video context overflow on square frames
SmolVLM2-256M-Video upscales every sampled frame and tiles it at 512 px.
- A square frame becomes a 4x4 grid plus an overview: 17 x 64 = 1088 positions.
- The default 4 frames overflow the 4096 context, and the router answers HTTP 503
  `model_not_runnable` ("prompt plus generation exceeds the context window").
- A 4:3 frame becomes a 4x3 grid plus an overview: 13 x 64 positions, which fits.

`VIDEO_FRAME_EDGE = 384` in `video_frames.spl` does not bound the token cost, because
the preprocessor upscales the frame first. Open:
- cap the frame count by the context;
- answer 400 (`context_length_exceeded`) instead of 503 for a prompt the client made
  too large.
