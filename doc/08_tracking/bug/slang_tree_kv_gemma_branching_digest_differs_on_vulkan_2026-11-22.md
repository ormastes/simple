# Tree KV cache (mode 3): not bit-exact against cache-off on Vulkan (Gemma branching digest differs)

- **Status:** C1 fixed by option (a) (2026-11-23, `slang_ggml_backend_init` sets `GGML_VK_DISABLE_FUSION`); C2 still open, direction (b) below.
- **Found:** 2026-11-22, Windows EVO-X5Pro host, Radeon 8065S through the Vulkan llama.cpp build (`build-mingw-vulkan`, llama.cpp `99b9548`)
- **Seed:** `C:/dev/seeds/simple-release.exe`
- **Spec:** `test/03_system/lib/slang/feature/slang_kv_tree_cache_live_spec.spl` (unchanged; it still fails 2/3 on Gemma on Vulkan)

## Observed

On Vulkan, `gemma-3-270m-it-GGUF` is fully offloaded (19/19 layers).

| workload | lane | prefilled | reused | digest |
|---|---|---|---|---|
| branching | off | 6652 | 0 | 81048996d497 |
| branching | tree | 3068 | 3584 | **4524590e911e** |
| boundary | off / tree | 1987 / 1475 | 0 / 512 | 57f18cb60a04 (equal) |
| multiturn | off / tree | 5295 / 2735 | 0 / 2560 | 695f3acdc604 (equal) |

Request 6 (follow-up 3) is the only request whose text differs. Qwen2.5-1.5B on Vulkan passes 3/3. On the CPU build Gemma branching is digest-equal (`C:/dev/slang-logs/shimtree/tree_spec3.log`); bits there are unmeasured.

## Method

A diagnostic shim printed an FNV hash of the full logits vector at every sample step, with the top-1 token and the top-1/top-2 gap. A diagnostic copy of the live spec printed per-request output digests. Each lane ran in its own load, and every run took the GPU lock. All logs are under `C:/dev/slang-logs/treevk/`; the diagnostic spec is kept there as `treevk_diag_spec.spl`. Steps are counted over the branching workload: 16 warmup steps ("Zebra."), then 16 per request.

## Findings

1. **The shape-split theory is wrong.** Splitting the last prompt token on the cold no-cache path (the earlier WIP) left every per-request digest unchanged in both lanes (`diag_base_gemma_1.log` vs `diag_fix1_gemma_1.log`).
2. **The prefix reuse is not the cause.** Off vs tree, 144 of 144 logits steps differ, including the warmup and cold request 0, which reuse nothing in either lane (`diag2_gemma.log`). With reuse forced off in the tree, the tree lane gives the same bad digest 4524590e911e (`diag2_noreuse_gemma.log`). The off lane is deterministic: two runs match at every step.
3. **Qwen is exact only by luck.** Every logits step differs between its lanes too; greedy argmax just never flips (`v_qwen.log`).
4. **Cause C1: ggml-vulkan fusion depends on the KV stream count.** With `GGML_VK_DISABLE_FUSION=1`, cold request 0 becomes bit-exact off vs tree (steps 17-32), and the off digest moves to the tree's value (`v_GGML_VK_DISABLE_FUSION.log`). `GGML_VK_DISABLE_GRAPH_OPTIMIZE=1` has the same effect (`v_GGML_VK_DISABLE_GRAPH_OPTIMIZE.log`). Both runs report 3/3, but at bit level requests 1-7 still differ, so that pass is luck as well.
   - Proven by the env experiment: fusion changes the off lane's numerics and not the tree's.
   - Inferred from code, no graph dump: with `n_stream > 1`, `llama_kv_cache::cpy_k` (`src/llama-kv-cache.cpp:1349`) inserts a `ggml_reshape_2d` between the K view and `set_rows`. The Vulkan `rms_norm_mul_rope_view_set_rows` / `rope_view_set_rows` matchers then no longer see their pattern, so the one-stream cache-off context runs the fused kernel and the 16-stream tree context does not.
5. **Cause C2: stale K/V data in freed cells changes flash-attention output.** With fusion off and reuse off:
   - requests 0-4 are bit-exact;
   - requests 5-7 differ (`v_nofusion_noreuse.log`). They ran on seqs 1-3, whose streams had earlier held longer requests, and the stale cells sit past the new request's frontier inside `n_kv`;
   - request 4 ran on seq 0, whose earlier contents (the warm-up) lay below the new frontier and were overwritten, and it is exact.

   Zeroing the stream first (a cross-stream `seq_cp` from a never-used seq) makes requests 0-7 all bit-exact (`v_nofusion_noreuse_zero.log`). Under reuse, `seq_cp` copies the owner's whole stream, including its tail past `reuse`, so every reused request carries stale data past its frontier.
   - Proven: masked cells within `n_kv` affect the result.
   - Not identified: the shader-level mechanism (the `-inf` mask should zero those terms).

## Fix options (owner decision)

- **(a)** Set `GGML_VK_DISABLE_FUSION` process-wide before Vulkan device init. This fixes C1 only. It costs about 6% wall time (branching off 1293 -> 1373 ms, tree 720 -> 749 ms) for every Vulkan model in the process.
- **(b)** Per tree request, zero the destination stream from a pristine seq, then restore the reused prefix with a host `llama_state_seq_get_data` / `set_data` round-trip instead of the whole-stream `seq_cp`. This fixes C2. It is untested and costs a host copy of the reused KV on every hit.
- **(c)** Upstream fix in llama.cpp/ggml-vulkan: accept the reshape in the fusion matchers when a ubatch uses one stream, and make flash attention independent of masked-cell data.

Exactness needs (a or c) plus (b or c). Until then mode 3 is digest-equal to cache-off on the CPU build only. On Vulkan it gives the same text only while greedy argmax happens not to flip. The live spec's digest check is not evidence of bit exactness on a GPU. Only branching was compared at bit level; boundary and multiturn are digest-only.

## Resolution of C1 (2026-11-23, option (a))

`slang_ggml_backend_init` (`src/runtime/slang_ggml_shim.c`) sets `GGML_VK_DISABLE_FUSION=1` before `llama_backend_init`, so it runs before any ggml-vulkan device exists (the device reads the variable once and is kept for the process). It is set at backend init rather than at mode-3 configure because the cache mode can be configured after a cache-off load in the same process, and the device would then already be fused. A value already in the environment wins. The cost is process-wide, as option (a) states.

- Spec `slang_kv_tree_cache_live_spec.spl` on gemma-3-270m-it, Vulkan, seed `simple-release.exe`: old shim `4 total, 2 passed, 2 failed` (branching digest 81048996d497 vs 4524590e911e, and the new fusion example), `C:/dev/slang-logs/treevk-a/old_gemma.log`; new shim `4 total, 4 passed, 0 failed`, branching off and tree both 4524590e911e, `C:/dev/slang-logs/treevk-a/new_gemma.log`.
- Perf, one paired run, wall ms old -> new (off/tree): branching 1342/727 -> 1231/628, boundary 296/156 -> 257/121, multiturn 1021/569 -> 1075/491. This run shows no slowdown above host noise (the host is shared); the earlier controlled measurement was about +6% (1293 -> 1373 ms off, 720 -> 749 ms tree). Repeat runs were not possible: `C:/dev/seeds` disappeared mid-session. The cost is documented, not fixed.
- C2 stays open: exactness on Vulkan still needs option (b) (zero the destination stream from a pristine seq and restore the reused prefix by host `llama_state_seq_get_data`/`set_data`) or (c). The spec's digest check is still argmax-level, not bit-level.
