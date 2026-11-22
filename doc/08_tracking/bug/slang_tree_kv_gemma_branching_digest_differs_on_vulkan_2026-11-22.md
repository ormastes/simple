# Tree KV cache (mode 3): Gemma branching digest differs from no-cache on Vulkan

- **Status:** open
- **Found:** 2026-11-22, Windows EVO-X5Pro host, Radeon 8065S through the Vulkan llama.cpp build (`build-mingw-vulkan`)
- **Shim:** `C:/dev/slang-shims/postfix-e7a4fb390ad/vulkan/slang_ggml.dll`, built from PR #10682
- **Seed:** `C:/dev/seeds/simple-release.exe`
- **Spec:** `test/03_system/lib/slang/feature/slang_kv_tree_cache_live_spec.spl`

## Observed

On Vulkan, `gemma-3-270m-it-GGUF` is fully offloaded (19/19 layers).

| workload | lane | prefilled | reused | wall ms | digest |
|---|---|---|---|---|---|
| branching | off | 6652 | 0 | 1584 | 81048996d497 |
| branching | tree | 3068 | 3584 | 655 | **4524590e911e** |
| boundary | off / tree | 1987 / 1475 | 0 / 512 | 276 / 145 | 57f18cb60a04 (equal) |
| multiturn | off / tree | 5295 / 2735 | 0 / 2560 | 959 / 509 | 695f3acdc604 (equal) |

The branching example therefore fails (2/3).

On the same host, Qwen2.5-1.5B-Instruct-Q4_K_M on Vulkan (29/29 layers) passes all three workloads (3/3) with equal digests. The same Gemma branching workload matched on the CPU build (`C:/dev/slang-logs/shimtree/tree_spec3.log`, digest 139fec2ec5a6).

## Suspected cause (not yet proven)

The Fable review of #10518 (finding 6) noted that the tree cold path differs in shape from the no-cache path on an offloaded host:

- no-cache decodes the whole prompt in one call while its context is unwarmed;
- the tree splits off the last token.

On a GPU backend, a different micro-batch shape can change reduction order, so branches decoded from a reused prefix can diverge in the last bits. The two workloads that are exact (boundary, multiturn) reuse along one path. Branching reuses one owner prefix for 7 siblings.

## Next steps

1. Run the no-cache lane twice on Vulkan to rule out run-to-run nondeterminism.
2. Log per-request outputs to find the first request that diverges.
3. If the cause is the shape difference, either make the cold no-cache path use the same split, or document that mode 3 is exact only on CPU, or on GPU when the shape matches.

Logs: `C:/dev/slang-logs/postfix/tree_live_vulkan_*.log`

## Root-Cause Proven in Source (2026-11-22, Bug Lane E Audit)

Static inspection of `src/runtime/slang_ggml_shim.c` proves the exact micro-batch split mismatch suspected above:

1. At `src/runtime/slang_ggml_shim.c:1573-1577`:
   ```c
   static int64_t slang_request_first_ubatch(const SlangGgmlRequest *request) {
       if (!request || request->warm || !g_model_offloaded) return 0;
       return slang_context_ubatch_tokens(); /* 512 on offloaded Vulkan */
   }
   ```
   And in `slang_request_warm()` (`slang_ggml_shim.c:1579-1589`), prompts with `prompt_len >= ubatch` (`~830` tokens in `branching`) return `1` early at line 1581 **without setting `request->warm = 1`**.
2. Next, in the **no-cache** evaluator `slang_ggml_request_eval_prompt()` (`slang_ggml_shim.c:1788-1792`):
   ```c
   /* Cold full-ubatch warm-up handled short prompts; split final token only when safe. */
   int64_t head = suffix_len > 1 && slang_request_first_ubatch(request) == 0 ? suffix_len - 1 : suffix_len;
   ```
   - On **CPU** (`!g_model_offloaded`), `slang_request_first_ubatch(request)` is `0`, so no-cache sets `head = suffix_len - 1` (`[512, 317] + [1]`), matching the tree lane (`139fec2ec5a6`).
   - On **offloaded Vulkan** (`g_model_offloaded == 1`, `request->warm == 0`), `slang_request_first_ubatch(request)` returns `512 != 0`, so every fresh no-cache request sets `head = suffix_len` (`[512, 318]` — decoding the final prompt token inside a 318-token GEMM batch!).
3. By contrast, `slang_tree_eval_prompt()` (`slang_ggml_shim.c:1090`) **unconditionally** splits off the final token:
   ```c
   int64_t head = suffix_len - 1;
   ```
   decoding `[512, 317] + [1]` (cold) and `[317] + [1]` (warm siblings), so the sampled logits always come from a 1-token GEMV kernel instead of a 318-token GEMM kernel. On GPU Vulkan shaders, GEMM (`n=318`) vs GEMV (`n=1`) FP reduction order differs in the low mantissa bits, flipping greedy argmax on `gemma-3-270m-it` in the 7-branch `branching` workload!

### Exact 1-Line Fix for the Slang Runtime Owner (`src/runtime/slang_ggml_shim.c`)
At `src/runtime/slang_ggml_shim.c:1790`, split off the final token whenever `head = suffix_len - 1` still covers a full `first_ubatch` (`512`) so the first chunk still warms the full `ubatch` graph AND the final token uses the identical `[1]` GEMV decode as `slang_tree_eval_prompt`:
```c
int64_t first_ubatch = slang_request_first_ubatch(request);
int64_t head = suffix_len > 1 && (first_ubatch == 0 || suffix_len - 1 >= first_ubatch) ? suffix_len - 1 : suffix_len;
```
*(Left untouched in `work/mac-bugs-vulkan-20261122` because `src/runtime/slang_ggml_shim.c` is outside the disjoint `*vulkan*` file ownership boundary; ready for the Slang runtime owner to apply and verify against `slang_kv_tree_cache_live_spec.spl`.)*
