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
