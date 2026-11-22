# slang image generation takes 23–33 s for one 512² step on the AMD GPU (perf)

- **Status:** open (perf). The cause has not been measured phase by phase yet.
- **Found:** 2026-11-22. Host: Windows EVO-X5Pro, Radeon 8065S (gfx1151), shared memory.
- **Path:** `POST /v1/images/generations` → `serving_images.spl` → `sd_runner.spl` → `slang_sd_shim.c` (stable-diffusion.cpp, the `sd-vulkan` variant built by `scripts/check/build-slang-sd-shim.shs`).

## Observed

Model sd-turbo (`sd_turbo.safetensors`, 5.2 GB), 512x512, `steps: 1`.

| Run | Wall time | Log |
|---|---|---|
| `slang_sd_image_live_spec` | `request_ms=33196` | `C:/dev/slang-logs/rel-live/sd_image.log` |
| system test, image_gen example | 23468 ms | `C:/dev/slang-logs/l45/system.log` |

sd-turbo at 1 step should finish in a few seconds on this GPU once the model is loaded.

## Suspected causes (unproven)

1. **The model loads on every request.** `sd_runner` holds the context in module globals. Under the interpreter, module state is thread-local per connection thread (see `llm_engine.engine_preload`), and the single-owner flag closes and reopens it. So each request probably pays the 5.2 GB safetensors load. Fix direction: a C-side context cache keyed by model path, with a refcount, like `slang_ggml_model_open`.
2. **The Vulkan backend may not be selected, or only partly offloaded.** The shim suppresses stable-diffusion.cpp's logs, so backend selection is unverified. The only info line seen is the CPU feature string.
3. **No ROCm/HIP variant exists.** `build-slang-sd-shim.shs` builds only `cpu` and `vulkan`. Try ggml's HIP backend (`SD_HIPBLAS`) with the ROCm clang on this host.

## To do

- Time each phase: dlopen, `new_sd_ctx`, text encode, each sample step, VAE decode, PNG encode.
- Fix the dominant phase.
- Record cold and warm numbers for cpu, vulkan and, if it builds, hip in `test/05_perf/`.
