# slang kind runners reload their models from disk on every request (perf)

- **Status:** open (perf; a deliberate trade-off for correctness).
- **Found:** 2026-11-22, during the Fable review of #10710.
- **Affected:**
  - `pooling_runner_serve`: `/v1/embeddings` and `/v1/rerank`;
  - `tts_runner`: `/v1/audio/speech`, which opens both the OuteTTS LM and the WavTokenizer vocoder;
  - `sd_runner`: images, see `slang_sd_image_generation_slow_on_amd_gpu_2026-11-22.md`.

## Why it is this way

Under the interpreter, each HTTP connection thread starts from a snapshot of module state, and its writes stay thread-local. A model handle cached in a module global was therefore reopened, and leaked, on every new thread, until the shim's 4 model slots ran out. #10710 made the pooling runner stateless instead: it opens the library and model handle, serves, and closes, on every request.

## Cost (measured 2026-11-22, Vulkan, Radeon 8065S)

| Request | Wall time | Note |
|---|---|---|
| embeddings, 2 inputs, bge-small | 127 ms | |
| rerank, 3 documents, bge-reranker-v2-m3 | 1058 ms | includes loading 600 MB |
| tts, "Slang speaks." | 27.4 s | most of it is the ISTFT (`slang_tts_istft_vocoder_decode_slow_in_spec_2026-11-19.md`), plus two model loads |

Logs are in `C:/dev/slang-logs/l45/system.log` and `build/probe/slang_system.txt`.

## Fix direction

Since #10710, the shim refcounts model handles (`slang_model_slot.opens`). Keep the handle resident on the C side with an idle timeout or LRU, so a reopen by path is a hash hit and not a disk load. The Simple side stays stateless per request, which keeps the thread-local problem solved.
