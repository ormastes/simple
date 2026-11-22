# slang — Pluggable Model Kinds and Modalities

Status: design, 2026-11-17. Base: `7e2920f84a9` (mtmd image+audio input live).
Scope: any-to-any local serving (text, image, audio and video in; text, image and
audio out) behind one OpenAI-compatible server, using a small common structure
that each model kind plugs into. The implementation lanes are kept outside git
(session scratchpad).

## 1. What the reference servers do (and what slang takes)

| Concern | vLLM | SGLang | slang takes |
|---|---|---|---|
| Model lookup | `ModelRegistry`: HF `architectures[]` -> class; plugins through `vllm.general_plugins` | `EntryClass` per module in `srt/models`; `SGLANG_EXTERNAL_MODEL_PACKAGE` | one ordered **kind resolver** (§3.2), keyed by GGUF metadata, not by class names |
| MM input | `MULTIMODAL_REGISTRY.register_processor(Processor, info, dummy_inputs)`; `PromptReplacement` expands a placeholder into N feature tokens; `get_input_embeddings` merges them | `BaseMultimodalProcessor.models=[...]`; `pad_input_ids`; `general_mm_embed_routine` | libmtmd already does placeholder expansion and embedding merge in the shim. slang keeps the *marker* contract (`SLANG_MEDIA_MARKER`, one per blob) and does **not** reimplement processors |
| Modality keys | `image`, `video`, `audio`; `limit_mm_per_prompt` | IMAGE / MULTI_IMAGES / VIDEO / AUDIO | `Modality` enum (§3.1) + per-model in/out sets |
| Video | `MediaConnector.fetch_video` -> frames + metadata; `--media-io-kwargs {"video":{"num_frames":N}}` | video processor -> frames | frames sampled by an on-demand external decoder, sent as image blobs (§4) |
| Tasks | `--runner generate|pooling`, `--convert embed|classify|reward`; `SupportsTranscription` | embedding/reward models in the same registry | `ModelKind` (§3.1). The kind fixes the task; there is no convert flag |
| Output modalities | vLLM-Omni: staged pipelines (Thinker -> Talker -> Code2Wav), a diffusion engine, `/v1/audio/speech`, `/v1/images/generations` | SGLang Diffusion: `/v1/images/generations`, `/v1/videos` | per-kind runners. TTS is LLM stage -> vocoder stage, a 2-stage pipeline in the Omni style |
| Endpoints | chat (`image_url`, `input_audio`, `video_url`, `audio_url` parts), completions, embeddings, score, rerank (Jina/Cohere), audio transcriptions/translations, pooling | same OpenAI set | the same set, one serving module per endpoint family (§3.5) |

llama.cpp-family equivalents, all used as **dynamically loaded libraries, never at import**:
- libmtmd (image and audio in; live in `slang_ggml_shim.c`).
- llama.cpp `--embeddings` / `--pooling rank`, which is the same C API through the existing shim.
- OuteTTS + WavTokenizer vocoder (`llama-tts`, through the llama C API).
- whisper.cpp (`whisper_full`).
- stable-diffusion.cpp (`new_sd_ctx`, `generate_image(sd_img_gen_params_t)`).

## 2. Model kinds

Local models are in `C:/dev/model`. HF names marked † were not re-verified this
session (the HF tool was down), so verify them before fetching.

| Kind | In -> Out | Runtime path | Local fit | Small model to fetch | Endpoint |
|---|---|---|---|---|---|
| `Chat` (text LLM) | text -> text | ggml shim (`backend.spl`); pure runner for safetensors Llama | Qwen2.5-1.5B-Instruct Q4_K_M, gemma-3-270m-it Q8_0, stories15M | — | `/v1/chat/completions`, `/v1/completions` |
| `Chat` + vision projector (VLM) | text+image -> text | ggml shim + mtmd (`load_mmproj`, caps bit 1) | SmolVLM2-256M-Video-Instruct (+mmproj, `clip.has_vision_encoder`) | — | chat `image_url` part |
| `Chat` + video | text+video -> text | video -> N frames -> VLM path. The frame source is ffmpeg, found on demand via `SLANG_FFMPEG` and run through SOSIX. If ffmpeg is absent the request is refused with a reason (today's behaviour) | SmolVLM2-256M-Video | ffmpeg static build (gyan.dev) into `C:/dev/tools/ffmpeg` | chat `video_url` part |
| `Chat` + audio projector (audio-LLM) | text+audio -> text | ggml shim + mtmd (caps bit 2) | ultravox-v0_5-llama-3_2-1b (+mmproj, `clip.has_audio_encoder`), Qwen3-ASR-0.6B (+mmproj) | — | chat `input_audio` part |
| `Asr` | audio -> text | (a) an audio-capable `Chat` model with a transcription prompt (Qwen3-ASR; live today); (b) whisper.cpp through a new `slang_whisper_shim` | Qwen3-ASR-0.6B | `ggerganov/whisper.cpp` `ggml-tiny.en.bin` / `ggml-base.en.bin`† | `/v1/audio/transcriptions` |
| `Tts` | text -> audio | Stage 1: OuteTTS (llama arch) produces audio-code tokens through the ggml shim. Stage 2: WavTokenizer vocoder run with embeddings out (pooling none) through the same shim. ISTFT and WAV are pure Simple (`common/audio/wav_encode.spl`) | — | `OuteAI/OuteTTS-0.2-500M-GGUF` Q8_0†, `ggml-org/WavTokenizer` `WavTokenizer-Large-75-F16.gguf`† | `/v1/audio/speech` |
| `ImageGen` | text -> image | stable-diffusion.cpp through a new `slang_sd_shim`, Vulkan or CPU. PNG output is pure Simple (`common/image/png_encode.spl`) | — | `stabilityai/sd-turbo` `sd_turbo.safetensors`† (1-4 steps, 512²) or `second-state/stable-diffusion-v1-5-GGUF` Q8_0† | `/v1/images/generations` |
| `Embedding` | text -> vector | ggml shim, `llama_set_embeddings` with pooling mean/cls/last | (Qwen2.5 can, but poorly) | `CompendiumLabs/bge-small-en-v1.5-gguf` q8_0† | `/v1/embeddings` |
| `Rerank` | (query, docs) -> scores | ggml shim, pooling `rank` | — | `gpustack/bge-reranker-v2-m3-GGUF`† | `/v1/rerank` (Jina/Cohere shape: `{query, documents[], top_n}` -> `results[{index, relevance_score}]`) |

VLM, audio-LLM and video are deliberately **not** separate kinds. They are a
`Chat` model whose *input modality set* comes from its projector. This is the
vLLM `SupportsMultiModal` idea, and it matches the existing caps mask.

## 3. Common structure

### 3.1 Enums (new `slang/modality/kinds.spl`)

```
enum Modality:   Text | Image | Audio | Video
enum ModelKind:  Chat | Asr | Tts | ImageGen | Embedding | Rerank
struct KindProfile:            # what /v1/models reports and routing reads
    kind: ModelKind
    inputs: [Modality]
    outputs: [Modality]
    runner: RunnerKind         # existing enum, grown (3.4)
    reason: text               # why not runnable, "" when runnable
```

`NativeModel` (`native_formats.spl:46`) gains one field, `profile: KindProfile`.
No parallel model descriptor is added.

### 3.2 Kind resolver (new `slang/modality/kind_registry.spl`)

`general.architecture` alone cannot identify the kind:
- OuteTTS uses a plain decoder architecture (`llama` or `qwen2`, depending on the version).
- bge embedder and bge reranker are both `bert`.
- VLMs and audio-LLMs have a plain decoder GGUF; the modality lives in the mmproj.
- whisper `.bin` is ggml (`lmgg` magic), not GGUF.
- SD weights are often safetensors.

`resolve_kind(dir) -> KindProfile` is therefore an ordered chain, where the
first decisive step wins:
1. **Manifest override.** A sidecar `slang_kind.sdn` (`kind: tts`, `vocoder: <file>`). This is the escape hatch for anything ambiguous.
2. **Companion files.**
   - An mmproj gives `Chat` with inputs from `clip.has_vision_encoder` (Image, plus Video when a frame source exists) and `clip.has_audio_encoder` (Audio). Both keys were probed in the three local mmproj files.
   - A WavTokenizer vocoder GGUF next to an LLM gives `Tts`.
3. **Metadata keys.** `<arch>.pooling_type` is a u32 enum (0 none, 1 mean, 2 cls, 3 last, 4 rank): 4 gives `Rerank`, 1-3 gives `Embedding`. Also `general.type`.
4. **Architecture table.** One `[(arch, ModelKind)]` literal: `bert`, `nomic-bert` and `jina-bert-v2` map to Embedding; `wavtokenizer-dec` is vocoder-only, not servable. This is the vLLM registry analogue; adding a model is one row.
5. **Magic sniff.**
   - `lmgg` / `ggml` gives `Asr` (whisper).
   - safetensors with an SD UNet key prefix (`model.diffusion_model.`) gives `ImageGen`.
   - The existing `LlamaForCausalLM` check gives `Chat` on the pure runner.

The GGUF reader must read the u64 `value_len` as **binary**. `gguf_is_projector`
(`native_formats.spl:96-100`) only works because `clip` is 4 bytes long. The
resolver reads key/value headers with ranged byte reads (see seed gap G8) and
stops at the first tensor-info entry.

### 3.3 Content parts (in and out)

- **Input.** Keep `ChatPart` (`protocol.spl:214`: kind, text, data b64, format) and `MediaBlob` (`backend.spl:673`). No new input type.
- **Output.** Add a twin in `kinds.spl`:
  ```
  struct OutputPart:
      modality: Modality
      text: text
      bytes: [u8]      # wav / png / f32-le vector, packed
      mime: text       # "audio/wav", "image/png", "application/x-f32le"
  struct KindRequest:  model_id: text, parts: [ChatPart], params: KindParams
  struct KindParams:   max_tokens, n, size, steps, seed, voice, top_n, response_format (all text/i64)
  struct KindResult:   parts: [OutputPart], prompt_tokens: i64, completion_tokens: i64
  ```

### 3.4 Runner contract and on-demand loading

`RunnerKind` (`runner_dispatch.spl:25`) grows from `Ggml | Pure` to
`Ggml | Pure | Whisper | StableDiffusion`. TTS, embeddings and rerank run on
`Ggml`: same library, different entry points.

Each runner module exposes the same four free functions:
- `<r>_open(model: NativeModel) -> Result<(), text>`
- `<r>_run(req: KindRequest) -> Result<KindResult, text>`
- `<r>_close()`
- `<r>_available() -> bool`

Each kind route calls its runner directly from its serving module (`engine/kind_dispatch.spl`, a `match` on `RunnerKind`, was removed once every route was served). That is
plain enum dispatch: no inheritance and no trait objects, which keeps it seed-safe.

Rules:
- **Load on demand.** A native library is `spl_dlopen`ed inside `<r>_open` only. It is never opened at import, startup or discovery. `<r>_available()` only checks that the configured path exists (`SLANG_GGML_LIB`, `SLANG_WHISPER_LIB`, `SLANG_SD_LIB`), the same way `engine_backend_available` does today. GPU variants (Vulkan, HIP, CUDA builds of each shim) are separate DLLs selected by the env path. They are never probed eagerly.
- **One C shim per native library.**
  - The dynamic SFFI is int64-only, with at most 13 arguments (`dynamic_sffi.rs:1015`). `whisper_full(ctx, whisper_full_params)` and `generate_image(sd_img_gen_params_t)` take structs by value, so each gets `src/runtime/slang_<lib>_shim.c`. Its exports are int64 scalars plus the `(buf, cap, out_len)` out-buffer idiom, modelled on `slang_ggml_shim.c`.
  - Windows sibling DLLs are preloaded with the existing `_preload_windows_dll_siblings`.
- **One ggml per process.** whisper.cpp and sd.cpp each vendor ggml, and the Windows loader reuses an already-loaded `ggml.dll` by name. Each new shim therefore links ggml **statically** (`BUILD_SHARED_LIBS=OFF`) into its own DLL, so it can never bind to llama.cpp's ggml.
- **Model slots per kind.**
  - Whisper and SD runners keep their own loaded model in their own DLL and module state, so they can stay resident next to a chat model.
  - The ggml shim keeps **one global model** (`slang_ggml_shim.c:201` `static struct llama_model *g_model`), so Ggml-backed kinds (Chat, Embedding, Rerank, Tts) swap on demand.
  - TTS needs the LLM and its vocoder at once. That requires a handle-based model API (`model_open(path) -> h`, requests bound to `h`) in the shim first.
  - Memory is shared with the GPU, so each `open` checks `memory_budget.spl` first.

### 3.5 HTTP surface

`api_server.spl` gets one route table, `[(route, ModelKind, handler)]`. Each
family lives in `entrypoints/openai/serving/` (a new directory, which keeps
`openai/` at 6 entries):

| Route | Module | Request -> response |
|---|---|---|
| `/v1/chat/completions` | `serving_chat.spl` (existing) | + `video_url` frames; `modalities:["text","audio"]` is refused until an omni model exists |
| `/v1/audio/transcriptions` | `serving/serving_transcriptions.spl` | multipart `file` (JSON `{file_b64, format}` until G1) -> `{text}` |
| `/v1/audio/speech` | `serving/serving_speech.spl` | `{input, voice, response_format: wav}` -> wav bytes (b64 JSON envelope until G1) |
| `/v1/images/generations` | `serving/serving_images.spl` | `{prompt, n, size, response_format: b64_json}` -> `data[].b64_json` |
| `/v1/embeddings`, `/v1/rerank` | `serving/serving_pooling.spl` | OpenAI embeddings / Jina-Cohere rerank |

Rules:
- A route that is called with a model of the wrong kind returns 400 `wrong_model_kind`, naming both kinds.
- Every refusal names its cause. A modality is never silently dropped; this is the `media_refusal` invariant (`serving_chat.spl:110`).
- `/v1/models` adds `slang_kind`, `input_modalities` and `output_modalities` to each entry.

## 4. Video input

`modality/video_frames.spl`: `sample_frames(blob, n) -> Result<[MediaBlob], text>`.
1. Write the blob to a temp file.
2. Run `ffmpeg -i <tmp> -vf fps=<n/duration>,scale=384:-1 -frames:v <n> -f image2pipe -c:v mjpeg -` through the SOSIX byte-output process call (bounded timeout and output cap; G7).
3. Split the stdout on JPEG SOI/EOI markers.
4. Expand the single video marker into `n` image markers.

If no frame source is available, keep today's refusal text. Default `n = 8`,
which fits SmolVLM2's context. The model needs no change.

## 5. Seed / stdlib gaps (evidence: base `7e2920f84a9`)

| # | Gap | Where | Needed by |
|---|---|---|---|
| G1 | HTTP bodies are `text` both ways, so raw wav/png responses and binary multipart uploads cannot round-trip; the server also hard-codes the JSON content type. Fix: `ApiResponse` gains `content_type: text` and `body_bytes: [u8]` | `http_server/types.spl:245` (req.body), `:301` (resp.body); `protocol.spl:18-20` (`ApiResponse` has no content type or bytes); `app/slang_server/main.spl:40-44` | speech, transcriptions |
| G2 | Body limit 10 MiB caps inline audio and video | `common/net/http_core.spl:27` `MAX_BODY_SIZE` | video, ASR |
| G3 | Shim output is read **one FFI call per byte**, and input is pushed one call per byte. This is fatal at MB scale (wav, png, f32 vectors) | `backend.spl:473-511` (`_push_text`, `_read_out`, request variants) | all outputs |
| G4 | `spl_wffi_call_i64_with_bytes` and `_into_bytes` are implemented in the seed (`interpreter_extern/dynamic_sffi.rs:822,897`), but the sync facade exports neither. `_into_bytes` is re-exported only by the async facade (`nogc_async_mut/sffi/dynamic.spl:11`); `_with_bytes` has no export anywhere. Users redeclare them | `nogc_sync_mut/sffi/dynamic.spl:72,677-679`; `backend.spl:35`; `chrome_render_module_sffi.spl:32,40` | all shims |
| G5 | No packed zeroed `[u8]` allocator. Out-buffers are filled with interpreted push loops. An empty `[u8]` literal lowers to a generic Array, so the bytes are widened and copied element-wise at every FFI call | `chrome_render_module_sffi.spl:425-429`; `interpreter/expr/ops.rs:885-891`; `dynamic_sffi.rs:847-852` | TTS, image, embeddings |
| G6 | Dynamic call ABI: i64 scalars only, at most 13 arguments | `dynamic_sffi.rs:1015` | whisper and sd (hence the shims, §3.4) |
| G7 | SOSIX aliases only the text `process_run_bounded` and the piped v2 calls. There is no alias for the byte-output variant (`process_ops.spl:2015`, seed `interpreter_extern/system.rs:904`) or for the bounded owned-v3 calls with stdin bytes (`process_ops.spl:59-71`) | `sosix/process.spl:14-29` | video frames |
| G8 | No exported ranged **byte** read; only the text-decoding `file_read_text_at_nullable`. The byte reader exists privately | `io_runtime.spl:371`; `io/external_file.spl:17` | kind resolver (GGUF KV) |
| G9 | f32 vectors are decoded per element in interpreted code (`f32_from_bits`) | `pure/tensor_ops.spl:51-69` | embeddings, vocoder ISTFT (perf, unverified) |

G3-G5 matter most. They decide whether TTS, image and embedding outputs are
usable on the seed.

## 6. Non-goals (v1)

- Audio or image *output* from a chat model (Qwen-Omni Talker).
- Video generation.
- `/v1/audio/translations`.
- Remote media URLs. These stay refused until slang has a network owner.
- LoRA for non-chat kinds.
- Batching across kinds.
