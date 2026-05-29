# svllm Master Plan

- **Status:** v0 — derived from user-supplied research doc (2026-04-17) and the approved plan at `~/.claude/plans/to-make-good-file-virtual-stardust.md`
- **Last-updated:** 2026-04-18
- **Related docs:**
  - `../nvfs/svllm_requirements.md` — upfront fs requirements for the parallel nvfs track
  - `./fs_requests/README.md` — reactive fs feature-request capture
  - Approved plan (authoritative): `~/.claude/plans/to-make-good-file-virtual-stardust.md`

## Scope

svllm is a vLLM-like LLM serving tool for Simple / SimpleOS. It provides:

- Paged KV-cache management
- Continuous batching + chunked prefill
- Prefix caching
- Dynamic model loading with sleep/wake semantics
- LoRA adapter hot-swap
- OpenAI-compatible HTTP API

It does **not** do: training, fine-tuning, quantization algorithms (consumes existing quantized tensors), distributed/multi-node serving (v1), RLHF loops.

## Architecture reference

svllm **mirrors vLLM's module layout and naming** unless doing so breaks MDSOC+. See `~/.claude/plans/to-make-good-file-virtual-stardust.md` → "Naming & Architecture Rule" for the full rule. Concretely:

```
src/lib/gc_async_mut/svllm/
  engine/                 # llm_engine, async_llm_engine, arg_utils, metrics
  executor/               # executor_base, gpu_executor
  worker/                 # worker, model_runner, cache_engine
  core/                   # scheduler, block_manager, policy
  model_executor/
    models/
    layers/
    model_loader/         # loader, tensor_pack, safetensors, weight_utils, streamer
    sampling_metadata.spl
  attention/              # layer, ops, backends/
  sequence.spl            # Sequence, SequenceGroup, SamplingParams
  lora/                   # request, layers, models, worker_manager, punica_wrapper
  entrypoints/            # llm, openai/{api_server,protocol,serving_chat,serving_completion}
  nvfs_client/            # shim against the parallel nvfs design
```

Product binary + integration tests live in a separate GitHub repo (`ormastes/svllm`, public, MIT) added at `examples/svllm/` as a git submodule.

## Phase roadmap

| Phase | Name | Key deliverables | Primary fs-requirement hooks |
|---|---|---|---|
| A1 | Model-loader baseline | tensor-pack format, safetensors reader, manifest, weight_utils; failing TDD tests; stubs for packer + service | R1 sealed/pin, R2 aligned async read, R5 capability query |
| A2 | Packer CLI | `src/app/svllm_pack/` consumes safetensors, emits tensor-pack | R3 atomic publish, R1 append_only |
| A3 | Streaming loader + pinned DRAM staging | `model_loader/streamer.spl`, `gpu/pinned_pool.spl`, concurrent chunk H2D | R2, R6 pinned-buffer registration |
| A4 | Paged KV cache + paged attention | `core/block_manager`, `worker/cache_engine`, `attention/backends/paged.spl` | R1 `kv_spill` (optional), R7 hints |
| A5 | Scheduler + worker + executor + engine | continuous batching + chunked prefill; ECS business layer for request batches | — (storage mostly not on hot path here) |
| A6 | HTTP API | `entrypoints/openai/api_server`, async HTTP bridge via monoio | R2 from request-handler tasks |
| A7 | Sleep/wake | `engine/llm_engine.sleep(level)` / `wake_up()` | R3 atomic manifest swap |
| A8 | LoRA adapter hot-load | `lora/` tree, per-request adapter routing | R1 `adapter` class, R8 async listing |

Details for each phase (including per-phase fs-request triggers) are in the approved plan file.

## Key design invariants

1. **Every model artifact is sealed after write.** No in-place mutation of weights, manifests, or adapter objects. Model updates are publish-plus-flip.
2. **Storage reads into pinned buffers only.** No bounce copies on the tensor-pack → GPU path.
3. **KV cache lives in GPU memory.** Spill to NVMe is optional and off the hot decode loop.
4. **Request batches are ECS entities.** MDSOC+'s ECS business layer manages concurrent requests; the `core/scheduler.spl` is a System over those entities.
5. **nvfs is a client contract, not a hard dep.** svllm builds on top of today's FAT32 as a bring-up substrate; the `nvfs_client` shim hides the difference. Production perf requires nvfs; functional correctness does not.

## Research doc — condensed excerpts (for quick reference)

The full user-supplied research doc is the authoritative architecture reference; these are pointers only.

- **SLLM runtime:** treat model weights as installed artifacts. Two-stage workflow: install-time repack → serve-time stream. Manifests separate from chunks. Residency hierarchy: GPU HBM → pinned DRAM → local NVMe → remote object store. Chunk sizes ≈ 2 MiB for dense models.
- **Steady-state serving:** paged KV, continuous batching, chunked prefill, prefix caching, V1 preemption = recompute (vLLM default). Prefill/decode disaggregation deferred to post-v1.
- **Dynamic model loading:** warm pools + cost-aware switching, not blind mmap. Layer-order prefetch for dense; expert-aware for MoE.
- **Adapters:** base models pinned sealed; adapters small hot-swappable objects with LFU residency.
- **Filesystem contract svllm depends on:** sealed objects, pinned extents, async range reads into pinned buffers. See `../nvfs/svllm_requirements.md` for the precise API.

## Verification strategy (end-of-phase gates)

Gates for each phase are in the approved plan's "Verification" section. Summary:

- Tensor-pack round-trip unit tests
- Packer CLI on a real small model (e.g., TinyLlama-125M)
- Cold load + first token via OpenAI-compat API
- Throughput baseline recorded under `doc/10_metrics/svllm_baseline.md`
- Model-switch measured (no fixed threshold yet; baseline first)
- Phase B coverage: at least one nvfs-requirements update per phase
- `bin/simple build check` stays clean (lint + gc_boundary_check)

## Risk register

See the "Risks & Mitigations" section of the approved plan; summarized here:

- Torch FFI's opaque handles could lock us in — mitigated by using raw CUDA FFI for weights/KV.
- HTTP sync→async bridge latency — measured in A6; fall back to direct monoio if painful.
- Feature-request backlog without prioritization — Phase B requires measured impact.
- Design drift from research doc — this file is the single source of truth for svllm; any deviation updates here.

## Change log

- **2026-04-18 (v0):** Initial doc. Pivoted from "fs_requests reactive only" to "upfront nvfs requirements in parallel track." Module layout confirmed as vLLM-mirrored. Repo split: library in main simple repo, product in `ormastes/svllm` submodule.
