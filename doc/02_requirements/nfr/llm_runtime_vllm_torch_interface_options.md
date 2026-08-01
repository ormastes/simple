# NFR Options: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Option A: Local Evidence NFRs

Targets:

- Nil-free public output: no literal `nil` in manifests, JSONL, dashboard text,
  or MCP/tool responses.
- Readiness probe runtime: under 2 seconds when checking static files and a
  mocked endpoint.
- Security: dynamic LoRA loading is reported as disabled by default.
- Observability: every probe emits one structured JSONL event with status,
  reason, and option-like missing fields.
- Data minimization: prompts, tool payloads, API keys, credentials, and secret
  paths are redacted or absent by default.

Pros:

- Verifiable without GPU hardware.
- Fits current dashboard diagnostics collector.

Cons:

- Does not prove real vLLM latency or GPU memory.

Effort: Small.

## Option B: Live vLLM NFRs

Targets:

- Everything in Option A.
- `/v1/models` probe completes under 5 seconds on a live local endpoint.
- Chat readiness records template status.
- RSS/GPU-memory observations are recorded when available.
- Torch/LibTorch ABI, CUDA/CPU mode, loader path, and graceful fallback are
  recorded in readiness evidence.

Pros:

- Closer to production serving evidence.

Cons:

- Depends on local vLLM/GPU availability.
- Needs skipped/blocked evidence when hardware is absent.

Effort: Medium.

## Option C: Training and Serving NFRs

Targets:

- Everything in Option B.
- Fine-tune job metrics, eval target, artifact hash, and serving regression
  evidence are recorded for each accepted adapter.

Pros:

- Best end-to-end quality bar.

Cons:

- Too expensive for a first planning/implementation slice.

Effort: Large.

## Recommended Selection

Option A. It gives a concrete quality gate now and leaves hardware-bound live
latency evidence for the next slice.
