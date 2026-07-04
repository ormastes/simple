# Requirement Options: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Option A: vLLM Readiness Bridge

Add a small manifest and SPipe-readable probe for vLLM serving readiness.

Requirements:

- Represent base model, optional chat template, optional LoRA adapter mapping,
  endpoint URL, and readiness state.
- Validate nil-free public output using option-like absence labels.
- Emit JSONL evidence consumable by the existing diagnostics/dashboard lane.
- Treat dynamic LoRA loading as disabled unless explicitly marked trusted.
- Reuse existing Torch/SFFI probes only as readiness evidence.
- Report known Torch/svLLM placeholder blockers as `blocked`, not `ready`.

Pros:

- Smallest slice that connects vLLM, fine-tune artifacts, SPipe, and dashboard.
- Avoids building a trainer or second model runtime.
- Gives later implementation a clear testable boundary.

Cons:

- Does not run fine-tuning.
- Does not implement dynamic adapter loading.
- Does not expose all vLLM APIs.

Effort: Small.

## Option B: Static LoRA Serve Harness

Implement Option A plus a local harness that starts a configured vLLM server with
static `--enable-lora` and `--lora-modules` arguments.

Requirements:

- Everything in Option A.
- Generate deterministic start command metadata without printing secrets.
- Probe `/v1/models` and record base model plus adapter IDs.
- Add SPipe evidence for chat template present/missing.
- Add contract tests for `/v1/models`, `/v1/chat/completions`, base model
  routing, adapter model routing, auth rejection, and unsupported parameter
  handling.

Pros:

- Proves the serving contract end to end.
- Still avoids runtime adapter mutation.

Cons:

- Requires local vLLM environment/GPU or a documented skipped evidence state.
- Higher process-management risk.

Effort: Medium.

## Option C: Full Fine-Tune and Serve Loop

Implement a Simple-managed PEFT/TRL fine-tune run, artifact registration, vLLM
serving, evaluation, and dashboard reporting.

Pros:

- Closest to the full long-term goal.

Cons:

- Too broad for a reliable first slice.
- Mixes training, serving, dashboard, and runtime interfaces in one change.
- Hard to verify without hardware and model fixtures.

Effort: Large.

## Recommended Selection

Option A. It creates the missing contract and evidence shape without owning
training or vLLM process lifecycle yet.

## Non-Selectable Blockers

No option may claim deployment-ready fine-tuned serving until SPipe records:

- target-reaching evaluation evidence for the selected task,
- model path/id and artifact hash,
- license constraints,
- refusal/boundary safety evidence where the domain requires it,
- runtime latency and memory evidence,
- nil-free dashboard/tool readback.
