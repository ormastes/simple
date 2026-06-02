# SPipe LLM Fine-Tune Process Requirement Options

## Context

The requested feature separates SPipe as a reusable project and extends SPipe
from research/design/implementation/verification into an LLM-backed app/server
development loop: research data, choose a base model, choose a tuning method,
train or retune, verify performance, retry implementation or tuning when
performance is not acceptable, and record the model plus training script.

## Option A: Fine-Tune Process Scaffold

Requirements:
- SPipe records research, data download commands, base model choice, tuning
  method, training script path, model artifact path, evaluation result, and
  retry decision.
- The process supports app/server development by linking each app build to the
  model attempt used for implementation assistance or runtime inference.
- Verification can mark an attempt as accepted, retry-implementation, retry-
  tuning, or try-other-way.

Pros:
- Smallest useful step; gives every future tuning run an auditable record.
- Avoids committing to one vendor, model family, dataset format, or trainer.
- Fits the separated-project goal because the schema can live in SPipe and the
  records can live in each host `.spipe/` directory.

Cons:
- Does not train a model by itself.
- Requires a later implementation pass for concrete download/train/eval tools.

Effort: Medium.

## Option B: Local QLoRA-First Tuning Pipeline

Requirements:
- SPipe downloads datasets into a configured cache, prepares instruction data,
  selects an open base model, runs QLoRA/LoRA fine-tuning, evaluates, records
  metrics, and retries with another model or hyperparameter set when targets
  fail.
- Default base-model candidates are chosen during design for code/app-server
  work and recorded per run.

Pros:
- Produces actual tuned model artifacts.
- Keeps model and data ownership local when hardware is available.

Cons:
- Depends on GPU/VRAM, Python package availability, dataset licensing, and
  model-license review.
- Higher verification cost and more environmental failure modes.

Effort: High.

## Option C: Provider Fine-Tune Adapter Pipeline

Requirements:
- SPipe records provider model choices, provider upload/download steps, tuning
  job IDs, eval results, and retry decisions.
- Training scripts are provider adapters rather than local trainer scripts.

Pros:
- Lower local hardware requirements.
- Faster first usable loop for teams already using hosted LLM providers.

Cons:
- Provider lock-in risk.
- Requires credential handling and cost controls.
- Some providers expose limited model internals and eval telemetry.

Effort: Medium-high.

## Option D: Hybrid Tuning and Retrieval Loop

Requirements:
- SPipe tries retrieval/context engineering first, then provider fine-tuning or
  local QLoRA only when eval failures show durable behavior gaps.
- Every attempt records why the chosen method is appropriate or why another way
  was tried.

Pros:
- Practical for LLM-backed app/server development where many failures are data,
  prompt, tool, or retrieval issues rather than model-weight issues.
- Reduces unnecessary training.

Cons:
- More complex decision tree.
- Requires eval design that can separate retrieval, app, prompt, and model
  failures.

Effort: High.
