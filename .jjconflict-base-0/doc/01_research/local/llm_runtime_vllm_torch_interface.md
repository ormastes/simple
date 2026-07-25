# Local Research: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Scope

This lane covers the smallest useful bridge between existing Simple LLM work,
vLLM serving, fine-tune artifacts, Torch/SFFI readiness, SPipe evidence, and the
agent dashboard.

It does not replace the context/ponytail mimic lane. That lane is tracked in
`llm_tooling_context_ponytail_mimic`.

## Existing Surfaces

- SPipe fine-tune process requirements exist at
  `doc/02_requirements/language/tools/spipe_llm_finetune_process.md`.
- SPipe fine-tune NFRs exist at
  `doc/02_requirements/nfr/spipe_llm_finetune_process.md`.
- Architecture and detail design exist under
  `doc/04_architecture/app/spipe/` and `doc/05_design/app/spipe/`.
- PyTorch wrapper and integration research/design already exists under
  `doc/01_research/ml/` and `doc/05_design/ml/`.
- svLLM planning exists at `doc/05_design/ml/svllm/svllm_master_plan.md`.
- Runtime/source surfaces include `src/app/svllm_pack`, `src/app/llm_caret`,
  `src/compiler_rust/driver/src/cli/llm_tools.rs`,
  `src/compiler_rust/compiler/src/interpreter_extern/torch.rs`, and
  `src/runtime/torch_sffi.h`.
- Dashboard work now has a diagnostics JSONL collector and web panel surface
  under `src/app/llm_dashboard` and `src/app/web_dashboard`.

## Gaps

- There is no single runtime bridge plan that says how a fine-tuned artifact is
  served by vLLM and observed by SPipe/dashboard evidence.
- Existing fine-tune docs focus on process and retries, not the serving contract.
- Existing Torch work is broad; this lane needs only readiness probes and
  artifact metadata, not a new trainer.
- User-visible absence must be option-like and nil-free.
- Torch runtime surfaces still have placeholder-like behavior that must block
  deployment claims: `dyn_torch_available()` is reported as hard-disabled,
  `dyn_torch_tensor_linalg_solve(...)` is reported as returning `0`,
  `tensor_cuda` is reported as hardcoding device `0` in multiple backends, and
  seed helpers are reported as no-op.
- svLLM loader surfaces still have unimplemented or stubbed entry points around
  manifest parsing, tensor-pack building, and `load_model_from_pack`.
- Existing fine-tune tracking still has open target-attainment, safety, license,
  latency, and memory evidence requests. A process-valid run is not deployment
  evidence.

## Smallest Viable Slice

Use vLLM as an OpenAI-compatible serving boundary, use LoRA adapters as the
first accepted fine-tune artifact type, and use existing Torch/SFFI only for
readiness/probe evidence. Feed all run metadata into SPipe JSONL so the
dashboard can show status without exposing nil.

The first implementation lane after requirement selection should either build
the vLLM readiness bridge or clear the Torch/svLLM placeholder blockers that
would make the bridge report a false-ready state.
