# Domain Research: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Sources

- vLLM Online Serving:
  https://docs.vllm.ai/en/stable/serving/online_serving.html
- vLLM LoRA Adapters:
  https://docs.vllm.ai/en/stable/features/lora.html
- PyTorch documentation:
  https://pytorch.org/docs/2.12/index.html
- Hugging Face PEFT:
  https://huggingface.co/docs/peft/index
- Hugging Face TRL:
  https://huggingface.co/docs/trl/index

## Findings

- vLLM provides an HTTP server compatible with OpenAI-style APIs including
  completions, responses, chat completions, embeddings, and selected media APIs.
- Chat completion serving requires a usable chat template. Missing templates
  make chat requests fail, so the Simple bridge must surface template readiness.
- vLLM serves LoRA adapters by starting the server with `--enable-lora` and
  explicit adapter mappings through `--lora-modules name=path`.
- vLLM also supports runtime LoRA updates, but its own docs warn that dynamic
  loading has security risk and should be limited to isolated trusted
  environments.
- PEFT focuses on parameter-efficient adaptation such as LoRA so large models
  can be adapted without full-parameter fine-tuning.
- TRL covers post-training workflows including SFT, DPO, GRPO, reward modeling,
  and related methods.
- PyTorch remains the broad tensor/autograd/accelerator layer. For this lane,
  Simple should consume Torch readiness and artifact probes rather than re-open
  full wrapper design.

## Implication

The first production-shaped Simple feature should treat vLLM as a process/API
boundary and LoRA as an artifact boundary. Dynamic LoRA loading, full PEFT/TRL
training orchestration, and custom Torch model execution should remain later
lanes until the static serving/readiness path is verified.

## 2026-07-01 Continuation: OpenCode and SGLang

<!-- codex-research -->

OpenCode's documented non-interactive surface is `opencode run [message..]`
with `--model`, `--session`, `--attach`, `--format`, `--dir`, and `--auto`
flags, while `opencode serve`/`web` create attachable headless servers:
https://opencode.ai/docs/cli/

OpenCode issue traffic also shows the failure mode this lane must defend
against: headless agent processes and their children can hang or survive
interrupts, so a Simple wrapper needs explicit pid readback plus a kill path
routed through the owner process facade, not shell-based name killing.

SGLang exposes a server launch surface with `python -m sglang.launch_server`,
`--model-path`, tensor parallel `--tp`, data parallel `--dp`, and memory tuning
through `--mem-fraction-static`:
https://github.com/sgl-project/sglang/blob/main/docs/advanced_features/server_arguments.md

vLLM remains the default Simple serving backend because its OpenAI-compatible
server and LoRA serving contracts are already modeled here. Its docs expose
static LoRA serving through `--enable-lora --lora-modules name=path`, dynamic
LoRA APIs that should stay trusted-only, and `/v1/models`/`/health` evidence
endpoints:
https://docs.vllm.ai/en/stable/features/lora/
https://docs.vllm.ai/en/stable/serving/online_serving/

Implication for this continuation: keep OpenCode as a Claude-like CLI provider
with explicit spawn/kill evidence, and borrow SGLang's backend/parallelism
manifest shape without replacing the existing vLLM default.
