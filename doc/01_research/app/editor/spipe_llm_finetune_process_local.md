# Domain Research: SPipe LLM Fine-Tune Process

Date: 2026-06-02

## Sources

- OpenAI API supervised fine-tuning guide:
  https://platform.openai.com/docs/guides/supervised-fine-tuning
- Hugging Face PEFT documentation:
  https://huggingface.co/docs/peft/index
- Hugging Face TRL SFT Trainer documentation:
  https://huggingface.co/docs/trl/en/sft_trainer
- Unsloth fine-tuning guide:
  https://docs.unsloth.ai/get-started/fine-tuning-llms-guide
- QLoRA paper:
  https://arxiv.org/abs/2305.14314

## Findings

Provider supervised fine-tuning uses a base model, uploaded training data, and a
fine-tuning method. The resulting model ID is then used through normal inference
APIs. This matches SPipe's need to record base model, training file/data,
training command/job, model artifact, and evaluation.

PEFT frames LoRA-style adaptation as a way to train a small number of additional
parameters instead of all model weights, reducing compute and storage cost while
remaining practical for large models. This supports SPipe's explicit separation
between base-model choice, tuning-method choice, and training artifact.

TRL SFT Trainer documents prompt/completion and conversational training modes,
including completion-only or assistant-only loss. This supports SPipe's data
record requirements: dataset format, prompt shape, target outputs, and eval
method must be captured before training.

Unsloth recommends starting with smaller instruct models for experimentation and
choosing among SFT, LoRA, QLoRA, full fine-tune, and RL based on goal and
resources. It also emphasizes that training and serving precision should match
when possible. This supports SPipe's `try-other-way` and retry classification
instead of blindly repeating the same tuning method.

QLoRA demonstrates memory-efficient fine-tuning by backpropagating through a
frozen 4-bit quantized model into LoRA adapters, using NF4, double
quantization, and paged optimizers. This supports QLoRA as the default local
resource-constrained path while preserving provider fine-tune and full
fine-tune as separate choices.

## Process Implications

SPipe should require evidence in this order:

1. Research goal, target app/server behavior, and candidate data.
2. Record data download commands, licenses, checksums, cache paths, and
   verification results.
3. Wait for user-selected requirements and NFRs.
4. Record base-model research, license/constraint fit, context length, and
   deployment target.
5. Select tuning method: retrieval/prompt/tool update, provider SFT, local
   LoRA/QLoRA, full fine-tune, or RL/preference optimization.
6. Record exact training script or provider-managed job command.
7. Evaluate with task metrics and performance targets.
8. If the attempt fails, classify retry as implementation, data research,
   base-model choice, tuning method choice, or another architecture.
9. For LLM-backed apps/servers, record the model handoff and retune request.

## Requirement Options Supported

The current requirement options remain valid:

- A: process scaffold and evidence tracking.
- B: local QLoRA-first tuning pipeline.
- C: provider fine-tune adapter pipeline.
- D: hybrid tuning and retrieval loop.

The domain evidence supports keeping these choices separate because each has
different cost, data, hardware, deployment, and verification implications.
