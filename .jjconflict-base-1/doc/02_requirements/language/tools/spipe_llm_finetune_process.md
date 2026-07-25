# SPipe LLM Fine-Tune Process Requirements

Selected feature sequence: Fine-Tune Process Scaffold -> Local QLoRA-First Tuning Pipeline -> Provider Fine-Tune Adapter Pipeline -> Hybrid Tuning and Retrieval Loop
Selected by: user
Notes: feature sequence A->B->C->D; NFR A+B

## Final Requirements

- REQ-SP-FINETUNE-001: SPipe records research, data download commands, base model choice, tuning
  method, training script path, model artifact path, evaluation result, and
  retry decision for each attempt.
- REQ-SP-FINETUNE-002: The process supports app/server development by linking each app build to the
  model attempt used for implementation assistance or runtime inference.
- REQ-SP-FINETUNE-003: Verification can mark an attempt as accepted, retry-implementation,
  retry-tuning-method, retry-data-research, retry-base-model, or try-other-way.
- REQ-SP-FINETUNE-004: SPipe downloads datasets into a configured cache, prepares instruction data,
  selects an open base model, runs QLoRA/LoRA fine-tuning, evaluates, records
  metrics, and retries with another model or hyperparameter set when targets
  fail.
- REQ-SP-FINETUNE-005: SPipe records provider model choices, provider upload/download steps, tuning
  job IDs, eval results, and retry decisions.
- REQ-SP-FINETUNE-006: Training scripts are provider adapters rather than local trainer scripts.
- REQ-SP-FINETUNE-007: SPipe tries retrieval/context engineering first, then provider fine-tuning or
  local QLoRA only when eval failures show durable behavior gaps.
- REQ-SP-FINETUNE-008: Every attempt records why the chosen method is appropriate or why another way
  was tried.
- REQ-SP-FINETUNE-009: Default base-model candidates are chosen during design for code/app-server
  work and recorded per run.
- REQ-SP-FINETUNE-RETRY6-001: Retry6 shall remain a training/eval handoff gate
  that fails closed until retry5 licensed cache review passes, a deployable
  model manifest exists, and target eval reaches the selected threshold. It may
  report review-required evidence, but it shall not mark acceptance allowed.
- REQ-SP-FINETUNE-RETRY7-001: Retry7 shall remain a normal-review acceptance
  gate that fails closed until retry6 model/eval evidence, accepted decision,
  license constraints, safety evaluation, deployment evidence, and app handoff
  evidence are all concrete and release-ready.
