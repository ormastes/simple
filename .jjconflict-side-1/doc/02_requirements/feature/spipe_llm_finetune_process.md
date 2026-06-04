# SPipe LLM Fine-Tune Process Requirements

Selected feature sequence: Fine-Tune Process Scaffold -> Local QLoRA-First Tuning Pipeline -> Provider Fine-Tune Adapter Pipeline -> Hybrid Tuning and Retrieval Loop
Selected by: user
Notes: feature sequence A->B->C->D; NFR A+B

## Final Requirements

- SPipe records research, data download commands, base model choice, tuning
  method, training script path, model artifact path, evaluation result, and
  retry decision for each attempt.
- The process supports app/server development by linking each app build to the
  model attempt used for implementation assistance or runtime inference.
- Verification can mark an attempt as accepted, retry-implementation,
  retry-tuning-method, retry-data-research, retry-base-model, or try-other-way.
- SPipe downloads datasets into a configured cache, prepares instruction data,
  selects an open base model, runs QLoRA/LoRA fine-tuning, evaluates, records
  metrics, and retries with another model or hyperparameter set when targets
  fail.
- SPipe records provider model choices, provider upload/download steps, tuning
  job IDs, eval results, and retry decisions.
- Training scripts are provider adapters rather than local trainer scripts.
- SPipe tries retrieval/context engineering first, then provider fine-tuning or
  local QLoRA only when eval failures show durable behavior gaps.
- Every attempt records why the chosen method is appropriate or why another way
  was tried.
- Default base-model candidates are chosen during design for code/app-server
  work and recorded per run.
