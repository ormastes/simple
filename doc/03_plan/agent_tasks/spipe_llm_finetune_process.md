# SPipe LLM Fine-Tune Process Agent Tasks

## Current Gate

Requirement selection is still required before full implementation. Start from
`doc/02_requirements/feature/spipe_llm_finetune_process_options.md` and
`doc/02_requirements/nfr/spipe_llm_finetune_process_options.md`.

## Implementation Slices

1. Add SPipe host config and links for separated project mounting.
2. Add attempt record schema under `.spipe/llm-finetune-process/`.
3. Add a dry-run CLI or script that creates a new attempt record.
4. Add data download, model selection, tuning method selection, training script,
   eval, and retry fields to the record.
5. Add verification that fails missing model/script/eval/retry evidence.
6. Add app/server handoff fields so LLM-backed app implementation can cite the
   model attempt used and request retuning from verification failures.
