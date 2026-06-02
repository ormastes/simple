# SPipe LLM Fine-Tune Process Agent Tasks

## Current Gate

Requirement selection is complete. Final feature and NFR requirements are in
`doc/02_requirements/feature/spipe_llm_finetune_process.md` and
`doc/02_requirements/nfr/spipe_llm_finetune_process.md`; unchosen option docs
have been removed.

## Implementation Slices

1. Done: add SPipe host config and links for separated project mounting.
2. Done: add `.spipe/spipe` and `examples/spipe` as SPipe submodule mounts.
3. Done: add attempt record schema and registries under
   `.spipe/llm-finetune-process/`.
4. Done: add CLI/MCP package surface for SPipe docs and fine-tune process.
5. Done: add data download, data check, model research, model architecture,
   model selection, tuning method selection, training script, eval, decision,
   app handoff, and retune records.
6. Done: add readiness/next/report/verify commands for fine-tune attempts.
7. Done: add host and package guards for SPipe links, gitlinks, package bins,
   MCP tools, and `doc/06_spec` layout.
8. Done: generate final feature/NFR requirements after the user selected the
   feature A->B->C->D and NFR A+B path.
9. Done: delete unchosen option docs.
10. Pending: run final verify and prepare release handoff.
