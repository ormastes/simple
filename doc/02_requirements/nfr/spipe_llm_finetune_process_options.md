# SPipe LLM Fine-Tune Process NFR Options

## Option A: Auditability First

Targets:
- Every tuning attempt has a durable `.sdn` record with source data, model,
  trainer, script, eval command, metrics, and retry decision.
- Records must be usable without opening transient logs.

Pros: Strong traceability and low implementation risk.
Cons: Does not guarantee fast training or best model quality.
Effort: Medium.

## Option B: Reproducibility First

Targets:
- Training scripts are deterministic where the trainer supports seeds.
- Data downloads include source URL, license note, checksum when available, and
  cache path.
- Model artifacts include base revision, adapter revision, and eval fixture
  revision.

Pros: Better scientific and release evidence.
Cons: More setup burden for each data/model source.
Effort: High.

## Option C: Cost and Hardware Guardrails First

Targets:
- Each run declares max wall time, max GPU memory target, max provider spend,
  and max artifact size before training starts.
- Verification fails attempts that exceed declared limits.

Pros: Useful for production tuning loops.
Cons: Harder to implement portably across local and provider trainers.
Effort: High.

## Selection Needed

Choose exactly one NFR option before final NFR requirements are generated:

- A: Auditability First
- B: Reproducibility First
- C: Cost and Hardware Guardrails First

After selection, SPipe writes
`doc/02_requirements/nfr/spipe_llm_finetune_process.md`, records the choice in
`.spipe/llm-finetune-process/requirements_selection.sdn`, and deletes this
options file as required by the pipeline.
