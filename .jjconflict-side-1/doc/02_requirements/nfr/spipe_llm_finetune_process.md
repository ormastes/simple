# SPipe LLM Fine-Tune Process NFR Requirements

Selected NFR sequence: Auditability First -> Reproducibility First
Selected by: user
Notes: feature sequence A->B->C->D; NFR A+B

## Final Targets

- Every tuning attempt has a durable `.sdn` record with source data, model,
  trainer, script, eval command, metrics, and retry decision.
- Records must be usable without opening transient logs.
- Training scripts are deterministic where the trainer supports seeds.
- Data downloads include source URL, license note, checksum when available, and
  cache path.
- Model artifacts include base revision, adapter revision, and eval fixture
  revision.
