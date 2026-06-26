# SPipe LLM Fine-Tune Process Detail Design

## Records

Attempt records live under `.spipe/llm-finetune-process/attempts/`.

Host registries live beside the attempt records:

- `attempts.sdn`
- `data_downloads.sdn`
- `data_checks.sdn`
- `process_docs.sdn`
- `requirements_selection.sdn`
- `model_research.sdn`
- `model_architecture.sdn`
- `models.sdn`
- `tuning_methods.sdn`
- `training_scripts.sdn`
- `eval_results.sdn`
- `decisions.sdn`
- `app_handoffs.sdn`
- `retune_requests.sdn`

The attempt template contains sections for goal, research, data sources,
requirements, process docs, model research, model architecture, base model,
tuning, evaluation, decision, app handoff, and retune.

## Process Doc Trace

Each attempt can record:

- local/domain research docs
- feature and NFR requirement docs or selected option evidence
- agent plan
- architecture doc
- detail design doc

SPipe can scaffold these docs, but final requirement docs are generated only
after the user chooses one feature option and one NFR option.

## Base Model Choice

The design phase must choose the base model for each run from documented
criteria: task fit, license, context length, tool/code capability, deployment
target, hardware/provider constraints, and expected tuning method.

Candidate model research records include candidate ID, license, context length,
fit, constraints, and decision. The selected model record includes base model,
revision, reason, and deployment target.

Default design guidance:

- Prefer provider fine-tuning when local hardware is unavailable or the target
  app already depends on a hosted provider.
- Prefer local QLoRA/LoRA when model/data ownership, offline use, or artifact
  reproducibility is more important than provider convenience.
- Prefer retrieval, prompt, or tool protocol changes before weight tuning when
  eval failures are caused by missing context, weak tools, or app behavior.
- Prefer a new adapter/model architecture only when base-model candidates and
  simpler tuning methods cannot satisfy the target constraints.

## Tuning Methods

Supported method records:
- retrieval-or-context update
- prompt/tool protocol update
- provider fine-tune
- local LoRA/QLoRA
- full fine-tune

The selected tuning method records method, reason, fallback, and selector. The
combined selection command records both base model and tuning method so design
handoff evidence is a single auditable step.

## Training Script Records

Every training attempt records the script path and the exact command used. A
model artifact without a script record is not release evidence.

Provider-managed jobs use `provider-managed` as the script marker and still
record the provider command/job reference and output model ID. Local jobs use an
executable script under `.spipe/llm-finetune-process/scripts/`.

## Verification Loop

If performance is not proper, verification records the failure class and retry
target. Retry can return to implementation, data research, base model selection,
tuning method selection, or app/server design.

Retry targets:

- `retry-implementation`
- `retry-data-research`
- `retry-base-model`
- `retry-tuning-method`
- `try-other-way`

`fine-tune-record-verify-loop` records evaluation plus decision evidence
together and can create the next attempt when a retry attempt is named.

## LLM-Backed App/Server Handoff

App/server development records:

- app or server target
- whether the model was used for implementation assistance, runtime inference,
  or both
- handoff doc path
- retune reason and source eval when verification asks for another attempt

The handoff report is the compact artifact an app/server implementation can cite
when it depends on a tuned model or requests retuning.

## Verification Commands

Key release evidence commands:

- `spipe doctor .`
- `spipe fine-tune-status <attempt_id>`
- `spipe fine-tune-next <attempt_id>`
- `spipe fine-tune-ready <attempt_id>`
- `spipe fine-tune-report <attempt_id>`
- `spipe fine-tune-verify <record.sdn>`
- `sh scripts/check/check-spipe-submodule-gitlinks.shs --check`
- `find doc/06_spec -name '*_spec.spl' | wc -l`

## Host Scripts

Host-local scripts live under `.spipe/llm-finetune-process/scripts/`:

- `new_attempt.sh` creates a record from `attempts/template.sdn`.
- `verify_attempt.sh` checks required research, model, tuning, training script,
  eval, and retry fields.
- `dry_run_training.sh` is a no-training placeholder used only until
  requirements select a real tuning path.
- `check_retry7_acceptance_gate.shs` is a no-training normal-review gate that
  wraps retry6 training/eval evidence and blocks acceptance until real model,
  eval, license, safety, deployment, and accepted-decision evidence exist.
