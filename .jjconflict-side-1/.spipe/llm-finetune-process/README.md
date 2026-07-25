# SPipe LLM Fine-Tune Process

This host state directory records LLM-backed app/server development attempts.

The process is intentionally record-first:

1. Research the task and data sources.
2. Record data download commands and license/checksum evidence.
3. Choose a base LLM model during design.
4. Choose the tuning method.
5. Record the training script and command.
6. Record the model artifact and eval result.
7. Verify performance and route retry to implementation, data, model choice,
   tuning method, or another non-training approach.

Final SPipe fine-tune process requirements are selected in the host docs. Use
`attempts/template.sdn` for new attempts, then keep the attempt record and all
registries in sync before claiming status.

## Commands

Initialize host state:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-init
```

Create a new attempt record:

```sh
.spipe/llm-finetune-process/scripts/new_attempt.shs <attempt_id> <goal> [app_or_server_target]
```

Verify a filled attempt record:

```sh
.spipe/llm-finetune-process/scripts/verify_attempt.shs .spipe/llm-finetune-process/attempts/<attempt_id>.sdn
```

The verifier delegates to `spipe fine-tune-verify` when the separated SPipe CLI
is available. Its fallback path checks the same full evidence shape: research,
data, requirement selection, process docs, model research, base model, tuning,
training artifact, evaluation, decision, and app/server handoff.

The checked-in `attempts/llm_backed_app_server_dry_run.sdn` record exercises the
retry loop with existing MedGemma Korean evidence. It records the best available
artifact found locally, but does not claim production readiness because the
artifact missed the target eval threshold. The linked retry attempt
`llm_backed_app_server_dry_run_retry1` has complete registry evidence and owns
the fixed-format/data-quality retry. It must continue to fail `fine-tune-ready`
until target-reaching eval evidence supports an accepted decision.
The linked retry attempt `llm_backed_app_server_dry_run_retry2` records the
repo-local fixed-format synthetic MCQ data-quality gate and routes to
`retry-implementation`; it also must continue to fail `fine-tune-ready` because
no new model artifact or accepted target eval exists yet.
The linked retry attempt `llm_backed_app_server_dry_run_retry3` records a local
implementation dry-run artifact/eval manifest after the fixed-format gate. It
must continue to fail `fine-tune-ready` because the artifact is marked
`deployable=false` and no target-reaching trained model has been accepted.
The linked retry attempt `llm_backed_app_server_dry_run_retry4` records the
license/data-access gate before real QLoRA. It must continue to fail
`fine-tune-ready` because no licensed data cache, model artifact, target eval,
or accepted decision exists yet.
The linked retry attempt `llm_backed_app_server_dry_run_retry5` records the
current licensed data acquisition and cache/checksum gate. The generic
`fine-tune-ready` command currently fails this attempt on its own readiness
surface: `model_artifact_created=pending`, `target_eval_reached=pending`, and
`decision_accepted=pending`. License approval, cache path, checksum, and app
handoff are checked by the retry5 wrappers below before any accepted decision or
deployment claim.
The linked retry attempt `llm_backed_app_server_dry_run_retry6` records the
real-training/eval gate after retry5. It must continue to fail readiness until
retry5 review passes, a real QLoRA model manifest exists, target eval reaches
the selected threshold, and normal review records accepted app handoff evidence.

Retry5 has two local evidence wrappers for normal-review handoff:

```sh
.spipe/llm-finetune-process/scripts/check_retry5_cache_manifest.shs \
  llm_backed_app_server_dry_run_retry5 \
  .spipe/llm-finetune-process/data/llm_backed_app_server_dry_run_retry5_cache_manifest.sdn

.spipe/llm-finetune-process/scripts/check_retry5_review_handoff.shs \
  llm_backed_app_server_dry_run_retry5
```

`check_retry5_cache_manifest.shs` reports `STATUS: WARN
retry5-cache-manifest` while the manifest is missing or incomplete, and only
reports PASS when `license_review=approved`, `data_access=granted`, the cache
path exists, and the recorded checksum matches the cached file. The output
includes `manifest_exists`, `cache_path_exists`, `expected_checksum`,
`actual_checksum`, `checksum_match`, and `training_allowed`.

`check_retry5_review_handoff.shs` combines the attempt verifier, cache manifest
gate, and data-access gate. It may report `STATUS: PASS
retry5-review-handoff` when the licensed cache is ready for real QLoRA, but it
still emits `acceptance_allowed=false`; target eval and app handoff evidence
remain mandatory before any accepted decision or deployment claim.

Retry6 has a local evidence wrapper for the real-training/eval handoff:

```sh
.spipe/llm-finetune-process/scripts/check_retry6_training_eval_gate.shs \
  llm_backed_app_server_dry_run_retry6
```

The retry6 checker first reads retry5 normal-review status. While retry5 is not
`PASS`, retry6 reports `STATUS: WARN retry6-training-eval-gate`,
`training_allowed=false`, and `acceptance_allowed=false`. After retry5 passes,
the same checker requires retry6 model and target-eval artifacts before normal
review may inspect the attempt. The model manifest must be deployable, and the
eval artifact must expose a numeric `target_accuracy` or `final_accuracy` that
meets the required 90.0 threshold. File presence alone is not enough. It never
marks acceptance allowed by itself.

Record data-download evidence:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-data <attempt_id> <name> <source> <license> <download_command> <cache_path> [checksum]
```

Inspect recorded data downloads and cache/checksum checks:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-data-plan <attempt_id>
```

Record data cache/checksum verification evidence after a download or deliberate
skip:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-data-check <attempt_id> <name> <cache_path> <result> [checksum] [notes]
```

Record research/requirements/plan/design trace:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-process <attempt_id> <research_doc> <requirements_doc> <nfr_doc> <plan_doc> <architecture_doc> <design_doc>
```

Create starter research, requirement option, NFR option, plan, architecture,
and design docs, then record the process trace:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-scaffold-process-docs <attempt_id> <feature_slug> [title]
```

Record the selected feature/NFR requirement options:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-requirements <attempt_id> <feature_option> <nfr_option> <selected_by> <selection_doc> [notes]
```

List the current host requirement options:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-options
```

After the user selects feature and NFR options, write final requirement docs,
delete the option files, and record the attempt selection:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-select-requirements <attempt_id> <feature_option> <nfr_option> <selected_by> [notes]
```

Record base-model selection evidence:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-model <attempt_id> <base_model> <revision> <reason> <deployment_target>
```

Record candidate model research before selection:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-model-research <attempt_id> <candidate_model> <license> <context_length> <fit> <constraints> <decision>
```

List researched candidates and supported tuning methods:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-model-method-options <attempt_id>
```

Record the base model and tuning method selected during design:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-select-model-method <attempt_id> <base_model> <revision> <deployment_target> <method> <selected_by> <fallback> [reason]
```

Record new-model architecture evidence:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-model-arch <attempt_id> <architecture_doc> <model_family> <data_strategy> <training_strategy> <deployment_target> <fallback>
```

Write a new-model/adapter architecture doc scaffold and record it:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-scaffold-model-arch <attempt_id> <architecture_doc> <model_family> <data_strategy> <training_strategy> <deployment_target> <fallback>
```

Record tuning-method selection evidence:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-method <attempt_id> <method> <reason> <fallback> <selected_by>
```

Record training/tuning evidence:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-training <attempt_id> <method> <training_script> <training_command> <model_artifact>
```

Create an executable training script scaffold and record it:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-scaffold-training <attempt_id> <method> <script_path> [model_artifact]
```

Record evaluation evidence:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-eval <attempt_id> <eval_command> <metrics> <target> <result>
```

Record verification decision and retry routing:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-decision <attempt_id> <status> <retry_target> [next_attempt] [notes]
```

Record evaluation plus decision evidence together, and create the retry attempt
when a failed decision includes `next_attempt`:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-verify-loop <attempt_id> <eval_command> <metrics> <target> <result> <status> <retry_target> [next_attempt] [notes]
```

Create the next retry attempt from a failed decision and record the retune
handoff:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-create-retry <source_attempt_id> <next_attempt_id> [goal] [target]
```

Audit an attempt across all evidence registries:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-status <attempt_id>
```

When a `data_checks.sdn` row records a repo-local executable `checker` under
`.spipe/llm-finetune-process/scripts/*.shs`, `fine-tune-status` also runs that
checker and prints `data_check_execution` plus the checker `STATUS:` line. For
retry gates that emit key/value evidence, status also surfaces fields such as
`result`, `target_accuracy`, `required_accuracy`, `target_eval_reached`, and
`acceptance_allowed` so operators do not need to re-run the shell checker to
understand the blocker. A WARN checker means registry rows exist but the
data/cache or model/eval gate is not ready.

Check evidence quality, placeholders, and next readiness action:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-doctor <attempt_id>
```

`fine-tune-doctor` exits nonzero for WARN/FAIL states. Treat that exit as
expected when the printed `next_action` routes an unfinished retry. If the
attempt has a checker, doctor prints the same gate fields as status before the
next-action summary.

Check whether an attempt is ready for real training/use:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-ready <attempt_id>
```

Print the next phase required before real training/use:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-next <attempt_id>
```

`fine-tune-next` exits nonzero unless the attempt is ready. It prints
`STATUS: WARN llm-finetune-next` for non-ready next actions and
`STATUS: PASS llm-finetune-next` only when the next action is `ready`. In shell
automation, capture its output explicitly instead of chaining it as a green
check for retry states.

An attempt is expected to fail `fine-tune-ready` until it has an accepted
decision backed by target-reaching eval evidence. When the best available model
artifact misses target, record the failure, create a retry attempt, and file the
remaining work in `doc/08_tracking/todo/todo_db.sdn` and
`doc/08_tracking/feature_request/` before handoff.

Generate a consolidated handoff report:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-report <attempt_id>
```

Record LLM-backed app/server handoff and retune routing:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-app <attempt_id> <app_target> <usage> <handoff_doc> <license_constraints> <safety_eval> <deployment_evidence>
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-record-retune <attempt_id> <reason> <source_eval> <next_attempt> <retry_target>
```

The app/server handoff is not production evidence unless it records the model
license/distribution constraints, safety evaluation coverage, and deployment
runtime/memory/latency/fallback evidence.

Print the app/server handoff evidence for verification:

```sh
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-app-handoff <attempt_id>
```

## Reusable SPipe Source

The reusable process guide and template are supplied by the SPipe project:

- `.spipe/spipe_project/doc/00_llm_process/spipe/llm_finetune.md`
- `.spipe/spipe_project/doc/00_llm_process/spipe/llm_finetune_attempt_template.sdn`

The compatibility mount exposes the same files through
`doc/00_llm_process/spipe/` after host link setup.
