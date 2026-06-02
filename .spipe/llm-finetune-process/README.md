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

Until final requirements are selected, use `attempts/template.sdn` for dry-run
planning only.

## Commands

Initialize host state:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-init
```

Create a new attempt record:

```sh
.spipe/llm-finetune-process/scripts/new_attempt.sh <attempt_id> <goal> [app_or_server_target]
```

Verify a filled attempt record:

```sh
.spipe/llm-finetune-process/scripts/verify_attempt.sh .spipe/llm-finetune-process/attempts/<attempt_id>.sdn
```

The checked-in `attempts/llm_backed_app_server_dry_run.sdn` record exercises the
retry loop without claiming that a model has been trained.

Record data-download evidence:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-data <attempt_id> <name> <source> <license> <download_command> <cache_path> [checksum]
```

Inspect recorded data downloads and cache/checksum checks:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-data-plan <attempt_id>
```

Record data cache/checksum verification evidence after a download or deliberate
skip:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-data-check <attempt_id> <name> <cache_path> <result> [checksum] [notes]
```

Record research/requirements/plan/design trace:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-process <attempt_id> <research_doc> <requirements_doc> <nfr_doc> <plan_doc> <architecture_doc> <design_doc>
```

Create starter research, requirement option, NFR option, plan, architecture,
and design docs, then record the process trace:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-scaffold-process-docs <attempt_id> <feature_slug> [title]
```

Record the selected feature/NFR requirement options:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-requirements <attempt_id> <feature_option> <nfr_option> <selected_by> <selection_doc> [notes]
```

List the current host requirement options:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-options
```

After the user selects feature and NFR options, write final requirement docs,
delete the option files, and record the attempt selection:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-select-requirements <attempt_id> <feature_option> <nfr_option> <selected_by> [notes]
```

Record base-model selection evidence:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-model <attempt_id> <base_model> <revision> <reason> <deployment_target>
```

Record candidate model research before selection:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-model-research <attempt_id> <candidate_model> <license> <context_length> <fit> <constraints> <decision>
```

List researched candidates and supported tuning methods:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-model-method-options <attempt_id>
```

Record the base model and tuning method selected during design:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-select-model-method <attempt_id> <base_model> <revision> <deployment_target> <method> <selected_by> <fallback> [reason]
```

Record new-model architecture evidence:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-model-arch <attempt_id> <architecture_doc> <model_family> <data_strategy> <training_strategy> <deployment_target> <fallback>
```

Write a new-model/adapter architecture doc scaffold and record it:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-scaffold-model-arch <attempt_id> <architecture_doc> <model_family> <data_strategy> <training_strategy> <deployment_target> <fallback>
```

Record tuning-method selection evidence:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-method <attempt_id> <method> <reason> <fallback> <selected_by>
```

Record training/tuning evidence:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-training <attempt_id> <method> <training_script> <training_command> <model_artifact>
```

Create an executable training script scaffold and record it:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-scaffold-training <attempt_id> <method> <script_path> [model_artifact]
```

Record evaluation evidence:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-eval <attempt_id> <eval_command> <metrics> <target> <result>
```

Record verification decision and retry routing:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-decision <attempt_id> <status> <retry_target> [next_attempt] [notes]
```

Record evaluation plus decision evidence together, and create the retry attempt
when a failed decision includes `next_attempt`:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-verify-loop <attempt_id> <eval_command> <metrics> <target> <result> <status> <retry_target> [next_attempt] [notes]
```

Create the next retry attempt from a failed decision and record the retune
handoff:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-create-retry <source_attempt_id> <next_attempt_id> [goal] [target]
```

Audit an attempt across all evidence registries:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-status <attempt_id>
```

Check evidence quality, placeholders, and next readiness action:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-doctor <attempt_id>
```

Check whether an attempt is ready for real training/use:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-ready <attempt_id>
```

Print the next phase required before real training/use:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-next <attempt_id>
```

The dry-run attempt is expected to fail `fine-tune-ready` until requirements,
base model, real tuning method, model artifact, and accepted decision evidence
are recorded.

Generate a consolidated handoff report:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-report <attempt_id>
```

Record LLM-backed app/server handoff and retune routing:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-record-app <attempt_id> <app_target> <usage> <handoff_doc>
node .spipe/spipe_project/cli/spipe.js fine-tune-record-retune <attempt_id> <reason> <source_eval> <next_attempt> <retry_target>
```

Print the app/server handoff evidence for verification:

```sh
node .spipe/spipe_project/cli/spipe.js fine-tune-app-handoff <attempt_id>
```

## Reusable SPipe Source

The reusable process guide and template are supplied by the SPipe project:

- `.spipe/spipe_project/doc/00_llm_process/spipe/llm_finetune.md`
- `.spipe/spipe_project/doc/00_llm_process/spipe/llm_finetune_attempt_template.sdn`

The compatibility mount exposes the same files through
`doc/00_llm_process/spipe/` after host link setup.
