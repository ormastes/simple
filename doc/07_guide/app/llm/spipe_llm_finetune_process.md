# SPipe LLM Fine-Tune Process Guide

Operator guide for the SPipe LLM fine-tune retry loop and retry7 acceptance
gate.

## Purpose

The fine-tune process records model, data, training, evaluation, safety,
deployment, app handoff, and retry-decision evidence before any LLM-backed
app/server work can claim a tuned model is release-ready.

Retry7 is the normal-review acceptance gate. It must stay blocked until retry6
or a successor attempt has real training and target-evaluation evidence plus
accepted license, safety, deployment, app-handoff, and final decision records.

Use this guide with:

- `doc/02_requirements/language/tools/spipe_llm_finetune_process.md`
- `doc/02_requirements/nfr/spipe_llm_finetune_process.md`
- `doc/03_plan/ml/spipe_llm_finetune_process.md`
- `doc/03_plan/agent_tasks/spipe_llm_finetune_process_parallel_agent_plan.md`
- `doc/04_architecture/app/spipe/spipe_llm_finetune_process.md`
- `doc/05_design/app/spipe/spipe_llm_finetune_process.md`

## Retry7 Contract

Retry7 is not a training attempt. It wraps the upstream retry6 training/eval
gate and normal-review acceptance requirements.

Expected blocked evidence includes:

- missing licensed data cache or checksum evidence
- missing deployable model manifest
- missing target-evaluation pass
- pending license-constraints review
- safety evaluation not run
- deployment evidence marked not deployable
- missing app-handoff document
- missing accepted normal-review decision

Public status surfaces must render those blockers as explicit text such as
`pending`, `false`, `not-run`, `not-deployable`, `WARN`, or `BLOCKED`.
Operator-facing output must not expose internal absence markers.

## Commands

Run retry7 status through the SPipe CLI:

```bash
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-status \
  llm_backed_app_server_dry_run_retry7
```

Run the direct retry7 acceptance gate:

```bash
.spipe/llm-finetune-process/scripts/check_retry7_acceptance_gate.shs \
  llm_backed_app_server_dry_run_retry7
```

Run the local guard evidence wrapper:

```bash
sh scripts/check/check-llm-finetune-guard-evidence.shs
```

This wrapper is the canonical local non-training check. It runs the
fixed-format sample quality gate, retry6 and retry7 direct gates, and the
retry6/retry7 SSpec manuals. For the checked-in dry-run records it should pass
only when retry6 and retry7 still report the expected WARN/blocked state. Its
env records `llm_finetune_guard_required_gates`,
`llm_finetune_guard_blocked_gates`,
`llm_finetune_guard_primary_blocked_gate`,
`llm_finetune_guard_blocker_reason`, and
`llm_finetune_guard_next_action`, so default aggregate evidence can report the
current guard blocker without reading a stale acceptance env.

Run strict ready mode only when tuned-model acceptance evidence is expected to
exist:

```bash
sh scripts/check/check-llm-finetune-acceptance-evidence.shs
```

The acceptance checker writes `build/llm_finetune_acceptance/evidence.env`.
It passes only when retry7 itself reports `STATUS: PASS retry7-acceptance-gate`
and `acceptance_allowed=true`; otherwise it records the concrete model,
target-eval, license, safety, deployment, app-handoff, and normal-review
blockers and keeps `llm_finetune_acceptance_status=fail`.

```bash
FINETUNE_ACCEPTANCE_EVIDENCE_ENV=build/llm_finetune_acceptance/evidence.env \
  sh scripts/check/check-llm-finetune-guard-evidence.shs --strict-ready
```

Strict ready mode requires the evidence env to contain
`llm_finetune_acceptance_status=pass`. The local guard pass is intentionally not
training, target-eval, safety, deployment, app-handoff, or normal-review
acceptance proof; the current retry7 dry-run should remain failed until those
records are real.

Run readiness only when upstream evidence is expected to be complete:

```bash
node examples/05_stdlib/spipe/cli/spipe.js fine-tune-ready \
  llm_backed_app_server_dry_run_retry7
```

For the current dry-run retry7 record, a warning or blocked result is the
correct outcome. A pass without real licensed data, model/eval, safety,
deployment, app handoff, and accepted-decision evidence is a process bug.

## Evidence Locations

Primary retry7 evidence:

- `.spipe/llm-finetune-process/attempts/llm_backed_app_server_dry_run_retry7.sdn`
- `.spipe/llm-finetune-process/scripts/check_retry7_acceptance_gate.shs`
- `scripts/check/check-llm-finetune-acceptance-evidence.shs`
- `scripts/check/check-llm-finetune-guard-evidence.shs`
- `test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.spl`
- `doc/06_spec/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.md`
- `doc/09_report/2026/06/llm_finetune_guard_evidence_2026-06-28.md`

Related upstream gates:

- retry5 licensed data/cache evidence
- retry6 training/eval gate evidence
- `.spipe/llm-finetune-process/app_handoffs.sdn`
- `.spipe/llm-finetune-process/retry_decisions.sdn`

## Handoff Rules

Before promoting retry7:

1. Confirm retry5 licensed cache/checksum evidence is real.
2. Confirm retry6 or successor training created a deployable model manifest.
3. Confirm target evaluation reached the selected threshold.
4. Confirm license constraints, safety evaluation, deployment evidence, and app
   handoff records are concrete.
5. Record the accepted normal-review decision with the exact model artifact,
   eval command/result, license constraints, safety eval, deployment evidence,
   and app handoff.
6. Re-run the guard evidence wrapper, retry7 gate, and generated manual quality
   checks once.

For aggregate LLM completion evidence, `scripts/check/check-llm-goal-evidence.shs
--strict-host` runs this wrapper with `--strict-ready`, so a missing tuned-model
acceptance env keeps the fine-tune lane failed instead of treating blocked
guard evidence as release readiness.

Do not repair stale generated specs or process docs during release. Update this
guide, the generated/manual spec doc, and the relevant plan first, then verify.
