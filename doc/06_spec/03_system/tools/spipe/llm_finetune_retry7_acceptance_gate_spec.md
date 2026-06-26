# LLM Fine-Tune Retry7 Acceptance Gate Specification

Generated/manual companion for
`test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.spl`.

## Purpose

This system specification verifies that retry7 in the SPipe LLM fine-tune
process is only an acceptance-review gate. It must not mark the fine-tune lane
ready while retry6 is still missing real model, target-eval, safety, deployment,
license, app handoff, and accepted-decision evidence.

## Covered Behavior

- The retry7 gate script is executable and has a concrete attempt record.
- `.spipe/llm-finetune-process/scripts/check_retry7_acceptance_gate.shs` reports
  retry7 as blocked by retry6 training/eval readiness.
- `spipe fine-tune-status llm_backed_app_server_dry_run_retry7` surfaces the
  retry7 gate as `data_check_execution=warn`.
- `spipe fine-tune-ready llm_backed_app_server_dry_run_retry7` fails until
  model artifact, target eval, and accepted decision evidence exist.
- Public gate and CLI output must not expose raw internal `nil` values.

## Verification

```bash
release/x86_64-unknown-linux-gnu/simple check test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.spl
release/x86_64-unknown-linux-gnu/simple test test/03_system/tools/spipe/llm_finetune_retry7_acceptance_gate_spec.spl --mode=interpreter --clean
```

