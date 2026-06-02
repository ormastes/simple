# System Test Plan: SPipe LLM Fine-Tune Process

Date: 2026-06-02

## Goal

Verify that SPipe is separated into a reusable project while the Simple host can
link it, initialize fine-tune evidence, record LLM-backed app/server attempts,
and route verification failures into retry/retune actions.

## Test Surfaces

- `examples/spipe/scripts/build.sh`
- `.spipe/spipe/scripts/build.sh`
- `scripts/install-spipe-dev-command.shs --check`
- `node examples/spipe/cli/spipe.js doctor .`
- `node examples/spipe/cli/spipe.js fine-tune-status <attempt_id>`
- `node examples/spipe/cli/spipe.js fine-tune-next <attempt_id>`
- `node examples/spipe/cli/spipe.js fine-tune-verify <record.sdn>`

## Required Scenarios

1. Submodule separation:
   - `.gitmodules` contains `.spipe/spipe` and `examples/spipe`.
   - Parent index records both paths as `160000` gitlinks.
   - `examples/spipe` and `.spipe/spipe` match apart from `.git`.

2. Host link wiring:
   - `.spipe/doc` resolves to configured host doc root.
   - `.spipe/spipe_project` resolves to `examples/spipe`.
   - Common links for domain expert, SPipe docs, template, project expert, and
     tool expert resolve into the separated SPipe project.

3. Fine-tune process evidence:
   - `fine-tune-init` creates all required registries.
   - Data downloads and data checks can be recorded.
   - Process docs can be scaffolded and recorded.
   - Requirement selection is recordable but not auto-selected.
   - Model research and model architecture can be recorded.
   - Base-model and tuning-method selections can be recorded.
   - Training script scaffolding and training evidence can be recorded.
   - Eval and decision evidence can be recorded.
   - Retry attempts and retune requests can be created.
   - App/server handoff can be recorded and reported.

4. Readiness behavior:
   - Missing attempt reports `next_action=create-attempt`.
   - Seeded dry-run attempt reports `next_action=requirements-selection`.
   - Complete accepted attempt reports `next_action=ready`.
   - Placeholder or incomplete attempt fails `fine-tune-ready`.

5. Layout guard:
   - `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Current Automated Coverage

The two SPipe build scripts cover scenarios 1 through 4 with temporary host
fixtures and full attempt-record verification. The repository-level installer
check covers SPipe command routing. The `doc/06_spec` guard covers scenario 5.

## Manual Gate

Final requirements remain blocked by user choice. Do not generate
`doc/02_requirements/feature/spipe_llm_finetune_process.md` or
`doc/02_requirements/nfr/spipe_llm_finetune_process.md` until the user selects
one feature option and one NFR option.
