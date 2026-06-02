# Local Research: SPipe LLM Fine-Tune Process

Date: 2026-06-02

## Scope

Research current Simple repository support for separating SPipe into its own
project while keeping host-local LLM fine-tune process state under `.spipe/`.

## Current Implementation Evidence

- `.gitmodules` declares both `.spipe/spipe` and `examples/spipe` using
  `https://github.com/ormastes/Spipe.git`.
- Parent index records `.spipe/spipe` and `examples/spipe` as gitlinks.
- `.spipe/spipe_project` links to `examples/spipe`.
- `.spipe/doc` links to this host project's configured process docs:
  `doc/00_llm_process`.
- `.spipe/config.sdn` sets the host override from the generic default
  `doc/llm_process` to `doc/00_llm_process`.
- `.spipe/domain_expert`, `.spipe/template`, `.spipe/spipe_docs`,
  `.spipe/project_expert/spipe`, and `.spipe/tool_expert/spipe_submodule`
  link common process/expert roots from the separated SPipe project.

## SPipe Package Surface

The separated SPipe project exposes:

- CLI: `examples/spipe/cli/spipe.js`
- MCP server: `examples/spipe/mcp/server.js`
- Package manifest: `examples/spipe/package.json`
- Plugin manifest: `examples/spipe/plugin/.codex-plugin/plugin.json`
- Build guard: `examples/spipe/scripts/build.sh`

The CLI supports host link inspection, doctor checks, process doc linking,
fine-tune attempt initialization, data download recording, data cache/check
recording, process doc tracing, requirement option recording, model research,
model architecture, base-model and tuning-method selection, training script
recording/scaffolding, evaluation, retry decisions, app/server handoff, retune
requests, readiness checks, next-step reporting, and consolidated reporting.

## Host Fine-Tune State

Host state lives under `.spipe/llm-finetune-process/` and includes registries
for attempts, data downloads, data checks, process docs, requirement selection,
model research, model architecture, base models, tuning methods, training
scripts, evaluations, decisions, app handoffs, and retune requests.

The seeded attempt `llm_backed_app_server_dry_run` has all registry files
present and currently reports:

- `STATUS: PASS llm-finetune-status`
- `next_action=requirements-selection`

This is correct because final requirements must not be selected by an agent.

## Verification Evidence

Current guards cover:

- `spipe doctor .` host link and common-surface checks.
- `sh examples/spipe/scripts/build.sh` separated project smoke.
- `sh .spipe/spipe/scripts/build.sh` compatibility mount smoke.
- `sh scripts/install-spipe-dev-command.shs --check` SPipe command routing.
- `find doc/06_spec -name '*_spec.spl' | wc -l` layout invariant.
- `diff -qr -x .git examples/spipe .spipe/spipe` checkout drift invariant.

## Gaps / Open Items

- User must select feature option A/B/C/D and NFR option A/B/C before final
  requirement files are generated.
- Release/push is not started because verification cannot be final while
  requirement selection is open.
