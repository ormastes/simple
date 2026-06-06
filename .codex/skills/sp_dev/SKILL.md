---
name: sp_dev
description: "SPipe dev entrypoint: refine a feature/bug/TODO into acceptance criteria, then continue through the SPipe pipeline."
---

# SP Dev -- SPipe Development Entrypoint

`/sp_dev` is the Codex entrypoint for the SPipe development workflow. The
standalone `/dev` Codex skill has been removed so development work routes
through the explicit SPipe namespace.

Use it for a feature, bug fix, refactor, or TODO that should start with SPipe
goal refinement and acceptance criteria, then continue through research, design,
SPipe specs, implementation, refactor, verification, and ship handoff:

```
/sp_dev <description of what to build or fix>
```

## Dispatch

Start with the SPipe dev agent instructions in `.claude/agents/spipe/dev.md`.
Use `.claude/skills/spipe.md` for SPipe test/spec conventions when the workflow
reaches specification and verification phases.

During the SPipe Refactor and Ship phases, run the doc/wiki refactor support
skill at `.claude/skills/spipe_doc_wiki_refactor.md` so stale docs, command
references, wiki-style process knowledge, and feature/layer expert links are
cleaned before completion.

When implementation changes add or replace evidence wrappers, refresh the
matching guide/process documentation in the same lane. For GPU, Engine2D, Simple
Web, Electron/Tauri, QEMU, or backend readback evidence, update the relevant
`doc/03_plan`, `doc/07_guide`, and `doc/09_report` references so future agents
can find the canonical wrapper instead of repeating stale commands.

For runtime concurrency work, keep the public API map current in
`doc/07_guide/lib/misc/stdlib.md`, `doc/07_guide/compiler/check_perf.md`, and
`.codex/skills/coding/SKILL.md`. In particular, distinguish `thread_spawn`
(OS thread), `green_spawn` / `green_spawn_value` / `std.concurrent.green_thread`
(implemented cooperative green-thread queue on the current OS thread), and
`task_spawn` (pool-backed native task path when `rt_pool_*` links). Do not
document green-thread APIs as Go-style M:N CPU parallelism unless the
scheduler-aware green runtime has actually landed and been benchmarked.

For dynSMF or SMF-startup work, distinguish three separate lanes before
editing: SimpleOS disk SMF placement, GUI SMF dynlib release evidence, and the
general dynSMF background compile/startup lane. If the request says the
interpreter should compile SMF while reading/running scripts, or mentions
precompiled `build/dynsmf/*.smf` artifacts, start with
`src/os/smf/dynsmf_session.spl`,
`src/app/startup/dynsmf_autoload.spl`, and
`scripts/check/check-low-dependency-dynsmf-build-plans.shs`. This is not
GUI-only: GUI renderer entries and non-GUI entries share the same manifest,
build-plan, `compile_background` evidence, and checked-autoload contract. Update
`doc/07_guide/lib/api/dynlib_api.md`, the low-dependency dynSMF architecture
and design docs, and the matching SPipe specs whenever that contract changes.

For optimization work, use `.codex/skills/optimize/SKILL.md`. SPipe optimization
tasks must start from a baseline, run
`bin/simple run src/app/optimize/main.spl <file> --full --level=O3` on touched
`.spl` files, preserve behavior, and rerun both correctness tests and the same
perf script. Do not rewrite Simple features in C/Rust to claim C-level speed; if
parity is blocked by runtime/compiler behavior, record a measured blocker under
`doc/08_tracking/bug/`.

For UI, GUI, MDI/window-manager, Draw IR, Simple 2D, or Engine2D backend-lane
work, keep the stack architecture current in
`doc/04_architecture/ui/simple_gui_stack.md` and its TLDR companion. If the work
changes shared UI contracts, event propagation, Draw IR source/event metadata,
or the drawing-vs-processing backend split, update the generated/manual spec
docs under `doc/06_spec`, the relevant `doc/07_guide` process note when one
exists, and cite the canonical implementation paths such as
`src/lib/common/ui/draw_ir.spl`,
`src/lib/common/ui/window_scene_draw_ir.spl`, and
`src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`.

For UI-test helper work, keep the test-library surface consistent: new specs
use canonical `use std.spec`, existing `use std.spipe` remains an alias, and
UI/SGTTI/Draw IR helpers must layer inside SPipe scenarios instead of replacing
`describe`, `it`, `expect`, or the built-in matchers.
When a UI change claims layout, border, color, style, or text-bound parity,
prefer the Protocol-v2 Draw IR baseline diff
`/api/test/draw-ir/diff?baseline=...&capability=draw_ir` or the shared
`common.ui.draw_ir_diff` helper as structured evidence before falling back to
pixel-only assertions.

For Simple Web/Electron renderer parity, keep the canonical wrapper documented
as `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`.
Generated-GUI evidence may record explicit `text_normalization_pixels` for
fixture-scoped browser text antialiasing normalization, but must still require
matching checksums, `mismatch_count=0`, and `blur_or_tolerance=false`. Treat
Linux Metal readback as host-unavailable (`metal-requires-macos`) and require
native raw Metal readback evidence on macOS.

Before marking a feature tracking row `status=done`, fill `requirement`,
`research`, `plan`, `architecture`, `design`, `system_spec`, `spec_doc`,
`implementation`, `unit_tests`, `integration_tests`, and `guide`, then run
`<runtime> lint doc/08_tracking/feature/feature_db.sdn`.

If other Codex, Claude, or Gemini sessions are active, identify the lane this
`/sp_dev` invocation owns before editing or syncing. Do not absorb unrelated
dirty files into the feature just because they are present in the shared
checkout. Preserve other-agent work, report it separately, and commit only the
intentional lane unless the user requests a combined integration.

For scenario-oriented work, the SPipe loop also includes generated manual
review. After specs are written or changed, generate the mirrored
`doc/06_spec/...` document and read it as a scenario manual. Update step
helpers, capture policy, inline/previous scenario expansion, and manual
visibility until the generated manual is good enough to use without opening the
source test. See `doc/07_guide/testing/sspec_scenario_manual.md`.

Run `sh scripts/setup/install-spipe-dev-command.shs --check` on Unix-like hosts, or
`powershell -ExecutionPolicy Bypass -File scripts\install-spipe-dev-command.ps1 --check`
on Windows, to verify that this repository still routes Codex development
through `/sp_dev` and does not carry a separate `/dev` skill.

Before handoff, run the generated-spec layout guard:

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
```

The result must be `0`; executable SPipe belongs under `test/`, while
`doc/06_spec` contains generated/manual Markdown and evidence assets only.

## LLM Fine-Tune Handoff

For SPipe LLM-backed app/server work, use the fine-tune registry commands under
`.spipe/llm-finetune-process/`. If an artifact exists but misses its target eval,
record the failed eval, create or link the retry attempt, and file remaining
retry/verification/safety/deployment work in `doc/08_tracking/todo/todo_db.sdn`
and `doc/08_tracking/feature/` before reporting the handoff state.
