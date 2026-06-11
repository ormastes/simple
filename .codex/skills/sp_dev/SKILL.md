---
name: sp_dev
description: "SPipe dev entrypoint: refine a feature/bug/TODO into acceptance criteria, then continue through the SPipe pipeline."
---

# SP Dev -- SPipe Development Entrypoint

`/sp_dev` is the Codex entrypoint for the SPipe development workflow. The
standalone `/dev` Codex skill has been removed so development work routes
through the explicit SPipe namespace. SPipe is the runner/docgen/process layer;
SSpec is the executable `.spl` scenario authoring surface.

Use it for a feature, bug fix, refactor, or TODO that should start with SPipe
goal refinement and acceptance criteria, then continue through research, design,
SSpec scenarios executed through SPipe, implementation, refactor, verification,
and ship handoff:

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
(OS thread), `cooperative_green_spawn` / `cooperative_green_spawn_value`
(implemented cooperative green-thread queue on the current OS thread),
`multicore_green_spawn` (Pure Simple bounded-worker facade over `rt_pool_*`),
and `task_spawn` (pool-backed native task path when `rt_pool_*` links). Do not
document cooperative green-thread APIs as Go-style M:N CPU parallelism. When a
profile or test claims M:N behavior through `multicore_green_spawn`, require
`MulticoreGreenHandle.used_runtime_pool()` evidence so inline fallback cannot
masquerade as CPU-parallel work.

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

For runtime-vs-pure-Simple algorithm work, use the shared dual-backend mode
names consistently in specs, docs, and code:

- `alpha` = current default, run both and stop on diff
- `beta` = run both and log a critical diff report
- `normal` = run only the preferred implementation

Prefer helper names that expose those mode names directly:

- `dual_backend_alpha_default_mode()`
- `dual_backend_beta_default_mode()`
- `dual_backend_normal_pure_simple_mode()`

Keep the legacy `assert/critical/pure_simple` helper names only as temporary
compatibility aliases. New wrappers, examples, and docs should use the
`alpha/beta/normal` helper names.

When a task introduces a new runtime/pure wrapper, update the shared guide at
`doc/07_guide/os/crypto_dual_backend.md` and prefer an explicit
`DualBackendConfig` dependency-injection entrypoint plus a default-config
convenience wrapper. If `normal` mode is meant to avoid dual execution on the
hot path, use the `dual_backend_run_*` lambda-based helpers rather than
precomputing both outputs before comparison.

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

For UI-test helper work, keep the test-library surface consistent: new SSpec
manual specs use canonical `use std.spec.*` and `step("...")`, existing
`use std.spipe` remains an alias, and UI/SGTTI/Draw IR helpers must layer inside
SSpec scenarios instead of replacing `describe`, `it`, `expect`, `step`, or the
built-in matchers. `Given_*`, `When_*`, and `Then_*` helpers are legacy manual
text helpers.
SGTTI is a test/debug evidence interface. Production entrypoints must not import
`std.ui_test.sgtti`, `SgttiTestDriver`, or SGTTI capture builders unless the
specific debug/test entrypoint explicitly opts in; compile-time entry-closure
builds must be able to elide SGTTI entirely. When adding TUI/GUI debug evidence,
include a system spec that proves the normal entrypoint has no SGTTI/debug-TUI
import path.
When a UI change claims layout, border, color, style, or text-bound parity,
prefer the Protocol-v2 Draw IR baseline diff
`/api/test/draw-ir/diff?baseline=...&capability=draw_ir` or the shared
`common.ui.draw_ir_diff` helper as structured evidence before falling back to
pixel-only assertions.
When the question is "where did this GUI component render?", use
`/api/test/draw-ir/layout?id=...&capability=draw_ir` or `expect_draw` to assert
the stable id, role/kind, geometry, hit rect, parent, and computed style inside
the SSpec case.
After adding or moving UI-facing app feature specs, run
`test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl` to keep
the critical UI SSPEC lane mirrored into generated manuals with visible
evidence markers.

For compiler cache, loader, JIT, formal verification, or accessor-forwarding
work, include SPipe evidence for semantic invalidation. A change to public ABI,
field-wrapper shape, forwarded getter/setter behavior, or generated accessor
dependencies must miss the interpreter/incremental cache and any SMF/JIT cache
that could otherwise reuse stale code. Add focused specs near the cache owner
instead of relying only on broad loader suites.

For MCP/runtime-forwarding or startup-latency work, refresh both the lane state
file and `doc/07_guide/app/mcp/startup_performance.md` before handoff. Keep the
guide aligned with the current wrapper contract (native-first, probe-stamped,
no silent source fallback in production), the direct-`rt_*` guard policy, the
interface-cache/source-mtime contract, and the latest local smoke numbers from
`scripts/check/check-mcp-native-smoke.shs`.

Do not write boolean-wrapper assertions in new SPipe specs:
`expect(a == b).to_equal(true)`, `expect(a != b).to_equal(false)`, and similar
forms are quality-gate failures. Assert concrete values directly, or use
`to_be(true/false)` only when the boolean value itself is the unit under test.

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
review. After SSpec `.spl` scenarios are written or changed, generate the
mirrored `doc/06_spec/...` document and read it as a scenario manual. Update
`step("...")` text, capture policy, inline/previous scenario expansion, and manual
visibility until the generated manual is good enough to use without opening the
source test. See `doc/07_guide/infra/sspec_scenario_manual.md`.

Run `sh scripts/setup/install-spipe-dev-command.shs --check` on Unix-like hosts, or
`powershell -ExecutionPolicy Bypass -File scripts\install-spipe-dev-command.ps1 --check`
on Windows, to verify that this repository still routes Codex development
through `/sp_dev` and does not carry a separate `/dev` skill.

Before handoff, run the generated-spec layout guard:

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
```

The result must be `0`; executable SSpec belongs under `test/`, while
`doc/06_spec` contains generated/manual Markdown and evidence assets only.

## LLM Fine-Tune Handoff

For SPipe LLM-backed app/server work, use the fine-tune registry commands under
`.spipe/llm-finetune-process/`. If an artifact exists but misses its target eval,
record the failed eval, create or link the retry attempt, and file remaining
retry/verification/safety/deployment work in `doc/08_tracking/todo/todo_db.sdn`
and `doc/08_tracking/feature/` before reporting the handoff state.
