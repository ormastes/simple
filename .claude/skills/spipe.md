---
name: spipe
description: SPipe Skill — Simple Pipe (spec → test → report). BDD test writing, matchers, file structure, doc generation. Use when writing or editing `*_spec.spl` test files, debugging matcher failures, or scaffolding from `.claude/templates/spipe_template.spl`. Renamed from `sspec` on 2026-04-26.
---

# SPipe — Simple Pipe (spec → test → report)

The SPipe dev entrypoint lives at:

**[.claude/agents/spipe/dev.md](../agents/spipe/dev.md)**

Codex routes SPipe development work through `$sp_dev`:

**[.codex/skills/sp_dev/SKILL.md](../../.codex/skills/sp_dev/SKILL.md)**

Check or install that wiring with:

```bash
sh scripts/setup/install-spipe-dev-command.shs --check
sh scripts/setup/install-spipe-dev-command.shs --apply
```

## Quick references in the same directory

- [`.claude/agents/spipe/research.md`](../agents/spipe/research.md) — SPipe research phase
- [`.claude/agents/spipe/spec.md`](../agents/spipe/spec.md) — SPipe spec phase
- [`.claude/agents/spipe/implement.md`](../agents/spipe/implement.md) — SPipe implementation phase
- [`.claude/agents/spipe/verify.md`](../agents/spipe/verify.md) — SPipe verification phase
- [`.claude/skills/lib/spipe_phases.md`](lib/spipe_phases.md) — phase map
- [`.claude/skills/lib/spipe_diagrams.md`](lib/spipe_diagrams.md) — diagram & concision rules (≤30 lines + ≥1 SDN diagram)
- [`.claude/skills/lib/spipe_ui.md`](lib/spipe_ui.md) — **UI skill**: the 3 main GUI check apps + framebuffer capture/verify & backend-parity gates
- [`doc/07_guide/infra/testing/sspec_scenario_manual.md`](../../doc/07_guide/infra/testing/sspec_scenario_manual.md) — scenario manual, capture, inline/previous scenario, and environmental-test guidance

## Scenario Manual Quality

SPipe specs are executable tests and generated manuals. For user-facing,
operator-facing, MCP/tooling, UI, protocol, hardware, system, and environmental
tests, generated `doc/06_spec/...` must read like a scenario manual:

- primary flows visible as ordered steps;
- `@inline` setup hidden as standalone content and expanded through `@prev` or
  `@include`;
- capture evidence attached under the step that caused it;
- advanced/edge/matrix/stress details folded or skipped by policy;
- executable SPipe folded below the manual.

Run `bin/simple spipe-docgen <spec> --output doc/06_spec` and revise the spec
until the generated manual is usable without opening the source.

## Startup-Sensitive Specs

If a SPipe change touches `simple run`, direct file argv parsing,
`get_cli_args`, `std.cli`, `.shs` dispatch, mmap/read-ahead startup loading,
launch metadata, or startup dynlib policy, keep this executable integration
spec in the evidence set:

```text
test/02_integration/app/startup_argparse_mmap_perf_spec.spl
doc/06_spec/02_integration/app/startup_argparse_mmap_perf_spec.md
```

Do not move executable startup specs into `doc/06_spec`, and do not route
script startup through compile/JIT as a workaround for a failing fast path. Fix
the fast path or record a concrete bug.

## Equality is not correctness (false-green guard)

A parity/equality assertion (`expect(a).to_equal(b)`, "backend A matches backend
B", "output == reference") passes whenever both sides are equal — **including
when both are empty, both are wrong in the same way, or both come from the same
code path.** Equality alone never proves the values are *right*.

When the two sides share the code you just changed, or one side can silently fall
back to mirroring the other, pair the equality check with an **absolute oracle**:

- a known fixed point with a known value (filled shape center == draw color; a
  far/background pixel == background; a counter == an independently computed total);
- proof the producer actually ran (e.g. a GPU `gpu_frame_complete`/hit-counter
  flag, not just "no error"), so a no-op fallback can't pass as success;
- two *independently produced* artifacts, never one value compared to itself.

This area of the codebase has a documented false-green history (software-vs-itself
"GPU parity", scalar paths reporting `has_neon` without running NEON, all-black
buffers matching all-black). See
`doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md` ("MATCH ≠ correct"). When the
test runner can't execute the `it` blocks (e.g. it segfaults importing a heavy
module graph), run the same assertions through a `bin/simple run …` harness and
keep the absolute oracle in it — don't downgrade to "files load".

## GUI sanity tests (pure-Simple lane)

After any GUI / engine2d / web-render change, sanity-check the **three main GUI
check apps** (one per surface; on macOS the lane = Engine2D CPU/NEON + Metal):

1. **2D rendering** — `examples/06_io/ui/engine2d_shapes_gui.spl` (primitives;
   backend variants `engine2d_cpu_simd_gui.spl` / `engine2d_metal_gui.spl`).
2. **GUI widgets** — `examples/06_io/ui/widget_showcase_gui.spl` (full widget catalog).
3. **HTML rendering** — `examples/06_io/ui/web_render_file_gui.spl <file.html>`
   (real HTML+CSS → web layout → Engine2D; headless PPM via `web_render_page_ppm.spl`).

Launch (macOS): `scripts/gui/macos-gui-run.shs <app.spl>`. **Verify the
framebuffer, not the screenshot** (`read_pixels()` → P6 PPM is the absolute
oracle; region screen-capture is flaky). Full launch/capture/parity-gate details:
**[`lib/spipe_ui.md`](lib/spipe_ui.md)** (the UI skill). Reference:
`doc/04_architecture/ui/simple_gui_stack.md` → "GUI Sanity Apps". The web-layout
lane is interpreter-bound (~1.5 ms/px) — keep web sanity surfaces ≤ ~900×760.

## Template

```
cp .claude/templates/spipe_template.spl test/my_spec.spl
```

## FILE.md Enforcement

SPipe verify runs `sh scripts/check-workspace-root-guard.shs audit --strict`.
Default: diagnose and report. Auto-fix: trace origin and fix creating code.
See [`doc/07_guide/infra/workspace/file_manifest_tldr.md`](../../doc/07_guide/infra/workspace/file_manifest_tldr.md).

## Code Quality Checks

SPipe verify and implementation phases enforce these quality gates:

- **Duplication**: no line-level, token-level, or semantic duplicates; parameter
  lists with 3+ fields become a struct
- **Cohesion**: each file covers one concern; split large files by feature, not
  by number suffix
- **Coupling**: minimize public interface per layer and per feature; prefer
  private helpers
- **Naming**: files use descriptive names, never numbered copies (`_1`, `_v2`)
- **Docs**: every new doc produces a `xxxx_tldr.md` (≤30 lines + diagram)

## Feature Module Packaging (`.sfm`)

When a feature ships a runnable module, package it as a **Simple Feature Module**
(`.sfm`): embed the compiled SMF as an opaque payload plus a feature manifest
(exposed front-end/back-end layers + `SfmSecurityLevel`; mark `Trusted` only when
privileged layers must be gated). Consume it via `std.sfm`: `sfm_load` parses the
container, `sfm_resolve` resolves a manifest layer (DI wires layers from the
manifest; an AOP authz aspect enforces the security level). See
[`doc/04_architecture/infra/sfm/simple_feature_module.md`](../../doc/04_architecture/infra/sfm/simple_feature_module.md)
and [`doc/05_design/infra/sfm/simple_feature_module.md`](../../doc/05_design/infra/sfm/simple_feature_module.md).

## Performance Checking & Cross-Language Comparison

To verify correctness across execution modes and benchmark against other languages:

- **Guide:** [`doc/07_guide/compiler/check_perf.md`](../../doc/07_guide/compiler/check_perf.md) — interpreter / SMF loader / native mode checks + cross-language perf matrix
- **Harness:** `sh scripts/check/check-cross-language-perf.shs` — measures size, cold startup, warm throughput (fib35), parallel spawn + binary sizes + peak RSS (baseline-subtracted per-worker delta) against bun, python, go, erlang, java, C. Use `RUN_TIMEOUT=<seconds>` for bounded smoke or slow-host runs; the harness removes failed Simple outputs so stale native/SMF artifacts are not measured.
- **GUI perf:** `sh scripts/check/check-gtk-gui-size-speed-baseline.shs` — frame time, binary size, cache hit rates, peak RSS (Simple vs GTK; GTK measured inside xvfb-run)
- **Startup audit:** `sh scripts/check/check-startup-size-performance-audit.shs` — cold startup, binary size, ELF sections, library deps, peak RSS
- **TL;DR:** [`doc/07_guide/compiler/check_perf_tldr.md`](../../doc/07_guide/compiler/check_perf_tldr.md)

Correctness quick-check across all modes:

```bash
for mode in interpreter smf native; do
    bin/simple test path/to/spec.spl --mode=$mode
done
```

Native-mode SPipe specs are not always a reliable oracle for runtime ABI work:
unresolved generated BDD calls (`rt_bdd_*` / `std.spec`) can no-op or segfault
before `it` bodies execute. For native runtime hooks, pair interpreter SPipe
coverage with a direct native entrypoint that uses hard `rt_exit` checks.

Optimization must stay **pure Simple** (`.spl`) — do not modify Rust seed or C runtime.
Mode escalation: interpreter (dev) → SMF (staging) → native (production).

## Run

```
bin/simple test path/to/my_spec.spl
```
