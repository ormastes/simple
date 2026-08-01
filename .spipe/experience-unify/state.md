# Feature: experience-unify

## Raw Request
spipe dev skill, make small tasks and evaluate each task and assign proper model and review by higher model. unify experience libs 2d 3d sound and physics.

## Task Type
feature

## Refined Goal
Land the first concrete unification wave for the experience libraries — 2D, 3D, sound, physics — by adding the four shared seams from `doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md` (3D-output-as-CompositeLayer, camera render_order, audio bus graph, shared fixed-timestep) plus default-tier reachability, each as a small independently-tested module.

## Acceptance Criteria
- AC-1: A `surface_layer` module adapts a renderer3d frame target into a compositor `CompositeLayer`, and a unit spec proves z-order compositing of one 3D layer with 2D layers via `LayerTree` (interpreter mode green).
- AC-2: `camera` and `camera3d` components carry `render_order` (default 0) and a pure ordering helper sorts mixed camera sets deterministically; unit spec green.
- AC-3: An `engine/audio/bus.spl` bus graph (named buses, dB volume, mute, send target) computes effective gain along bus paths with absolute-oracle assertions (computed expected values, not self-comparison); unit spec green.
- AC-4: An `engine/core/fixed_timestep.spl` accumulator (fixed dt, max substeps, interpolation alpha) is shared-usable by both game loops; unit spec green with exact step-count/alpha oracles.
- AC-5: Engine surfaces (audio, physics, render, core, component) are reachable from the default tier `nogc_async_mut` via `export use` wrappers; `bin/simple check` passes on the wrappers, `deps fast` shows no new cycles.
- AC-6: A physics 2D/3D shared-core audit doc lists the concrete dimension-generic refactor seams (no code change).
- AC-7: All new specs pass in interpreter mode; no skip(), no bare expect(), no equality-of-self oracles.

## Scope Exclusions
- No render-graph/MDI work (plan P5), no Steam Audio SFFI, no netcode.
- No edits to compositor internals, renderer3d internals, or the Rust seed.
- Physics code refactor itself is audit-only this wave (AC-6).

## Task Breakdown, Evaluation, Model Assignment

Rubric: difficulty = language-quirk exposure x cross-module risk x design judgment.
Implement model by difficulty (low=haiku, medium=sonnet, high=opus); review model = next tier up; final gate = Fable (main loop).

| ID | Task | Files (disjoint scopes) | Difficulty | Impl model | Review model |
|----|------|------------------------|-----------|-----------|--------------|
| T1 | Default-tier export-use wrappers for engine surfaces | `src/lib/nogc_async_mut/engine*` (new wrappers only) | Medium (E0410 strictness) | sonnet | opus |
| T2 | renderer3d -> CompositeLayer surface bridge + spec | `engine/render/surface_layer.spl` (new), `test/01_unit/lib/engine/surface_layer_spec.spl` (new) | High (cross-module design) | opus | fable |
| T3 | Camera `render_order` + ordering helper + spec | `engine/component/camera.spl`, `camera3d.spl`, `camera_order.spl` (new), spec (new) | Low (field + sort) | haiku | opus |
| T4 | Audio bus graph module + spec | `engine/audio/bus.spl` (new), spec (new) | Medium | sonnet | opus |
| T5 | Shared fixed-timestep accumulator + spec | `engine/core/fixed_timestep.spl` (new), spec (new) | Medium | sonnet | opus |
| T6 | Physics 2D/3D shared-core audit (read-only) | `.spipe/experience-unify/physics_unify_audit.md` (new) | Medium (analysis) | sonnet | fable |

## Phase
verify-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature); 6 tasks evaluated and model-assigned (haiku x1, sonnet x3+audit, opus x1; reviews opus x4, fable x2).
- implement: T1 sonnet (2 wrappers + 2 __init__), T2 opus (surface_layer + spec), T3 haiku (render_order + camera_order, 4/0), T4 sonnet (bus graph, 30/0), T5 sonnet (fixed_timestep, 11/0), T6 sonnet (physics_unify_audit.md, S1-S10 seams).
- review (opus): T1 FIXED — default-tier bus wrapper was missing (AC-5 gap), added nogc_async_mut bus.spl + __init__ line. T3 APPROVED. T4 FIXED — _exp_approx Taylor tail error (0.0845 vs 0.1 at -20 dB); replaced with range-reduced e^x=(e^(x/4))^4, <0.001% over ±20 dB. T5 APPROVED.
- review (fable): T2 List-nil diagnosis independently confirmed (probe: List<i64>() nil receiver, even with SIMPLE_LIB=src); spec restructured to pure interpreter-green assertions 7/0; bug recorded doc/08_tracking/bug/interpreter_list_generic_nil_2026-06-12.md. T6 audit accepted (S6 contact-cache convergence flagged highest-value). Cross-lane guard: concurrent sound-engine lane's untracked sound_engine.spl excluded; its export lines stripped from committed __init__ blobs; T1's premature sound_engine wrapper held back with it.
- verify: camera_order 4/0, audio_bus 30/0, fixed_timestep 11/0, surface_layer 7/0 — all interpreter mode with seed driver.
