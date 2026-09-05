# T20 — U4 cutover sweep (investigation-only)

Per `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md` T20:
"the flag-guarded cutover at one dispatch site + the sweep confirming nothing
else needs migrating." Acceptance requires an enumerated sweep list, not
prose.

## Finding: no migratable dispatch site exists yet

T20's premise is that a real production dispatch site currently runs the
"old" scene path and needs a flag to alternately route through the "new"
arena-V2 / `SceneDeltaRef` / packed-producer pipeline. That premise does not
hold: the new pipeline has zero callers anywhere under `src/app/**`
(production code) — it is self-contained scaffolding (module + its own spec
+ the sibling module that builds it), the same pattern already recorded for
T15 (`HirForwardDecl` referenced by zero passes) and T16 (blend-span C symbol
never linked) elsewhere in this campaign.

## Sweep (enumerated)

| Candidate dispatch site | Checked how | Result |
|---|---|---|
| `showcase_core.spl:286-318` (`showcase_scene` + `showcase_run` calling `host.present_scene(scene)`) | Read source | **This is the one production dispatch site.** All four `ScreenHost` impls (`host_2d`, `host_gui`, `host_wm`, `host_web`) go through it. Docstring at :287-288: "Widget tree -> DrawIR v2 composition -> DrawIrV3 scene VALUE. This is the single production path; no host sees a writer." Confirmed by reading `draw_ir_v2_to_v3.spl`'s imports (:40,:53) — no `arena_v2`/`column_arena`/`SceneDelta` reference anywhere in that file. |
| `UiSceneColumnArenaV2` (`src/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2.spl`) | `grep -rn "UiSceneColumnArenaV2" src/ --include=*.spl` | Referenced only by its own module, `draw_ir_v3_direct_writer_v2.spl` (writer helpers), and `ui_scene_ports_v3.spl` (T5's `ui_scene_v3_build_delta`). Zero callers under `src/app/**`. |
| `SceneDeltaRef` / `ui_scene_v3_build_delta` (T5, `ui_scene_delta_v2.spl` + `ui_scene_ports_v3.spl`) | Same grep, plus targeted grep for `ui_scene_v3_build_delta` | Zero callers outside its own spec. T5's commit message scopes it as "give `SceneDeltaRef` a home" — a type + cursor, not a wired consumer. |
| `ui_gui_packed_producer.spl`, `wm_packed_producer.spl`, `ui_web_packed_producer.spl` | `grep -rln` for each symbol under `src/`, then `grep -rn` restricted to `src/app/ui_showcase/` | Zero callers under `src/app/ui_showcase/`. `host_web.spl:16-18` explicitly documents *declining* to call `ui_web_packed_producer` ("that producer goes html -> DrawIrV3Scene; this host already HAS the scene and needs the opposite direction, so calling it would be decoration"). |
| `draw_ir_v3_direct_writer_v2.spl` (`ui_scene_v2_write_row/update_word/commit`) | `grep -rn` for the three fn names under `src/` | Callers are its own spec only. |
| `draw_ir_v3_execution_route.spl` (GPU/CPU route selector, 531L) | Read header + `grep -rn "draw_ir_v3_route" src/app` | This is the offload cost-policy selector (cpu_reference/hybrid_vector_gpu/resident_gpu), a different axis from the arena-V2 cutover — no showcase host calls into it either. Out of scope for T20 (it is its own already-scoped wave-1 CPU-reference lane, not a pending cutover). |

## Conclusion

There is no bounded "flip a flag at one call site" edit available: the
candidate new path (`UiSceneColumnArenaV2` → `SceneDeltaRef` →
packed-producer) has never produced a `DrawIrV3Scene` equivalent to what
`showcase_scene()` emits, so a flag-guarded cutover would route real hosts to
a pipeline with no proven output — not a cutover, a regression. Building that
missing producer (widget tree → arena-V2 columns → `SceneDeltaRef` → full
`DrawIrV3Scene`) is new feature work spanning several modules, not the
scoped-as-one-site T20 unit.

**T20 disposition: investigation-only.** No spec, no sabotage — matches the
plan's own rule ("Investigation-only units ... need no spec/sabotage — say so
explicitly"). U4's status in the plan is corrected from NOT STARTED /
executable-now to **BLOCKED (no producer)**: the missing piece is a
widget-tree → arena-V2 → `SceneDeltaRef` → `DrawIrV3Scene` producer, which
does not exist in any lane's output reviewed for this campaign (F3/T5
delivered the type only, per its own commit message).

Binary/tooling used: `grep`/`Read` only — no build or test run needed for a
pure non-existence sweep.
