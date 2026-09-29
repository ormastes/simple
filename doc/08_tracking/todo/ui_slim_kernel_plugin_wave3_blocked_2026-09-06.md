# Slim UI kernel/plugin — Wave 3 rows blocked or deferred (2026-09-06)

Lane: `.spipe/ui_slim_kernel_plugin/state.md` · plan: `doc/03_plan/ui/slim_kernel_plugin/plan.md`
· PR #382 (`ui-slim-wave1`). Every row below keeps its acceptance id open; none is
counted as PASS. Resume commands run only existing binaries; rows marked BOOTSTRAP
cannot start while the 2026-09-06 no-bootstrap rule stands.

| # | row | acceptance | blocker / prerequisite | resume command | artifacts | owner |
|---|---|---|---|---|---|---|
| 1 | Certified before/after startup (H0/T0/T1) on a deployed pure-Simple `ui` | REQ-UI-SLIM-008, NFR-UI-SLIM-001 | **BOOTSTRAP**: no pure-Simple full CLI deployed on macOS; seed numbers are `diagnostic` | `sh scripts/check/check-ui-slim-startup.shs --binary bin/release/<triple>/simple --lane T1 --samples 100 --warmup 20` | `build/ui_slim/startup/*.sdn` | ui_slim lane |
| 2 | Certified G1/G0 window timing | REQ-UI-SLIM-005, REQ-UI-SLIM-012 | same binary; plus launcher defects `doc/08_tracking/bug/macos_gui_run_sigpipe_141_and_stale_winit_marker_gate_2026-09-06.md` | `sh scripts/check/check-ui-slim-gui-present.shs` | PPM + milestone SDN | ui_slim lane |
| 3 | Simple-vs-C comparison table (§8.7 template) | REQ-UI-SLIM-008 | rows 1 and 2; C fixtures already measured (termbox2 26.9 ms, ncursesw 27.1 ms, diagnostic) | rerun `test/05_perf/ui_slim/ref/*/run*.shs` on an idle runner, then fill `doc/09_report/ui/` | receipts under `build/ui_slim/ref/` | ui_slim lane |
| 4 | FLTK visible-window reference | design §4 | FLTK not installed (`brew list fltk` absent); no substitute | install FLTK, then `sh test/05_perf/ui_slim/ref/fltk/run.shs` | receipt | A09 |
| 5 | T2 richer TUI workload (focus/nav/resize/Unicode corpus) | design §8.1 | not written | extend `t1_greeting.ui.sdn` + C fixtures | — | A08 |
| 6 | Gate or remove diagnostic counters (`screen_row_copy_count`, `tiny_*_count`, layout steps, event_wait wakes) | log-retention convention | after row 1 certification | grep the counters, gate behind a debug flag | — | ui_slim lane |
| 7 | tty-inheriting spawn facade so spawned backends can be interactive | runtime boundary | `rt_process_spawn_async` nulls stdin (`env_process.rs:800`); runtime-owned change, seed rebuild = BOOTSTRAP | add `process_spawn_inherit` extern + facade, then revert tui to spawn if desired | — | runtime owner |
| 8 | `_host_backend_selector` undefined in `os.compositor.host_compositor_entry` | shared-WM product | `doc/08_tracking/bug/host_compositor_entry_calls_undefined_host_backend_selector_2026-09-06.md` | define it, `shared_wm_entrypoints_spec` 8/8 | — | compositor owner |
| 9 | Promote `push-ui-slim-closure*` rows from advisory to blocking | NFR-UI-SLIM-002 | needs the seed on every push host and the deps resolver fix merged | flip `push_blocking` in `config/check/must_check_gates.sdn` | — | ui_slim lane |
| 10 | Interpreter defects found on the way | — | `spec_runner_array_element_binding_mutates_copy_2026-09-06.md`; `state` rebinds to bool after `expect(state.<me-method>())` (seed) | interpreter owner | — | interpreter owner |

`bin/simple todo-scan` cannot run on this host (bootstrap shim), so the matching
`todo_db.sdn` rows were appended by hand with `file` pointing at this record; the
next scan may renumber them.
