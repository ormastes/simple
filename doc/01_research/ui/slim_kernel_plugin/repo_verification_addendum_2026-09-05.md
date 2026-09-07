# Slim TUI/GUI kernel–plugin — repo verification addendum

**Date:** 2026-09-05 · **Verified at:** HEAD `56dd3059c2e` (external docs were written against `e0432cd7be2`)
**Companion (imported from Downloads, unchanged):**
`simple_slim_tui_gui_kernel_plugin_design_parallel_plan_2026-09-05.md`,
`simple_slim_ui_parallel_agent_briefs_2026-09-05.md`,
`simple_lint_kernel_plugin_mdsocpp_research_design_parallel_plan_2026-09-03.md` (prior kernel/plugin try, P01).

This addendum records what the repo actually contains today, so the design and plan
rest on verified facts rather than the external doc's source observations.

## 1. Source observations — all CONFIRMED at HEAD

| Ref | File | Verified evidence |
|---|---|---|
| R02 | `src/lib/nogc_sync_mut/tiny/common/static_registry.spl` | linear duplicate scans `:27-36`; linear `query_module`/`query_class` `:40-58` |
| R03 | `src/app/ui.tui/screen.spl` | `draw_hline` loops `put_text` per cell `:325-334`; `_screen_replace_row` copies every row for a one-row change `:181-192`; `Screen` is a value (COW), `put_text` returns a new `Screen` `:289` |
| R04 | `src/app/ui.tui/async_app.spl` | `try_recv` then `thread_sleep(16)` `:151-163`; watcher polls content every 500 ms `:79-86`; `new` parses then re-reads the file `:112,120`; imports `os.compositor.host_compositor_entry` `:29` |
| R05 | `src/lib/nogc_sync_mut/tiny/gui/state.spl` | `add` validates parent + `push` `:33-37`; `resolved_panes` linear parent scan `:82-86`, sibling scans `:94-108`; `direct_child_extent_y` scans all nodes `:55-62` |
| R06 | `src/lib/nogc_sync_mut/tiny/tui/{render,cell}.spl` | fresh `TinyCellBuffer.create` per render `render.spl:33`; panes recomputed `:35`; `value.chars()` per text `:14` |
| R07 | `src/lib/nogc_sync_mut/tiny/engine2d/software.spl` | `fill_clipped` → `store_pixel` per pixel with format check inside `:99-115`; `surface_receipt` ships `pixels` + full checksum `:56,82-97`; `pixels: [i32]` for both formats `:15` |
| R08 | `src/lib/gui/pure_core.spl` | caller-supplied `elapsed_us` `:72`; `gui_dynlib_hot_probe_tick` `:123` counts event kinds `:94-105` |

Call sites of `.put_text(`/`.draw_hline(`: ~35 real (`src/app/ui.render/_TuiWidgets/core_widgets.spl`,
`src/app/llm_dashboard/tui/*`, `screen.spl`). Existing specs: screen 7 files, async_app 1,
tiny state 4, tiny render 1, software 2 (`test/01_unit/app/ui/`, `test/01_unit/lib/tiny/`).

## 2. Entry points (the external doc left these as "to be established")

| Product | Real owner | Note |
|---|---|---|
| CLI `ui` command | `src/app/cli/command_registry.spl:68` → `src/app/ui/main.spl` (`"tui"` → `run_tui`, `"gui"/"desktop"` → `detect_gui_backend` + `run_detected_backend`) and `src/app/ui/cli_entry.spl` | not in `dispatch/table.spl` |
| Normal TUI | `app.ui.tui.app.run_tui`; live-reload app `src/app/ui.tui/async_app.spl` | |
| Native GUI window | `src/app/ui_showcase/hosts/host_gui.spl` (GuiRenderer, SDL2/winit) | no Metal-specific host file |
| Tiny TUI | `tiny_tui_render` has NO app-level entry; lib + tests only | Tiny lane still open (see §4) |
| `examples/06_io/ui/hello_gui.spl` | a **TUI** app on `app.ui.tui.screen.Screen` | keep as T1 workload, never as G1 |

## 3. Import closure — seed lane, diagnostic only (`src/compiler_rust/target/bootstrap/simple deps fast`, 2026-09-05)

| Entry | Files in closure | Top directories |
|---|---:|---|
| `src/app/ui.tui/async_app.spl` | 344 | `lib/gc_async_mut` 137, `lib/nogc_sync_mut` 72, `lib/common` 44, **`os/compositor` 21, `os/drivers` 20, `lib/skia` 20, `os/kernel` 10** |
| `src/app/ui/main.spl` | 79 | `lib/nogc_sync_mut` 43, `app/io` 11 |
| `src/app/ui_showcase/hosts/host_gui.spl` | 4 | resolver stops at `gui_renderer` — UNKNOWN true closure |

The TUI live-reload app reaches skia OpenType parsing, virtio GPU drivers, and kernel
modules through `host_compositor_entry` (P08). That is the import-side proof for
UI-SLIM-004; link/map evidence is still required.

## 4. Kernel/plugin architecture — what is landed vs vapor

- **Landed:** `src/lib/nogc_sync_mut/composition/` (provider_contract, cli_registry,
  cli_provider_wire, sci_generator/reader, provider_generation, source, types, abi_digest,
  codec …) — 28 importing files (`src/app/simple_core`, `src/app/provider_cli`, `src/os/smf`,
  `src/os/services/launcher`, `src/compiler/80.driver/driver_provider_contract_v1.spl`),
  35 spec files (`test/01_unit/lib/composition/`, `test/03_system/app/simple/feature/sci_provider_query_abi_digest_spec.spl`).
- **Absent:** `src/lib/nogc_async_mut/kernel_plugin` (0 hits). The lint migration plan
  `doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md` is PROPOSED; its Phase 0
  deliverables (`check-kernel-closure.shs`, `kernel_closure.sdn`) do not exist.
- **Zero** `composition` imports under `src/lib/nogc_sync_mut/tiny/` or `src/app/ui.tui/` — the A02 adapter is genuinely new.
- Known contract gaps to inherit, not re-discover: `abi_interface_digest` is compute-and-log only
  (`module_identity.spl:9-31`); SMF manifest never rejects on mismatch (`smf_manifest.spl:220-233`);
  unregistered extern returns nil (`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`).
- The Tiny lane `.spipe/tiny_ui_web_wm/state.md` is OPEN: the 2026-08-16 highest-capability review
  returned FAIL (B-10..B-14 unlanded), and every executable gate is blocked on an admitted
  pure-Simple runtime. It owns `tiny/gui/state.spl`, `tiny/tui/*`, `tiny/engine2d/software.spl`.

## 5. Prior tries and numbers (do not repeat)

| Try | Outcome | Source |
|---|---|---|
| core-C-bootstrap TUI lane (2026-05-29) | Simple standalone TUI 14,336 B / 5.295 ms vs C termios 14,472 B / 4.474 ms — TUI primitive already near C; gap is closure, not the renderer | `doc/09_report/startup_size_performance_audit_2026-05-27.md` |
| dynSMF default-on caching for ui/gui/web/2d | **NO-GO**: `smf_dlopen` executes no real code; premise falsified 430×; negative ROI; reopen gates = execution-wiring proof + ≥0.30 s AND ≥10 % measured win | `doc/01_research/ui/perf/smf_default_ui_caching_research.md`, `doc/03_plan/ui/perf/smf_default_ui_caching_plan.md` |
| SIMD-first render optimisation | rejected: CPU-SIMD 1282 ms vs scalar 909 ms + colour corruption; order is packed memory → retained scene → zero-copy → scalar → SIMD → GPU | `doc/01_research/ui/perf/render_perf_diagnosis_2026-08-06.md` |
| Persistent Engine2D session | LANDED (`a7b57550`), 176–684× — reuse, do not rebuild | same |
| 800-module import cap | root-caused; limit raised to 4000 in seed, NOT redeployed; workaround `SIMPLE_MODULE_LIMIT=4000` or `--no-session-daemon` | `doc/08_tracking/bug/module_count_limit_800_intermittent_simple_test_2026-08-08.md` |
| MCP startup ladder | measure → cache probe → exec compiled → lazy registry → interfaces only → split import graph → background compile → keep-warm | `doc/07_guide/app/mcp/startup_performance.md` |
| String concat | O(n²) `rt_string_concat` — relevant to `put_text` prefix/suffix rebuild | `doc/08_tracking/bug/rt_string_concat_quadratic_2026-06-12.md` |

Harness limits: `check-startup-size-performance-audit.shs` and
`check-gtk-gui-size-speed-baseline.shs` are Linux-only (`ldd`, `/proc`, xvfb);
`check-cross-language-perf.shs` partially portable. macOS rows need `otool -L`,
`/usr/bin/time -l`, `vmmap`, or are `unsupported`.

## 6. Host status for a baseline

`bin/simple` on this mac is a 244-byte bootstrap shim (no `ui`, `run`, `test`, `deps`).
By the design's own rule (UI-SLIM-008, §11 Phase 0) a bootstrap-only binary is
`BLOCKED`, not a baseline. The fresh Sep-5 seed can run `deps` and specs for
diagnostics; certified before/after numbers need a deployed pure-Simple `ui` command.

<!-- sdn-diagram:id=ui_slim_kernel_plugin.research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_slim_kernel_plugin.research hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_main -> tui_app
tui_app -> screen
async_app -> screen
async_app -> host_compositor_entry
host_compositor_entry -> os_drivers
host_compositor_entry -> skia
host_compositor_entry -> os_kernel
host_gui -> gui_renderer
composition -x tiny
composition -x ui_tui
tiny_lane_open -> tiny_state
tiny_lane_open -> tiny_tui
tiny_lane_open -> tiny_software
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_slim_kernel_plugin.research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
