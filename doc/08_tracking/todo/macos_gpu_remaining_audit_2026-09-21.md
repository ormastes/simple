# Remaining macOS GPU TODO and bug audit

Date: 2026-09-21
Baseline: `origin/main` `20245f731db`
Host: aarch64-apple-darwin

| Rows / bug | Current disposition and evidence needed |
|---|---|
| TODO 18, ordered Metal font batches | Source repair and regressions added; open pending native execution. See `../bug/metal_font_ordered_flush_span_false_failure_2026-09-21.md`. |
| TODO 8 / 292, real Metal trace | Open. An actual GPU trace and tool-produced capture receipt are still required; a CPU or routing result cannot close this row. |
| TODO 9 / 293 and 173 / 316, available Metal probe | Open. The admitted portable core still defines `rt_metal_is_available()` as zero in `src/runtime/runtime_core_host_services.c`. A native provider, nonempty device name/identity and probe transcript remain missing. |
| TODO 10 / 294, Metal lifecycle phases | Open. No `addCompletedHandler`-backed lifecycle extern is available to the pure-Simple provider. |
| TODO 11 / 295, Metal fence token | Open. No `rt_metal_command_buffer_event` or shared-event token extern is available. |
| TODO 12 / 296, Metal device timestamps | Open. No `MTLCounterSampleBuffer` timestamp extern is available. |
| GPU loader Linux sonames on macOS | Open; the shared worktree contains another session's source/test changes for this defect. This lane preserves those edits. |
| GUI Aqua activation / window registration | Open; the shared worktree contains another session's report update. A live OS-input/window movement receipt is required. |
| Vulkan vector-font empty batch | Open. The existing report isolates invalid glyph bitmap material and native aggregate transport; no current positive-quad/readback receipt exists. |
| WM Metal glass multi-receipt opacity | Open. Source contracts already exist; admitted opaque-Metal device readback with ordered receipts is still absent. Sub-opaque material remains an explicit capability gap. |

The paired TODO IDs are existing scanner duplicates of the same source lines;
both remain visible and open. This audit does not relabel provider capability
or hardware evidence gaps as completed work. It adds explicit blockers to
those rows so their next action is visible without rereading historical notes.

Compiler/memory, bootstrap P0, runtime process/sosix and Endpoint Security
admission rows are assigned to the other parallel lanes. Their results are
integrated by the parent session; this audit does not duplicate their edits.

The Metal span fixture's native build hit the cold-inventory memory guard
before compilation (951,296 KiB, 10.66 seconds). Existing GPU SSpecs and real
device gates were not reported as passing from source inspection.
