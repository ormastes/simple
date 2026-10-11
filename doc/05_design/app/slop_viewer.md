# Slop viewer native integration design

Date: 2026-10-03. Status: design proposal; API inventory is source inspection,
not a claim of runtime verification. Baseline: the traceability SDN final report
in `doc/09_report/simple_traceability_sdn_slop_final_2026-10-03.md`, requirements
REQ-TRC-013, 015, 016, 020. Shared graph signatures require implementation-owner
agreement before source changes. This document adds no competing graph authority.

## Existing facilities and actual gaps

| Facility | Physical source and existing interface | Integration and gap |
|---|---|---|
| Widget tree | `src/lib/common/ui/widget.spl`: `UITree`, `UIState`, `UIEvent`; `widget_kind.spl`: Tree, Treenode, Scroll, Textarea, Inspector, Tabs | Build real native widgets; no Graph or CodeEditor widget exists in this enum. |
| Composition | `src/lib/common/ui/builder.spl`: `row`, `column`, `panel`, `text_widget`, `button`; `widget_store.spl`: `WidgetStore` | Stable widget IDs map to canonical graph IDs through an explicit table, not unescaped action strings. |
| Session | `src/lib/nogc_sync_mut/ui/session.spl`: `UISession.new`, `update_tree`, `open_surface`, `access_snapshot`, `access_recent_events` | One session owns selection, focus, surfaces and event history. Host integration still needs a real launch and event-loop smoke test. |
| Tree | `src/lib/editor/view/file_tree.spl`: `FileTreeState.visible_nodes`, `select_next`, `select_prev`, `toggle_expand` | Filesystem paths are not canonical trace identities. Current `toggle_expand` handles only the root; implement nested expansion in Slop projection state rather than claim this API satisfies it. |
| Docking | `src/lib/editor/view/split_tree.spl`: `split_tree_split`, `SplitTree`; `dock_zone.spl`: `DockLayout`, panels and active zones | Reuse split/dock concepts and adapters where layer rules permit; avoid importing the complete editor app. |
| Diagram projection | `src/lib/editor/services/sdn_graph.spl`: `SdnGraph`, `sdn_graph_parse`, `sdn_graph_to_canonical_sdn`, `sdn_graph_render_html` | Useful diagram precedent only. Its schema, parser and HTML output cannot replace typed TraceGraph validation or a native Slop surface. |
| Graph rendering | `src/lib/common/ui/render_surface_widget.spl`; shared DrawIR and layered panel widgets | Native deterministic layer placement plus actual typed edge rendering/hit targets is required. A list of columns alone does not satisfy the graph acceptance criterion. |
| Read-only source | `src/lib/editor/buffer/syntax_highlight.spl`, `common.ui` Scroll/Textarea/Text | Optional syntax presentation, lazy source from snapshot owner. No direct working-directory file read for historical nodes. |
| Accessibility | `common.ui` typed access snapshot and semantic command machinery | Reuse typed objects. `access_source.spl` has JSON serializers: do not call them for Simple-owned Slop persistence or protocol. Add SDN projection at Slop boundary. |
| Text/HTML reports | `src/app/depgraph/render_adapter.spl`, `src/app/ui.render/session.spl` | Reuse render contract for exports only; generated HTML is not proof of interactive native GUI operation. |

## Ownership and interfaces

Physical proposal: `src/app/slop/main.spl` dispatches `simple slop viewer`;
`model.spl` owns view state; `projection.spl` maps the shared graph to bounded
view records; `session.spl` reduces actions; `view.spl` builds the UITree;
`source.spl` delegates immutable content lookup to the trace snapshot owner.
Shared model, query, evidence eligibility and SDN codec stay in the canonical
traceability owner. No Slop parser may independently infer semantic relations.

Proposed typed handoff (names may align with the parent's final shared contract):

* `TraceQuery`: snapshot ID, selected canonical ID, direction, relation-kind
  filter, bounded limit, cursor, grouping dimension.
* `TraceQueryResult`: snapshot ID, nodes, typed edges, total matching count,
  next cursor, complete flag, diagnostics and graph generation.
* `SourceRequest`: snapshot ID, artifact ID, blob/content identity, validated
  repository-relative path and requested line range.
* `SourceSlice`: the same identities, actual line range, content, truncation
  flag and availability/error status. Missing blob is an error, never a fallback
  to current worktree content.
* `SlopState`: graph generation, selected canonical ID, focused widget ID,
  expanded alias IDs, grouping, bounded projection, active inspector tab and
  pinned run ID. Focus and selection are distinct.
* `SlopAction`: select, expand/collapse, change grouping, forward/reverse trace,
  inspect source, inspect evidence, next page and change snapshot.

SDN envelopes include schema version, request ID, snapshot ID and operation.
Responses echo these fields and include graph generation, completeness and
diagnostics. Source responses arriving after a snapshot/selection change are
discarded. A delta must name its exact base generation; mismatch requests a
fresh bounded projection. Unsupported schemas or operations fail explicitly.
The first native integration can call typed APIs in-process: no HTTP listener
is necessary. If a service is introduced later, loopback origin/session checks
are required and its payloads remain SDN.

## Semantics and performance

Tree aliases resolve to one canonical node. A shared implementation highlights
all related features. Unassigned/unresolved nodes remain navigable. Layer
placement is stable by phase, grouping and canonical identity. Draw only edges
present in the query result; adjacent visual columns imply no relation.
Initial graph limit is 200 nodes with explicit shown/total counts and paging.
Selection must query cached indexes rather than repeatedly scan source trees.
Source is fetched only for the visible inspector and bounded line window.

Evidence labels come from the shared evaluator: linked, not_run, pass, fail,
incomplete and stale remain distinguishable. Every observation exposes run,
snapshot, lane, eligibility and reason. Invalid live indexing preserves the last
valid view with a conspicuous stale-snapshot banner; it cannot repaint that
view as verified for the invalid candidate. Preferences are user-local SDN,
not tracked source or test evidence.

## Verification handoff

Use a fixture with two features sharing implementation, an acceptance pass,
an unexecuted unit test, rejected historical evidence and an unresolved node.
Assert canonical selection through both tree aliases; exact edge sets and
origins; all evidence states; explicit pagination; and pinned-source contents
after the worktree changes. Reject traversal, absolute paths, missing blobs,
stale responses and hostile metadata markup/action strings.

A real native host must launch, render and accept selection events. Assert the
resulting UITree/access snapshot and source/evidence changes, then capture GUI
output under `doc/06_spec/image/03_system/app/slop/feature/`. Neither a static
HTML screenshot nor a text-only unit test fulfills native GUI verification.
TUI captures belong under `build/test-artifacts/03_system/app/slop/feature/`.
Generated manuals must link actual captures and report unavailable providers
as incomplete, never pass. Keyboard checks cover Tab/Shift-Tab, tree arrows,
Home/End, Enter, Escape, focus preservation and a nonvisual relation list.
Record warm startup, bounded-query latency and peak RSS separately from cold
index creation; compare to the parent report's NFR targets before acceptance.

## Initial source implementation, not runtime admission

The native slice now exists under `src/app/slop/`: `projection.spl`, `view.spl`,
`session.spl`, `source.spl`, `evidence.spl`, `native_frame.spl`, `native_host.spl`
and `main.spl`. It consumes the frozen shared `TraceQueryResult` and
`TraceQualification` records. The session is a real `UISession`; bounded
query controls, canonical aliases, focus events, tree keys and pinned source
updates change the widget tree. Qualification labels and rejection reasons
come directly from the shared evaluator.

Native host discovery found `nogc_sync_mut.ui.gui_renderer.GuiRenderer` and
`gc_async_mut.gpu.engine2d.draw_ir_adv.engine2d_draw_ir_adv_composition` already
provide OS window, input, DrawIR execution and pixel presentation. Slop uses
these owners directly. `native_frame.spl` derives edge endpoints from actual
widget layout and adds typed labeled edges to the widget DrawIR composition.
There is no HTML intermediary. `run_slop_native` opens the native window and
routes pointer, keyboard, scroll and resize events; missing provider/display
or skipped render commands return an error. It does not print a fabricated
pass or silently substitute another renderer.

Focused specs are in `test/01_unit/app/slop/`. They are authored, not executed
in this lane: no source-matched runtime has been admitted. Central CLI and
snapshot loading are integration-owner work. Search, alternative grouping,
full Tab/Shift-Tab pane traversal, complete accessibility, resizable persisted
docks, snapshot comparisons, run-opening and visual/native captures remain
open beyond this slice. Source reads currently admit public artifacts only;
private reads require an explicit access-policy owner. These gaps prevent a
claim that REQ-TRC-015/020 or the entire report is complete.

### Source-only checkpoint after full-scope / release 1.0 selection

The user selected full report scope and release 1.0, and requested waiting for
runtime readiness before verification or landing. No viewer tests, native
launches, benchmarks or captures have run. All three new viewer specs carry
`# @tag:in-development`; their real assertions remain intact.

Source review reconciled the exact shared APIs and fixes these state issues:

* Query refusal (`TRACE-QUERY-INVALID`) retains the old view; graph diagnostic
  and incomplete-input pages remain navigable with their diagnostics visible.
* Display counts are nodes on this page versus total matches, not cumulative
  coverage. Final-page state and full input completeness remain independent.
  The query owner retains neighborhood anchors across pages.
* Page changes clear off-page canonical selections and reset focus through
  the actual `UISession.FocusEvent` path. Collapsing a focused child's parent
  restores parent focus. Tree labels expose focus and selection separately;
  no detached or unused focused-property write claims visual focus.
* Source requests have explicit pending state. Reselecting the same node or
  changing its query reloads source once; scrolling/redraw does not reread it.
  Failed reads clear previous source content. Missing providers and rejected
  events are visible, with source status separate from navigation status.

Before the next viewer verification attempt, the integration owner must supply
a source-matched self-hosted runtime, the sanctioned native window provider
and display, and the immutable graph/source loading path. Review native event
and raster API behavior on that runtime, then execute the tagged specs once,
capture actual native selection/source/evidence transitions, and measure the
startup/query/RSS targets. No tests should be marked admitted from source
inspection alone. Full release work still includes search/grouping, complete
keyboard/pane accessibility, private-artifact read policy, persisted dock
resizing, source-location selection, snapshot comparison/run opening and TUI
adaptation. Current keyboard support is bounded tree navigation; it is not a
claim of complete WAI tree or desktop accessibility behavior.

Performance remains an explicit source gap: `slop_native_pixels` currently
creates and shuts down `Engine2D` for each dirty frame. The next renderer
work item is a retained engine/context with deliberate resize and shutdown
ownership, followed by asynchronous/cancellable layout that rejects stale
results. This checkpoint does not claim the 150 ms interaction target.
Native edge attachment scans page nodes for each edge (O(E*N), N capped at
200), and reruns widget layout for geometry. Edge-volume culling, retained
layout and cancellation still need implementation and measured evidence.
The existing DrawIR APIs expose edge commands; actual backend edge rendering
and labels remain runtime acceptance checks, not source-review conclusions.
