# CoreMux smux presentation and geometry source review — 2026-10-25

STATUS: WARN / NOT_RUN. Independent first-cycle review of the exact13-path presentation freeze. No scoped P0/P1/P2 identified. This is source review only:17 pure state/render and2 native ConPTY scenarios are authored and0executed. No compiler, helper, native product, test runner or doc generator was launched; no production source edit or commit occurred.

## Exact inputs

Freeze: `build/review/coremux-presentation-source-v1.sdn`, SHA256 `e0f35e52e5dcee8cb12bf426be9b10e395bc99cf5869a1d98174c360badbbd52`. All13 listed file hashes independently matched actual source bytes. The following pins define this review, not the moving API/server integration tree:

| Path | SHA256 |
|---|---|
| src/os/apps/smux/contract.spl | 3533ecba9d4a030536d3b7bfc5e148605e70249d23bbc139a03e071fecb946d8 |
| src/os/apps/smux/pane_presentation.spl | 8771ba57f894d408e609ef8c4966e490853c60960bfa7285b96521313dde66a4 |
| src/os/apps/smux/pane_presentation_service.spl | a2daa3eecd1b23d722cfbd71d3f2ab4e6ae4cd830b9ac870a0aeb33d6aba8801 |
| src/os/apps/smux/sized_split.spl | 9ef975964c93738e48253e61c5a3f201307ea78c7c9f5ba4aa54413e5b14cb22 |
| src/os/apps/smux/window_layout_service.spl | e04a0d7e05475d672c56169f6664ea5f389f9babf0965de835e6c67f212c915a |
| src/os/apps/smux/frame_snapshot.spl | 6618505ab5d2a0da0d25e87481625d37762cad7644cf5e743233111c5040cb57 |
| src/os/apps/smux/pane_lifecycle.spl | 023d80d2efb2e2a6f8db705594bd8f5f93cd97bfbe0a8706df006674d5c8e1ad |
| src/os/apps/smux/split_checkpoint.spl | def04b444561e048e2596abdb66e003fb0f92c497cd4765de5127d248e5b6295 |
| test/03_system/tools/smux_presentation_spec.spl | 3a47d158c37ba56a1d69063be54b57679a18db66948ae57aecdf770e3c9b09d4 |
| test/03_system/tools/smux_presentation_native_spec.spl | fdef990e2f006a03cd4a8ae04f7df394ba7d976b0ef234b1c00a916faa7208c9 |
| doc/06_spec/03_system/tools/smux_presentation_spec.md | 13386384fa38b4ec8f2294a2f264139b6b9c01e3c444892f3ba644ec4986cb5e |
| doc/06_spec/03_system/tools/smux_presentation_native_spec.md | f103d988faa3e83f9bf2683c8246403174abae604aa18802a12b5018b7f1b048 |
| doc/09_report/coremux_smux_presentation_source_2026_10_25.md | 8b74943133a25e4177e212b341e6ed333fff57f6cf03d7b5af286f251a0e68c7 |

## Source conclusions

`contract.spl` adds presentation to the existing MuxWindow owner rather than introducing another service or child registry. Ordinary window constructors preserve it; with_geometry retains only entries whose live geometry IDs remain. The internal store replaces by ID, preserves order and refuses a ninth entry. Membership validation occurs before the service setter calls that store. This matches the service's eight-pane capacity; direct value constructors do not themselves grant authority.

Title setters preserve literal text and reject more than1024 UTF8 bytes, C0, DEL and C1 controls. Rendering clips title cells by the existing VT width model, retains combining marks with their base and does not split a two-cell glyph at the available boundary. The pure fixtures check literal combining/wide text, byte-boundary rejection and terminal escape/control injection.

Single and Double borders both reserve one cell per edge but render different actual glyphs. Top/Bottom status reserves another row inside the border. Content rectangles, child sizes and cursor placement use the decorated content origin; border/status cells do not become child viewport cells. Frame allocation/content projections preserve ordering. Background holes remain blank, and the existing bounded frame canvas/reply policy remains in force. Base and zoom content dimensions must stay positive, including the geometry to which zoom would later restore.

Sized split arithmetic applies Cells/Percent to the new child's content on the selected axis. It subtracts the independent separator and existing pane's decoration cost; the new pane starts undecorated. Percent is1..99 and uses integer floor, while Equal assigns the odd remainder to the new child to retain legacy behavior. Zero, oversized, nonfitting and duplicate-identity plans fail before publishing state. Explicit pane resize treats requested dimensions as content and adds decoration costs to the allocation. Rebalance retains the selected named layout; Manual deliberately selects even-horizontal, as documented. Hidden panes retain their allocations in layout edits.

The approved visibility policy is implemented in the frozen plans. Hide changes independent metadata and preserves handles, output/history and explicit-target ownership. It rejects the last independently visible pane, chooses a visible sibling when hiding focus, and clears zoom when hiding the zoom target. Show clears only independent hiding, preserving current focus and an unrelated zoom. Rendering combines explicit hiding with zoom occlusion; the snapshot flag must continue to represent explicit hiding only in the separate snapshot integration. Hidden panes cannot be targeted for focus/zoom/split through these plans. Explicit targeted sends are intentionally not revoked by a presentation change.

Presentation operations reuse checked geometry commits. They plan and validate first, compute affected surviving child dimensions against the original state, and resize native PTYs before publishing the new VT state. Compensation includes the failed attempted handle as well as earlier successful ones, because a failed call need not prove zero effect. Failed compensation returns the prior state with uncertainty so the API can quarantine it while retaining ownership. No new native boundary is introduced. Failure injection and actual quarantine publication remain unexecuted.

Closing a pane refuses deletion while owned handles remain. Removing the last visible pane reveals/focuses the first surviving background pane. The old-window geometry reconstruction filters out the removed pane's presentation, preventing entry resurrection even when ServiceState pruning occurred earlier. Final-pane teardown remains delegated to checked window/session lifecycle. Split checkpoint restore compares presentation entries before native compensation, preserving later title/border/status/visibility edits rather than restoring stale whole-window metadata; existing identity, child-handle, geometry and focus freshness checks remain.

## Authored controls and evidence limits

The17 state/render controls call production plans and projections. They assert default Equal compatibility, title persistence/control limits, actual border/title/cursor rendering, width clipping, invalid content refusal, modeled ownership preservation during hiding, focus and last-visible rules, Cells/Percent arithmetic, nonfitting requests, content resize, rebalance policy, last-visible close/prune and stale-style checkpoint refusal. The modeled123/456 handles are explicitly identified as pure retention controls, never native effect evidence. A distinct Show-while-another-pane-remains-zoomed case is not separately exercised by these authored controls, although the source path preserves zoom as required.

The2 native scenarios are intended to call actual API operations, spawn real cmd.exe ConPTY children, obtain independently generated PowerShell console dimensions, inspect frame glyphs/titles, continue explicit input/output while hidden, reject stale interactive input and complete checked cleanup before asserting observations. Expected dimension strings are absent from submitted commands, so command echo cannot satisfy the measurement oracle. PID observations use the approved arbitrary-PID Sosix presence seam; they still require the actual linked provider, process identity/PID-reuse interpretation and owner resource/Job cleanup evidence. Deferred PTY cleanup must be zero. Neither scenario has executed, and the Percent scenario does not prove forced native resize rollback.

Manuals are authored mirrors and say NOT_RUN; native doc generation, branch coverage, runtime timing/soak and provider qualification are not claimed. The primary source report likewise retains these limits. No unavailable-provider fallback or unconditional-success scenario was identified.

## Integration boundary and disposition

API/controller publication, CoreMux snapshot/command dispatch and ServiceState remove_pane pruning are separate owners and not admitted by these13 pins. The interactive route must reject both explicit-hidden and zoom-occluded stale targets while preserving intentional explicit-send authority. The current moving interactive_protocol file contains such checks, but that observation is not an exact-freeze integration review or execution evidence. The native spec references new API methods whose final connected implementation must be reviewed with the provider freeze.

No remaining scoped P0/P1/P2 identified in this first review. This does not establish a complete provider, successful old-server compatibility, full mandatory-operation admission, complete Caret/IDE/Tmux behavior, or N2 performance/soak. Final pipeline admission still requires connected-source review and actual qualified producer/runtime tests with exact source/artifact/cleanup receipts. STATUS remains WARN / NOT_RUN.
