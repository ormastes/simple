# Smux release/1.0.0 and Phase3 check

Source reviewed: `1e431722b40236eda5e80bd5f5bf06395b0d0d08`, fetched from `origin/release/1.0.0` on 2026-10-25. Worktree: `D:/dev/simple-smux-phase3-suite-20261025`; branch `work/smux-phase3-suite-20261025`. Other sessions' main-worktree compiler changes and unrelated image materialization differences are excluded.

## Compiler evidence

No verified Phase3 compiler was found in the bounded current-artifact review. Do not use a directory named stage3 as generation evidence.

- `C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/output/stage3/simple.exe`, SHA256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`: downstream inputs explicitly identify this as provisional Phase2, diagnostic-only. Retained Hello output is `disk-provider-successor-hello-ok`; that does not change its generation.
- `C:/dev/simple-phase3-phase4-13d-storage-20261025/phase3/output`: no candidate in the reviewed directory.
- `C:/dev/simple-fixed-phase3-storage-20261024/phase3/terminal.sdn`: FAILED_RESOURCE, exit88, parse185/1441, no native output.
- `C:/dev/simple-phase3-c635-storage-20261025/phase3/build.log`: 65 HIR failures plus missing bootstrap-entry HIR during MIR, link skipped.
- `C:/dev/simple-any-phase3-continuation-storage-20261025/terminal-seal.sdn`: FAILED-RSS88, candidate NOT_ISSUED, incomplete failure ledger.
- `C:/dev/simple-any-phase3-no-rss-diagnostic-storage-20261025`: candidate absent; timeout124 and quiescent termination.
- Installed active CLI SHA256 `6094dcae291aa984973ccd681f956e67a7a60543ab99f76a29313fbbfdee96d1`: no current Phase3 lineage established.

User constraint: rebuild Phase3 with Phase3 if necessary; do not rebuild Phase2. No compiler was launched or rebuilt in this review. A usable Phase3 executable, its producer/runtime receipts and successful actual Hello compilation/execution are prerequisites for the requested smux run. Full CLI or a matching standalone SSpec runner is additionally required for suite execution.

## Feature findings

Existing production and executable specs cover separate sessions/windows, directional API splits, named layouts, attachment state, independent server lifetime, real ConPTY, terminal input, history and multiple clients. Their presence does not prove runtime success. Current review found no matching executed PASS receipts for this producer/source tuple.

Confirmed baseline interactive split defect: the client requests a directional split, then arranges the window; protocol `current` and frame reflow replace manual geometry with tiled geometry. This loses the requested orientation and nested placement. Persistent manual rectangles, reference-canvas projection and a freshness-checked failed-split rollback correction are now authored with modern SSpec regressions and independent source review. Native compilation/execution remains pending.

Baseline source-review gaps included abandoned client capacity/size constraints and missing session lifecycle commands. Candidate fixes now add secure-incarnation interactive leases, heartbeat/sweep and per-request stale-token checks, session rename and checked partial-cleanup termination. These changes remain unexecuted. Legacy direct attachments are persistent/unmanaged; window deletion and automatic owner discovery are still absent from the reviewed remote command surface. Mouse handling, key tables, tmux configuration and control mode remain deferred. These prevent an all-major-tmux-features completion claim.

## Acceptance status

STATUS: NOT_QUALIFIED. Phase3 smux native build, binary help/error sanity, live detached owner, split/layout/window/Unicode/multi-client workflows, SSpec case execution, generated-manual validation and required core/MCP checks remain unexecuted for this source. No placeholder result, source-only case count or old Phase2 success substitutes for those gates. Preserve earlier failure receipts and the six-cycle per-feature limit across continuations.

## Subsequent user-selected scope

The user explicitly selected both targeted pane text/command delivery and visible notifications between attached clients. Delivery must preserve session/window/pane ownership and detached child lifetime. Notification acknowledgment must follow successful rendering; queue refusal and disconnect behavior must be observable, with no exactly-once or per-human identity claim under a shared owner token.

The user additionally requires every actual Caret tmux workflow to be supported by smux with equivalent behavior. Audit the real `src/app/llm_caret` pane backend, swarm executor, workspace and scripts, including command arguments, parsed replies, pane targeting, lifecycle, zoom, capture, hiding/showing and layout/resize semantics. Source models that merely append tmux command strings are not execution evidence. Existing in-process smux panes live only as long as the dashboard, so they do not by themselves satisfy independent background-owner behavior.

The user selected A (mandatory CoreMux plus optional TUI extensions) and N2 (baseline plus concurrent/stress/24-hour soak qualification). Final selected requirements: doc/02_requirements/feature/caret_mux_tui.md and doc/02_requirements/nfr/caret_mux_tui.md. Required Caret geometry, lifecycle, input/capture and presentation operations remain mandatory; optional extension discovery cannot hide a compatibility gap.
