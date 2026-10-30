# Independent smux window zoom source review

**Current result: v2 source review complete, WARN / NOT_RUN. No remaining scoped P0/P1/P2 findings identified.** The two v1 defects below are closed by the focused v2 corrections recorded at the end of this report. All 14 v2 file hashes matched; five changed and nine retained their reviewed v1 pins. Sixteen scenarios remain authored, zero executed. This is not native qualification, full tmux parity, production readiness or release admission.

## Historical cycle-1 review

Status: **WARN / NOT_RUN**. Source cycle 1 has **two blocking findings: P1 and P2**. No runtime or production-readiness PASS is granted. Review date: 2026-10-25. Worktree: `D:/dev/simple-coremux-shared-20261025`; declared base `7bc0826bf89d6f6b5a240468b1453435505f94a8`.

## Exact input and method

All 14 hashes in `build/review/smux-zoom-source-freeze-v1.sdn` matched the actual files before review. The 11 production paths plus spec, authored manual and author report are pinned below. The author subsequently began cycle 2; these pins and findings describe v1 only. Reported fixes are not accepted until their new freeze receives focused review. No common-contract files were changed or assessed as this lane's implementation.

Reviewed the production call chains, original snapshot/native effect ordering, lifecycle paths, protocol status classification, client recovery, actual Caret caller and each of the 16 authored scenario bodies. Context-mode file execution returned exit -1, so bounded PowerShell reads were used. No compiler, test, product, helper executable or native probe was launched. No production edit or commit was made. The verify skill's execution/docgen/coverage requirements remain blocked, not waived.

Primary reference: the separate `build/review/tmux-zoom-primary-semantics.md` records official tmux 3.5a and targeted master source. In particular, [resize-pane -Z](https://github.com/tmux/tmux/blob/3.5a/cmd-resize-pane.c) restores any already-zoomed ordinary window regardless of target, while [select-pane](https://github.com/tmux/tmux/blob/3.5a/cmd-select-pane.c) preserves zoom for no-op same-pane selection and otherwise unzooms unless explicitly requested to preserve it.

## Blocking findings

### P1 — Successful interactive zoom is classified as failure

`interactive_protocol.spl:171-175` emits `smux: zoom restored` or `smux: zoom <id>` after mutating service geometry. `interactive_client.spl:40-50` requires `smux_remote_reply_ok` for every request. That production predicate at `smux_remote.spl:417-432` accepts neither new success reply. Prefix-z therefore changes the owner window and then returns an error from `apply_action`, ending the attachment rather than rendering success. The v1 dispatcher test compares reply text without traversing the predicate, so it does not detect this integration failure.

Required correction: narrowly admit the exact restored status and a well-formed canonical pane-ID success envelope; keep failed, malformed and extra-field replies rejected. Assert the actual dispatcher reply through the actual production predicate for both toggle directions and rejection controls.

### P2 — Split rollback can restore zoom onto a nonfocused pane

`split_checkpoint.spl:83-86` restores the previous window, including its zoom target, while intentionally retaining current pane focus. Checkpoint validation does not detect a geometry-neutral focus change. Concrete sequence using production planners: zoom p1; split; focus p2; restore the split checkpoint. The window returns to zoom p1 but p2 retains focus. A subsequent focus-p2 operation at `window_layout_service.spl:364` returns immediately and leaves the focused pane hidden.

Required correction: before any native restore, reject incompatible focus drift when restoring a zoomed checkpoint, or establish an explicitly designed focus policy without silently overwriting unrelated current state. Retain unzoomed checkpoint focus independence where valid. Add the actual zoom/split/focus/rollback sequence as a regression and verify refusal leaves current state intact.
Root identified an adjacent case within this same inspected P2 owner: start unzoomed, split, focus the newly added pane, then rollback. The added pane is the sole focused pane, but restoration removes it while retaining every surviving false focus bit. There is then no focused survivor. Reject removal of an independently focused added pane before native effects; preserve current state and add this unzoomed regression. This is the same checkpoint-focus invariant defect, not a new review cycle or unrelated feature expansion.

Both findings were sent promptly to root and the production author. The author reported cycle-2 fixes in progress; those reports alone do not close these findings.

## Findings without a new source blocker

- Base, visible and child viewport projections are separate in `window_layout_service.spl:48-85`. Hidden panes retain underlying sizes and ownership. Window canvas changes preserve zoom and reproject the reference map; explicit named layout, valid pane resize and split clear zoom through the window geometry constructors. One-pane toggle is a no-op; different-target toggle restores; same-focus preserves; different-focus restores.
- Geometry plans validate scope, dimensions and overlap before effects. `resize_layout_children:182-218` preflights all indices, identities, dimensions and PTY resize capability. The failing attempted child is included in compensation as well as prior successful children. Metadata/VT publication follows successful native changes. Typed `uncertain` propagates to API-owned closing-window quarantine; every affected child handle remains available to checked deletion. No text matching decides this outcome.
- Nonfinal close first uses checked child teardown. A survivor-resize failure retains the released target record, pending close, base/zoom authority and surviving handles. Incomplete compensation quarantines the window. Final-pane requests delegate to checked window/session deletion before the ordinary closing-window guard, preserving final deletion retry. Poll/input/spawn/layout guards consult the same closing state; no second live registry was introduced.
- Split checkpoints now cover all child viewport rectangles and zoom identity, not only visible rectangles. Except for P2 above, checks reject changed geometry, reference map, pane identities, child tokens or a newly owned child before native restoration. Counters are not rewound.
- Caret `pane_backend.spl:366` calls the service toggle; listing reads service zoom identity. The former adapter-local display flag is removed. This establishes source connectivity, not rendered Caret behavior or successful selected library/profile compilation.
- The managed `client-request` whitelist includes zoom and retains exact lease/session checks before recursive dispatch. Raw commands remain under the existing shared server-token model; this does not establish per-human authorization. Hidden interactive input is rejected before decoding/enqueue, while explicit programmatic hidden-pane commands remain available.
- Hidden-cursor frames and hidden interactive input produce exact recoverable replies. Client recovery obtains scoped visible-pane metadata and validates a current frame before replacing local selection/copy state. The failed action and later actions in its current chunk are not replayed; decoder state resets after recovery. Transport errors are not interpreted as missing/hidden targets.

## Spec/manual quality and remaining gates

Sixteen cases are authored; **zero executed**. They exercise actual production geometry/lifecycle/frame/input/dispatch functions. Synthetic handle values are confined to pure ownership/capability guards and are explicitly not native failure evidence. The typed uncertainty construction is only a representation control; it does not exercise compensation or API quarantine.

The native case acquires two real ConPTY children, asks child PowerShell to compute inherited viewport dimensions, tests a command in the hidden pane, samples original PID existence, then requires checked session cleanup before assertions. Full expected markers do not occur in echoed commands. Native acquisition is followed by outcome collection rather than early assertions; cleanup covers both children even when either spawn fails. PID absence and provider cleanup count supplement but cannot replace an external process-tree quiescence receipt; PID reuse and provider binding remain explicit limits. The expected resized widths 48/50 match the stored manual reference projection.

This case proves neither unattended detached progress nor two real clients: active capture drives output, and no real hosted-client/Caret UI runs in it. Provider refusal, partial close, failed compensation, actual client recovery, external descendant cleanup and concurrency/interleaving need genuine runtime evidence. A copied-flag or fake backend test must not replace them. Authored manual accurately distinguishes pure controls, required native observations and these gaps, but its connected prefix-z behavior is blocked by P1. Native docgen, captures, maintenance scan, coverage and selected NoGC/provider compilation remain NOT_RUN.

The supplied source budgets are API 778 and layout owner 403 lines, with owned sources below 800; no repeated line-budget verification was run. A new freeze after fixes must retain that constraint. Source-level acceptance requires closing the two findings; release/major-parity readiness additionally requires admitted executable evidence.

## Frozen v1 SHA-256 inputs

| Path | SHA-256 |
|---|---|
| src/os/apps/smux/api.spl | `eb0683e66cd8933f8a982e56ebf0c8faa92db8c8a1e006d147c072583c022e8b` |
| src/os/apps/smux/contract.spl | `b12eaa35b30f48d38367c86b88f4c3386f815661d7507c8cd610adcc8e8d53ea` |
| src/os/apps/smux/window_layout_service.spl | `4758a954c25c401728c49c947970d36bc1d643050d0920c2d7a40d635444b4e2` |
| src/os/apps/smux/pane_lifecycle.spl | `8172253bc12e4030d7dbf21f4d29b78be0de99cb9fd496160bb767a3b3adb920` |
| src/os/apps/smux/split_checkpoint.spl | `e5f69d01feea7c84a87a01e2c1294f8d8dc74c0add6397152e42a772b6d9dca9` |
| src/os/apps/smux/frame_snapshot.spl | `f5f8bfad65a4a845e6ba9ebfa3b974672a6b1be63af6e478a0e1d0301c4e7ed4` |
| src/os/apps/smux/interactive_protocol.spl | `40fb39517bc16d0cd3ea40c3ceb3f2d9f33747d6cf19afa308d1c5b413aac57d` |
| src/os/apps/smux/interactive_client.spl | `843d81201f652c4c8495f9a1dac3f042e02fce8b84289fa7709ae213535c578a` |
| src/os/apps/smux/client_input.spl | `83c863aa0f26b2fcd007edb5da703979e4f96fc8a948e9d56c0e5a28a9ddb5f3` |
| src/os/apps/smux/smux_remote.spl | `90e4df9d65b3fb96cc4a35c770accb2ba8d446f833ebe90f74c171539ce93f0d` |
| src/app/llm_caret/pane_backend.spl | `86c389b1d8270191b9e9d1a767b566166009c9d47a950f4ca49983eae0d5c20c` |
| test/03_system/tools/smux_zoom_spec.spl | `f7d3348c68e8dd384e2e8c4d1355b710481182699d74a6fb740f736fbc98b775` |
| doc/06_spec/03_system/tools/smux_zoom_spec.md | `c7b7aa119123d04189f3e689eb349b7b841270dc5544a22b7f85618dbaf1e6a2` |
| doc/09_report/smux_window_zoom_source_2026_10_25.md | `5e17bab9e46574d9cf2543a818cc605a3244682bd63c65a2738573ca1a8a531b` |

## Cycle-2 focused correction review

Input: `build/review/smux-zoom-source-freeze-v2.sdn`. All 14 actual SHA-256 values were checked once against this freeze: five changed pins and nine identical to v1. Review was limited to the changed reply predicate, checkpoint guards, their expanded scenario assertions and matching manual/author notes. Unchanged broad production checks were not repeated. No compiler, helper, test, native process, product or runtime probe was launched.

**P1 closed in source.** `smux_remote.spl:415-422` recognizes the exact restored success or exactly three fields with the canonical `id` prefix and positive int64 decimal serial round-tripping to its original text. This matches the service `id_text` owner. The actual client predicate invokes this helper at line 431. Error prefixes, empty/zero/noncanonical IDs, extra fields and trailing newline variants remain rejected. Scenario 15 now passes real dispatcher zoom/restore replies through `smux_remote_reply_ok`, with actual unknown-target and malformed-envelope controls. No transport success is substituted for command success.

**P2 closed in source, including the adjacent case.** `split_checkpoint.spl:56-61` rejects restoring prior zoom if its target no longer has focus. Lines 75-79 reject removing an independently focused added pane before ownership/native effects. Both paths return the current snapshot unchanged. The native resize call follows at line 83. Scenario 9 retains the valid restore control and adds production zoom/split/refocus/refusal plus unzoomed split/focus-added/refusal sequences, asserting preserved unzoomed state, current focus and retained panes. Unzoomed rollback can still retain a valid independently selected surviving pane; the fix does not overwrite current focus.

The mirrored manual's rows 9 and 15 and appended correction notes describe these same source assertions. The author report retains the 16-authored/0-executed distinction. No remaining scoped P0/P1/P2 is identified. All runtime, provider-failure/compensation, real client/Caret, docgen/capture and process-tree qualification limits in the historical review remain open evidence gates.

### Frozen v2 SHA-256 inputs

| Path | SHA-256 |
|---|---|
| src/os/apps/smux/api.spl | `eb0683e66cd8933f8a982e56ebf0c8faa92db8c8a1e006d147c072583c022e8b` |
| src/os/apps/smux/contract.spl | `b12eaa35b30f48d38367c86b88f4c3386f815661d7507c8cd610adcc8e8d53ea` |
| src/os/apps/smux/window_layout_service.spl | `4758a954c25c401728c49c947970d36bc1d643050d0920c2d7a40d635444b4e2` |
| src/os/apps/smux/pane_lifecycle.spl | `8172253bc12e4030d7dbf21f4d29b78be0de99cb9fd496160bb767a3b3adb920` |
| src/os/apps/smux/split_checkpoint.spl | `965f634408d097846858e1b7ba899c515ea03d6781acd308be223bdfc3775425` |
| src/os/apps/smux/frame_snapshot.spl | `f5f8bfad65a4a845e6ba9ebfa3b974672a6b1be63af6e478a0e1d0301c4e7ed4` |
| src/os/apps/smux/interactive_protocol.spl | `40fb39517bc16d0cd3ea40c3ceb3f2d9f33747d6cf19afa308d1c5b413aac57d` |
| src/os/apps/smux/interactive_client.spl | `843d81201f652c4c8495f9a1dac3f042e02fce8b84289fa7709ae213535c578a` |
| src/os/apps/smux/client_input.spl | `83c863aa0f26b2fcd007edb5da703979e4f96fc8a948e9d56c0e5a28a9ddb5f3` |
| src/os/apps/smux/smux_remote.spl | `dc1e9298483c6f96ab5bb385240b886b5e15bed96065e80cc92aa4e75d18d6ae` |
| src/app/llm_caret/pane_backend.spl | `86c389b1d8270191b9e9d1a767b566166009c9d47a950f4ca49983eae0d5c20c` |
| test/03_system/tools/smux_zoom_spec.spl | `818dad318d5b966d6c77c3a7387d2fe135399ce90f88f7787853bb4233f230dc` |
| doc/06_spec/03_system/tools/smux_zoom_spec.md | `641d9c55465273778c460abfe646bb22d9b9a60f2ceceb84b4a664c243c43486` |
| doc/09_report/smux_window_zoom_source_2026_10_25.md | `372fc780af4cf8185035077ef7a3eb647a23407b9e3f9df3bde4b834972f2f3a` |
