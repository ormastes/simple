# Checked smux pane lifecycle independent source review — 2026-10-25

STATUS: WARN / NOT_RUN. Cycle 3 source rereview closes both P2 findings. No remaining P0/P1/P2 identified in the reviewed source scope; runtime qualification remains pending. No production-code P0/P1/P2 identified in the six-file frozen repair. This is not native qualification or a release PASS.

Baseline: `bee3e7b9f79228b0d310614b9cef22a62bb81651` in `D:/dev/simple-smux-system-execution-20261025`. The reviewer did not author this repair. All six freeze SHA256 pins matched current bytes at review. No compiler, executable, tests or build was launched. Unrelated materialization/session changes are excluded.

## Historical first-review findings

1. **P2 — existing production specifications retain the superseded last-pane lifetime.** `test/03_system/tools/smux_service_layouts_spec.spl:274` closes the last pane, then unwraps the removed window's layout and expects `manual`. The new required behavior deletes the window/session; that lookup must fail. `test/03_system/tools/smux_protocol_features_spec.spl:136` and `:220` likewise expect `no focused pane` after final-pane deletion, although session target resolution now reports an unknown session. Update these scenarios and their manuals to assert intended owner removal and truthful refusal. Preserve any separate empty-window layout validation as a pure state control rather than recreating a deleted public owner. Root accepted this finding and assigned correction.

2. **P2 — positive native close cases lack independent target-death evidence.** `test/03_system/tools/smux_pane_lifecycle_spec.spl:80` records pane removal and surviving child output, but never probes the closed child's PID independently. The old unconditional-removal path could satisfy the piped scenario even if its child stayed alive; the global PTY pending count says nothing about that pipe child. Capture target-dead/survivor-live from the existing process facade before session cleanup, then both-dead after cleanup. Keep native false/deferred-close scenarios separately NOT_RUN; this improvement is not fault-injection evidence. Sent to author/root during the same correction cycle.

## Source trace and contract review

- `close_owned_children` adds an optional pane selector while retaining legacy session/window defaults. A false native close leaves the exact PID/PTY fields; success clears them. No synthetic provider result or new raw host boundary was introduced.
- `close_pane_state` validates the complete identity before effects, refuses a competing close in the same pending window, permits the exact retry, and delegates native release to that shared checked owner. `remove_closed_pane_state` refuses any retained process or PTY authority and refuses a final-pane removal at this lower layer.
- Failed close retains state and pending intent. `smux_window_closing` projects pane-close intent into the existing write/spawn/capture/resize/layout/focus/rollback gates. Polling projects the same window into `_drain_bounded`'s closing guard, preventing both output reads and queued-input flush. Other windows retain their routes.
- Final-pane API delegation precedes generic closing refusal: a repeated close can continue checked window/session deletion after its closing marker has been installed. Window/session kill installs its own marker before forgetting pane-level intent and retains the same native handles on partial failure; no authority is discarded by supersession.
- Successful non-final removal preserves survivor rectangles, output and ID counters, selects a surviving focus only when needed, and invalidates only that window's split checkpoint. Final window/session cleanup reuses established attachment/lease/notification handling. Public signature remains boolean; callers must treat false as incomplete cleanup.
- Caret dashboard's deliberate last-slot preservation still uses its separate `smux_pane_close_pty` path, so it does not silently acquire the new final-owner deletion policy. Workbench teardown already handles a false close and independently checks process existence. The stale production test expectations above must be repaired before integration.

## Evidence limits

All eleven authored cases were inspected. Pure fake-handle records exercise only ownership guards, not native failure behavior. Pending-intent cases cover exact versus competing requests; public cases cover focus/checkpoint isolation and final-owner deletion. The two real Windows cases contain actual pipe/ConPTY launch and computed output checks, bounded polling, and checked cleanup before ordinary assertions; their missing independent target-death oracle is finding 2.

Eleven authored, zero executed, zero passed. Real false/deferred-close, final-pane retry after a native refusal, escalation to window/session kill, and crash-safe external cleanup observations remain NOT_RUN. Source reasoning cannot establish native handle/provider behavior, child absence or measured coverage. The previous source-readiness receipt remains stale after this repair until the root commits and repins it.

## Historical first-freeze pins

The following immutable input record identifies exactly the reviewed first candidate. Later correction pins must supersede changed entries explicitly.

```sdn
schema: smux-pane-close-source-freeze-v1
baseline: "bee3e7b9f79228b0d310614b9cef22a62bb81651"
status: SOURCE_FROZEN_WARN_NOT_RUN
source_fix_cycle: 1
cases_authored: 11
cases_executed: 0
whitespace_check: PASS
native_false_close_evidence: NOT_RUN
readiness: STALE_AFTER_PANE_REPAIR
files: [
  { path: "src/os/apps/smux/api.spl", sha256: "9b9534337e0c2422315cdc8f43d0f4dff1468c0b1b28baee0ccb21870a0aa577", lines: 755 },
  { path: "src/os/apps/smux/child_lifecycle.spl", sha256: "49642b39d01f70c635bbca6da5fa9b774772bec33e0ccf238dfe3f5634aa1ec1", lines: 22 },
  { path: "src/os/apps/smux/pane_lifecycle.spl", sha256: "6d7eb5ff6412d5f22b544d4f1e239a50b17facd8c521d689f49ad8b7f981a65d", lines: 100 },
  { path: "test/03_system/tools/smux_pane_lifecycle_spec.spl", sha256: "4332864e197a71f92687a7429e59847c170a5cb837fc1d131b4c25c3c4dbf8ee", lines: 192 },
  { path: "doc/06_spec/03_system/tools/smux_pane_lifecycle_spec.md", sha256: "87738fd6d57eb94e557b7658e6fb6da441781c0188d7962b626d923059e30515", lines: 66 },
  { path: "doc/08_tracking/bug/smux_pane_close_discarded_native_failure_2026_10_25.md", sha256: "7950e6ec6116338e4adc0755159d65749c93f703dfaaf7ab5b30b0f234073e4a", lines: 46 },
]

```

## Cycle 2 focused rereview

The three smux production owner hashes remain unchanged. The stale lifetime expectation finding is source-resolved: existing layout/protocol cases now assert removed window/session inventories and exact unknown-owner errors; a separate pure empty-window snapshot retains independent layout-refusal coverage. The manuals match this distinction. No runtime pass is claimed.

The native scenarios now record both targets live before closure, target absent/survivor live before full cleanup, and both absent after cleanup, with assertions after cleanup. However, **P2 remains open because the selected query is not an arbitrary-PID contract**. New `sosix_process_is_running` merely aliases `process_ops.process_is_running` (line 2121). Its normal Windows C owner `src/runtime/platform/platform_win.h:798` casts the argument to a HANDLE, while Rust `src/compiler_rust/runtime/src/value/sffi/env_process.rs:1183` queries the SPAWNED_CHILDREN registry. Only the standalone core-C `src/runtime/runtime_process.c:72` uses OpenProcess(PID). The returned numeric pipe/ConPTY PID is therefore not a portable input to this alias; the pre-close assertion may falsely reject a real live child. Calling this a universal independent OS-PID query in the manual is inaccurate.

The existing `process_ops.process_exists` (line 2228) provides the required arbitrary-PID contract without the `/bin/ps` fallback used by `process_pid_exists`. Its C owner `runtime_core_host_services.c:131` and Rust owner `env_process.rs:1239` use OpenProcess(PID) on Windows. Root accepted correction cycle 3 using that existing boundary; no new host implementation or ABI is needed. Actual linked-runtime availability remains an execution prerequisite, and PID reuse/provider-query failure/descendant evidence limitations still apply.

Read-only evidence pins: `process_ops.spl` cb4452debfe1b9bb9874759b23eddd2b8cf3f51131f1307398a76039b4b095a2; `platform_win.h` c15c8f0465f14d8e2ced9cb858dbd2d2d542895c9e1f21bbda2b82827bdc4937; `runtime_process.c` c1dbc2e4496afe68fee5a08a98dbb3a3607d7053092a50f85eb47547259630b7; `env_process.rs` 997777e48a5150c6f35e935bd6a9b0ef7223c8990fa243ff66acfb127323ebbe; `runtime_core_host_services.c` 25cfdadce3df4044746a1d57b4df0a484274d311fac8d9f2de957b83d0252ff5. These files were not changed by this review.

All eleven v2 manifest pins matched at review. Eleven new pane cases, one added pure layout case and three corrected existing cases remain unexecuted. Historical v1 pins above are preserved; the following v2 pins identify this focused review input.

```sdn
schema: smux-pane-close-source-freeze-v2
baseline: "bee3e7b9f79228b0d310614b9cef22a62bb81651"
status: SOURCE_FROZEN_WARN_NOT_RUN
source_fix_cycle: 2
new_pane_spec_cases_authored: 11
new_pure_empty_window_case_in_existing_suite: 1
existing_layout_protocol_cases_updated: 3
native_cases_strengthened_with_os_pid_queries: 2
cases_executed: 0
whitespace_check: PASS
native_false_close_evidence: NOT_RUN
readiness: STALE_AFTER_PANE_REPAIR
files: [
  { path: "src/os/apps/smux/api.spl", sha256: "9b9534337e0c2422315cdc8f43d0f4dff1468c0b1b28baee0ccb21870a0aa577", lines: 755 },
  { path: "src/os/apps/smux/child_lifecycle.spl", sha256: "49642b39d01f70c635bbca6da5fa9b774772bec33e0ccf238dfe3f5634aa1ec1", lines: 22 },
  { path: "src/os/apps/smux/pane_lifecycle.spl", sha256: "6d7eb5ff6412d5f22b544d4f1e239a50b17facd8c521d689f49ad8b7f981a65d", lines: 100 },
  { path: "src/lib/nogc_sync_mut/sosix/process.spl", sha256: "986ff221c3b8203201ab6277ba3a161a6bb0d660ac8592f874395d7021fecf33", lines: 14 },
  { path: "test/03_system/tools/smux_pane_lifecycle_spec.spl", sha256: "b7eb0ca6fec01a82cbe721ed4f46b045ee741a35c33ee74155bfc0b11d010b47", lines: 208 },
  { path: "test/03_system/tools/smux_service_layouts_spec.spl", sha256: "c72331c661f86a3e29f3c84cfb84d20fcbd4d6255d6c6255e2df0244716bc9d5", lines: 320 },
  { path: "test/03_system/tools/smux_protocol_features_spec.spl", sha256: "10b1579cbce75a6a8aeb587518f8c318fcfd11a961875309166e1017eac103c3", lines: 666 },
  { path: "doc/06_spec/03_system/tools/smux_pane_lifecycle_spec.md", sha256: "6ee7d6bb2356965d85415a5eed88667851ae0dc4c95dc5d2683bfd6a3b54d16b", lines: 78 },
  { path: "doc/06_spec/03_system/tools/smux_service_layouts_spec.md", sha256: "d8e0091b5d697e31570f11327aea5203cd9cc70942f471d011a948bf5dece2d4", lines: 67 },
  { path: "doc/06_spec/03_system/tools/smux_protocol_features_spec.md", sha256: "4545fea9a203ae8e15004c7efd4ed2da8eccc9a63bc2c478dfff14d4c4f9ca8f", lines: 194 },
  { path: "doc/08_tracking/bug/smux_pane_close_discarded_native_failure_2026_10_25.md", sha256: "5be5f06050c280db1ce839a5cc725445531eccc6fe08f9dd75f0737eefc5aec2", lines: 56 },
]

```

## Cycle 3 final focused disposition

**Both source-review findings are resolved.** This cycle inspected only the remaining PID-query correction, its native test call sites and evidence wording; the unchanged three smux production owners were not reviewed again.

The Sosix facade now exports exactly `process_exists as sosix_process_exists` from the existing process owner. The spec imports that generic facade and uses it for six independent presence observations: both actual returned PIDs present before close; target absent and survivor present after checked target close; both absent after checked session cleanup. Real computed output remains required from target before close and survivor afterward. All ordinary scenario assertions remain after cleanup. No `process_pid_exists` shell fallback, handle-based `process_is_running`, registry-only substitute, new native ABI or fabricated provider response is introduced.

This closes the test-oracle finding at the source-contract level. The already inspected C/Rust `rt_process_exists` implementations query arbitrary Windows PIDs; the new manual correctly distinguishes process-object presence from execution status. It retains PID reuse, retained process objects, query ambiguity, actual linked-runtime/ABI admission and external descendant/Job cleanup limitations. Those are execution evidence requirements, not a source PASS manufactured by changing the expected result.

All eleven v3 manifest hashes matched current bytes. Seven entries retain their v2 hashes; four changed entries are the alias, pane spec, manual and bug report. The prior v1/v2 inputs and finding history remain above. No remaining P0/P1/P2 was identified in the reviewed scope. **WARN / NOT_RUN:** all execution counts remain zero; eleven pane cases, the added pure empty-window control and three corrected existing cases are authored only. Native false/deferred-close, final-pane retry and escalation, actual process absence and linked-runtime/Job receipts remain pending. No compiler, test, build or product executable ran during this review.

### Final v3 input pins

```sdn
schema: smux-pane-close-source-freeze-v3
baseline: "bee3e7b9f79228b0d310614b9cef22a62bb81651"
status: SOURCE_FROZEN_WARN_NOT_RUN
source_fix_cycle: 3
new_pane_spec_cases_authored: 11
new_pure_empty_window_case_in_existing_suite: 1
existing_layout_protocol_cases_updated: 3
native_cases_strengthened_with_os_pid_queries: 2
cases_executed: 0
whitespace_check: PASS
native_false_close_evidence: NOT_RUN
readiness: STALE_AFTER_PANE_REPAIR
files: [
  { path: "src/os/apps/smux/api.spl", sha256: "9b9534337e0c2422315cdc8f43d0f4dff1468c0b1b28baee0ccb21870a0aa577", lines: 755 },
  { path: "src/os/apps/smux/child_lifecycle.spl", sha256: "49642b39d01f70c635bbca6da5fa9b774772bec33e0ccf238dfe3f5634aa1ec1", lines: 22 },
  { path: "src/os/apps/smux/pane_lifecycle.spl", sha256: "6d7eb5ff6412d5f22b544d4f1e239a50b17facd8c521d689f49ad8b7f981a65d", lines: 100 },
  { path: "src/lib/nogc_sync_mut/sosix/process.spl", sha256: "dbf420544794e35f36ea5ea5e02df25da62f92f12e5f75192a1af9ba95e9e1d5", lines: 14 },
  { path: "test/03_system/tools/smux_pane_lifecycle_spec.spl", sha256: "b75e2d887a7f76153e0d45ee99102590be65c795a739aad9799764fd1a41af94", lines: 208 },
  { path: "test/03_system/tools/smux_service_layouts_spec.spl", sha256: "c72331c661f86a3e29f3c84cfb84d20fcbd4d6255d6c6255e2df0244716bc9d5", lines: 320 },
  { path: "test/03_system/tools/smux_protocol_features_spec.spl", sha256: "10b1579cbce75a6a8aeb587518f8c318fcfd11a961875309166e1017eac103c3", lines: 666 },
  { path: "doc/06_spec/03_system/tools/smux_pane_lifecycle_spec.md", sha256: "c348dd2707ae1689a573aac73d693bed7b2ae0d3a201fb58e819d804243af2e3", lines: 87 },
  { path: "doc/06_spec/03_system/tools/smux_service_layouts_spec.md", sha256: "d8e0091b5d697e31570f11327aea5203cd9cc70942f471d011a948bf5dece2d4", lines: 67 },
  { path: "doc/06_spec/03_system/tools/smux_protocol_features_spec.md", sha256: "4545fea9a203ae8e15004c7efd4ed2da8eccc9a63bc2c478dfff14d4c4f9ca8f", lines: 194 },
  { path: "doc/08_tracking/bug/smux_pane_close_discarded_native_failure_2026_10_25.md", sha256: "4fbb03dcf7a38b8aeb5dae48e0d15c82f139d0a21f4979cf28091f7477817b23", lines: 65 },
]

query_contract: EXISTING_ARBITRARY_PID_PROCESS_EXISTS_NO_SHELL_FALLBACK
linked_runtime_query_admission: STILL_REQUIRED_NOT_RUN

```
