# Feature: WM GUI Web 2D Host Environment Hardening

## Raw Request
$sp_dev harden simple wm,gui,web,2d(vulkan/simd backed) lane. add system tests
in modern sspec tests. let it not have mock on middle. and check rendering
buffer. and eventing handlling test from screen come to wm/gui check test.
research web how to make test infra. and use also simple renderdoc. research to
check 1. perf bug in rendering. 2. check missing path. 3. check bug in path.
make test_host_env which test simd(x86,arm,riscv) and vulkan. event propagation
and rendering in buffer and simple renderdoc. with unit and components tests.
make the coverage to 98% or 100%. with pherallel small agents. harden related
tests infra and fix the bugs on rendering.

## Task Type
feature

## Refined Goal
Harden the production screen-to-WM-to-GUI/Web-to-Draw-IR-to-Engine2D pipeline with real host-capability, event, framebuffer, SIMD, Vulkan, RenderDoc, performance, and path-integrity evidence plus measured 98% or better branch coverage of the owned testable contract.

## Acceptance Criteria
- AC-1: A canonical `test_host_env` surface reports x86 SIMD, ARM SIMD, RISC-V vector/SIMD, Vulkan, RenderDoc, display/input, and framebuffer-readback capabilities with stable machine-readable status and concrete unavailable reasons.
- AC-2: Modern SSpec system scenarios use `std.spec.*`, user-facing `step("...")` flows, `@req` traceability, real assertions, and generated operator manuals; no placeholder, mock-middle, fixture-only renderer bypass, raw runtime alias, synthetic backend handle, or CPU-mirror result is accepted as production evidence.
- AC-3: A real input event originating at the screen/host boundary is correlated through WM hit-testing, GUI/Web target dispatch, application callback, damage/composition, Engine2D submission, and the same-frame backend readback; focus, keyboard/text, pointer down/up, window move/maximize, timing, and animation evidence fail closed when any hop is missing.
- AC-4: The canonical production route `SharedWmScene -> DrawIrComposition -> Engine2D` renders deterministic nonblank buffers with absolute pixel or Draw-IR oracles, exact dimensions/stride/format, stable provenance, positive backend handle, completed submission/fence, device-origin readback where claimed, and pairwise ARGB mismatch count zero for comparable Simple/Chrome/Electron artifacts.
- AC-5: SIMD component and unit coverage proves executed-path identity and scalar-oracle parity for available x86, ARM, and RISC-V implementations; unavailable cross-ISA native rows remain explicit blockers with owner, prerequisite, retained artifacts, and exact resume command rather than skips or emulated performance claims.
- AC-6: Vulkan component and system coverage proves validated shader/module use, real queue submission, completion, and device-origin readback; fallback or software execution is labeled honestly and cannot satisfy Vulkan acceptance.
- AC-7: RenderDoc evidence uses the shared Simple/Chrome/Electron capture helpers, records valid `.rdc` files with `RDOC` magic and logs, and keeps host-unavailable or invalid-capture rows blocked rather than substituting screenshots.
- AC-8: Rendering performance is measured with bounded warm-start and representative frame/request workloads, backend identity, latency/throughput/max-RSS counters, and absolute output oracles; every discovered regression is fixed at the shared owner boundary or recorded as a concrete bug with reproduction and measured evidence.
- AC-9: Missing production routes and incorrect routing/fallback/provenance paths found by static and executable analysis are fixed at their common owner, with focused reproduce-before/fix-after tests and no parallel private rendering or event path.
- AC-10: Unit, component/integration, and modern SSpec system coverage jointly measure the owned host-env/event/render contract at 98% branch coverage or better (100% where feasible); uncovered host-only branches are enumerated as blockers and are not counted through mocks.
- AC-11: Architecture, detail design, test plan, agent-task plan, requirements, research, generated manuals, relevant operator guides, and UI stack TLDR remain synchronized with the implemented contract and name every required host/capability row.
- AC-12: Focused checks, UI SSpec evidence audit, RenderDoc/Vulkan aggregate gates, production renderer/event-routing gates, direct-runtime guards, generated-spec layout guard, and applicable compiler/lib/MCP smoke gates each have one recorded result; completion requires all mandatory current-host rows to pass.

## Scope Exclusions
None of the requested WM, GUI, Web, 2D, Vulkan, SIMD, event, buffer, RenderDoc,
performance, path-integrity, or coverage lanes may be excluded. Native
capabilities unavailable on this host remain active blocked rows with resume
plans and do not become PASS.

## Cooperative Review
- Sidecar `local-pipeline-inventory`: map canonical production callers, existing tests, mocks/fallbacks, and likely missing/wrong paths.
- Sidecar `host-env-and-coverage`: inventory existing host/SIMD/Vulkan detection and coverage measurement surfaces.
- Sidecar `renderdoc-web-research`: research authoritative RenderDoc/Vulkan/browser and graphics test-infrastructure practices.
- Sidecar `event-and-buffer-tests`: inventory real screen/input propagation and framebuffer/readback oracles.
- Merge owner: root Codex agent for this lane.
- Final reviewer: root normal/highest-capability Codex after sidecar evidence is reconciled against the live tree.
- Shared interfaces: `TestHostEnv`, `test_host_env()`, `HostCapabilityRow`, `RenderPipelineReceipt`, and `EventPropagationReceipt`; reuse existing names instead if an equivalent owner already exists.
- Manual step flow: `Inspect the real host capabilities`; `Inject one screen-originated event`; `Follow the event through WM and GUI dispatch`; `Render the resulting canonical composition`; `Read back and compare the backend buffer`; `Capture the Vulkan frame with RenderDoc`; `Measure the retained rendering workload`.
- Setup/checker helpers: reuse `scripts/setup/setup-gui-web-2d-vulkan-env.shs`, `test/helpers/renderdoc_capture_helper.shs`, `scripts/check/check-wm-browser-event-routing-evidence.shs`, and existing renderer parity/coverage gates; add only the smallest missing owner helper.
- Fail-fast placeholders: any temporary executable helper must use `assert(false)` or `fail(...)` until real evidence is wired.
- Generated-manual review owner: root Codex agent.

## Runtime Boundary Decision
- runtime_need: No new runtime capability is assumed; host detection, process/file access, rendering, input, and capture must reuse existing facades and production owners.
- facade_checked: `std.io_runtime`, app IO/process facades, canonical WM/Draw IR/Engine2D owners, existing SIMD/backend probes, and shared RenderDoc helpers.
- chosen_path: reuse-facade; add-smallest-owner-facade only when research proves a real gap.
- rejected_shortcuts: raw `rt_*` aliases in specs/apps, fixture-only render branches, direct backend pokes, synthetic handles, CPU mirrors labeled as device readback, screenshot-only RenderDoc claims, mock filesystem/process/input layers, and compatibility renderers presented as the canonical route.

## Research Summary

### Existing Code
- `src/os/hosted/hosted_entry.spl:363-478` is the real winit input/present loop.
- `src/os/compositor/host_compositor_core.spl:775-835,984-1063` owns canonical composition, WM input, damage, and Engine2D routing.
- `src/lib/common/ui/draw_ir.spl:478-560` has reusable event target resolution but no hosted caller.
- `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:34-142` already detects x86, ARM, and RVV levels.
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:744-767` distinguishes device readback from fallback.
- `src/lib/nogc_sync_mut/coverage.spl:1-204` already measures true/false branch execution.

### Reusable Modules
- Reuse hosted compositor, `shared_wm_scene_draw_ir_composition_with_content`, SIMD/backend probes, strict Vulkan spec, live Linux/QMP gates, coverage engine, and shared RenderDoc helpers.

### Domain Notes
- Vulkan validation/debug labels, explicit image-to-buffer readback, RenderDoc in-app frame capture, and CDP input/system/performance domains provide the primary-source model for real correlated evidence.

### Open Questions
- NONE: the user selected Feature B and NFR B.

<!-- sdn-diagram:id=wm_gui_web_2d_host_env_hardening.research -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=wm_gui_web_2d_host_env_hardening.research hash=sha256:auto render=ascii
@layout dag
@direction LR
HostInput -> HostCompositor
HostCompositor -> DrawIrComposition
DrawIrComposition -> Engine2D
Engine2D -> DeviceReadback
HostCompositor -x GuiWebSemanticDispatch
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=wm_gui_web_2d_host_env_hardening.research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Requirements
- REQ-1 (AC-1,5,6): aggregate real host/ISA/Vulkan/capture/readback capabilities using existing probes.
- REQ-2 (AC-2,3,9): route one real screen event through WM and semantic GUI/Web dispatch without a mock middle.
- REQ-3 (AC-4,6,7): correlate canonical Draw IR submission, completion, device readback, exact pixel oracle, and valid RenderDoc capture.
- REQ-4 (AC-8): measure warm rendering latency/throughput/RSS by stable hardware bucket and fix or file every reproduced regression.
- REQ-5 (AC-10): achieve at least 98% measured branch coverage of the owned contract, with 100% for feasible pure classification code.
- REQ-6 (AC-11,12): keep manuals/guides/design current and run each required fail-closed gate once.

## Architecture

- Add a pure host-env/receipt contract, a test-only live capability aggregate,
  and a hosted-only persistent BrowserSession adapter.
- Reuse the existing `HostWmInputReceipt`, Linux hosted evidence protocol,
  `SharedWmScene -> DrawIrComposition -> Engine2D` route, backend readback, SIMD
  probes, Vulkan probes, and RenderDoc helpers.
- Keep BrowserSession out of shared compositor/bare-metal dependencies; only
  hosted entry owns semantic Web sessions.
- Reject synthetic queues, compatibility renderers, CPU mirrors, screenshots,
  and new raw runtime access as production proof.

## Design Artifacts

- `doc/04_architecture/wm_gui_web_2d_host_env_hardening.md`
- `doc/04_architecture/wm_gui_web_2d_host_env_hardening_tldr.md`
- `doc/05_design/wm_gui_web_2d_host_env_hardening.md`
- `doc/05_design/wm_gui_web_2d_host_env_hardening_tui.md`
- `doc/05_design/wm_gui_web_2d_host_env_hardening_gui.md`
- `doc/03_plan/sys_test/wm_gui_web_2d_host_env_hardening.md`
- `doc/03_plan/agent_tasks/wm_gui_web_2d_host_env_hardening.md`

## Phase
verify-failed

## Specs

- `test/01_unit/lib/common/ui/host_env_contract_spec.spl`
- `test/02_integration/os/hosted/hosted_web_content_session_spec.spl`
- `test/03_system/gui/feature/wm_gui_web_2d_host_env_hardening_spec.spl`
- The specs deliberately reference the missing pure contract, hosted semantic
  adapter, compositor content helpers, and live host-env aggregate. They remain
  red until implementation; generated manuals follow a runnable pure-Simple
  docgen binary.

## Implementation

- `src/lib/common/ui/host_env_contract.spl`
- `src/app/test/test_host_env.spl`
- `src/os/hosted/hosted_web_content_session.spl`
- `src/os/compositor/host_compositor_core.spl`
- `src/os/hosted/hosted_wm_evidence.spl`
- `src/os/hosted/hosted_entry.spl`
- `scripts/check/check-linux-hosted-wm-live-window-evidence.shs`

The missing hosted semantic dispatch path is now routed through a persistent
BrowserSession registry. The live proof window exposes a visible text input;
X11 pointer/text events retain WM/semantic/callback/mutation identity and update
the authoritative window body before the canonical Engine2D render.

## Verification

STATUS: FAIL

Third resumed blocker audit (2026-07-26): the concurrent
`src/runtime/runtime.h` conflict, 12,121,010-byte `.git/index.lock`, bootstrap
seed at the release path, missing `renderdoccmd`, and unavailable native
ARM/RISC-V hosts are unchanged. All remaining acceptance proofs depend on one
or more of these external state changes; capped checks were not rerun.

Fresh resumed audit: cached pure-Simple
`build/bootstrap/stage2_memfix/simple` passed the host contract 11/11, proving
the focused test is not seed-only. It is not accepted for deployment because
its runner prints denormal garbage for the configured safeguard percentages,
showing stale compiler/runtime ABI behavior. Its bounded `simple check` also
confirmed the specs correctly require `simple test`; the earlier silent check
stall is specific to the repair runtime. The same pure compiler ran
`test_host_env` successfully and emitted valid `simple-test-host-env-v1` JSON:
x86 SIMD passed; every unavailable native/live row remained fail-closed with
an exact resume command.

Path-integrity audit fix: `test_host_env` previously pointed Vulkan, RenderDoc,
display/input, and framebuffer rows back to its aggregate JSON rather than the
source evidence that determined each result. The shared row helper now retains
the exact Vulkan, RenderDoc, SIMD-matrix, or live-WM artifact path for both PASS
and blocked rows. A bounded pure-Simple run emitted the corrected paths with an
empty validation reason.

Fresh resumed blocker audit 3/3: `src/runtime/runtime.h` still contains the
same concurrent conflict, `.git/index.lock` remains 12,121,010 bytes with the
same timestamp, the canonical release path still identifies as a Rust bootstrap
seed, and `renderdoccmd` remains absent. Native ARM/RISC-V hosts are also still
unavailable. The remaining acceptance evidence cannot be generated safely
without external state changes.

Git lock recovery: a later ownership audit found no process holding
`.git/index.lock`; only a read-only `jj log` was active. The unchanged stale
lock was moved recoverably to
`/tmp/simple-index.lock.stale-20260726T111610`. A piped diagnostic then
terminated `git status` early and left a new lock; that known local lock was
moved to `/tmp/simple-index.lock.stale-20260726T235732`. An unpiped
`git status --porcelain=v1 --untracked-files=no` completed with status 0 and
left `.git/index.lock` absent.

Runtime/QEMU recovery (2026-07-27): the `src/runtime/runtime.h` conflict was
resolved by retaining the shared debug, interpreter-runtime, and Vulkan
quarantine declarations; all have live implementations/callers. The full SIMD
owner matrix then compiled x86_64, AArch64, and RISC-V/RVV runtime owners and
executed architecture-specific x86, NEON, and RVV binaries through the existing
native/QEMU lane. Target-binary path markers all passed.

Simple RenderDoc clarification: the repo-native counterpart is the existing
Simple 2D RenderDoc Backend Equivalence capsule, not just the external
`capture-simple` wrapper. Its pure record/diff core passed 6/6, exact
equivalence integration passed 5/5, and the pure-Simple RDC XML inspector
passed 5/5. The SPipe/LLM feature-expert wiki, canonical guide, and glossary
now identify the implemented core and fail-closed gaps. Production backend
matrices, SimpleOS guest/QEMU receipt specs, aggregate checker, and manual audit
still contain explicit fail placeholders, so counterpart completion is not
claimed.

Tracking split:
- Local implementation remains active in
  `doc/08_tracking/feature/simple_renderdoc_counterpart_completion_2026-07-27.md`.
- Native/platform qualification is postponed in
  `doc/08_tracking/todo/simple_renderdoc_external_host_postponed_2026-07-27.md`
  until local focused and aggregate checks are green.
- Shared feature/TODO databases were not edited because concurrent lanes modify
  them.

- PASS: numbered-artifact guard (`--working`, `--staged`).
- PASS: direct env/runtime guard (`--working`, `--staged`).
- PASS: no executable `*_spec.spl` files under `doc/06_spec`.
- PASS: shell syntax and `git diff --check` for the owned lane.
- PASS: the pure host contract spec passed 11/11 and hosted WM evidence passed
  7/7 with `build/bootstrap/repair-full/x86_64-unknown-linux-gnu/simple`.
- PASS: `test_host_env` evidence classification is now entirely routed through
  the shared pure contract. Vulkan, RenderDoc, display/input, and framebuffer
  predicates cover acceptance plus every missing-field rejection. The
  framebuffer predicate now consumes the live producer's real
  `framebuffer_status`, `readback_source`, and `glyph_crop_live_match` fields
  instead of the nonexistent `argb_mismatch_count` key.
- PASS: `test_host_env` emitted valid `simple-test-host-env-v1` JSON; x86 SIMD
  passed and unavailable ARM, RISC-V, Vulkan, RenderDoc, display-input, and
  framebuffer rows remained blocked with exact resume commands.
- PASS: Vulkan host check found the hardware NVIDIA TITAN RTX/loader.
- PASS: the shared WM pixel buffer now uses runtime-owned memory fill/copy
  externs; its clear, row replication, clipping, and readback spec passed 2/2.
- PASS: coverage wiring/stable-identity source contract passed 4/4. The
  evaluator now reuses stable AST IDs and interpreter externs retain runtime
  decision/condition SDN.
- PASS: x86 AVX2, ARM NEON, and RISC-V RVV standalone kernel parity executed
  successfully; the RISC-V harness's false `scalar path` label was fixed and
  the matrix now retains fail-closed per-architecture path markers.
- PASS: `test_host_env` consumes the real SIMD matrix and reports valid JSON;
  x86 is native PASS, while QEMU ARM/RVV evidence remains honestly blocked
  pending native hosts and the runtime-owner build.
- PASS: requirement annotations now use the authoritative zero-padded
  `REQ-001` through `REQ-012` identities across unit, component, and system
  specs.
- PASS: the feature SSpec no longer accepts field presence as production
  evidence. It requires Vulkan and RenderDoc PASS rows, exact device readback,
  exact live glyph output, input/move/maximize/restore receipts, a no-fallback
  path, and a passing retained 200-frame 4K measurement.
- PASS: direct docgen refreshed all three changed manuals with zero stubs.
- FAIL: RenderDoc is unavailable (`missing-renderdoccmd-in-search-paths`).
- WARN: the component's unresolved raw `memset` owner is fixed, but the
  three-cycle cap prevents rerunning that component this session.
- FAIL: a full 98% coverage run still needs a rebuilt accepted pure-Simple
  release runtime. The `src/runtime/runtime.h` conflict is resolved, but
  `bin/simple --version` currently identifies the deployed binary as the Rust
  bootstrap seed.
- PASS: the full SIMD owner compile and target-binary matrix passes for x86,
  AArch64 NEON, and RISC-V RVV; QEMU rows remain correctness evidence, while
  native ARM/RISC-V promotion stays blocked on those hosts.
- FAIL: SPipe docgen produced all three manuals with zero stubs, but its
  quality accounting remained stale after three cycles; see
  `doc/08_tracking/bug/spipe_docgen_stale_manual_quality_2026_07_26.md`.
- FAIL: the retained 4K gate rejects the available runtime because it is not
  the deployed release self-hosted binary.
- PASS: the stale 12,121,010-byte `.git/index.lock` was moved recoverably after
  confirming it had no holder; `git status` succeeded afterward.
- FAIL: strict workspace-root audit reports 447 broad pre-existing/concurrent
  FILE.md violations. The owned `.spipe` directory is among the globally
  undeclared `.spipe/*` entries.
- FAIL: rendering-source-coupling audit produced no output for two minutes and
  was terminated once; it was not retried.
- FAIL: a syntax-only three-spec `simple check` emitted no output for 90
  seconds and was terminated once; see
  `doc/08_tracking/bug/simple_check_multi_spec_hang_2026_07_26.md`.
- FAIL: live X11/RenderDoc/cross-ISA/performance artifacts have not been
  regenerated from this source state. Blocked rows retain exact resume
  commands through `test_host_env`.
- FAIL: measured 98% branch coverage remains unavailable.
- PASS: refreshed `build/test-artifacts/test_host_env/evidence.json` after the
  newer SIMD matrix. The diagnostic `simple-test-host-env-v1` aggregate reports
  x86 SIMD PASS and preserves ARM/RISC-V native SIMD, Vulkan, RenderDoc,
  display/input, and framebuffer readback as blocked with evidence paths and
  exact resume commands. The diagnostic Rust-seed runner is not qualification.
- FAIL: no branch-coverage SDN exists at `build/coverage/coverage.sdn`,
  `.coverage/coverage.sdn`, or `coverage.sdn`; the 98% threshold still requires
  a source-matched deployed pure-Simple runtime.
- PASS: kernel IPC now owns exact bounded payload copies. The modern
  `ipc_payload_roundtrip_spec.spl` reproduced the missing API before the fix and
  passes 2/2 afterward; its generated manual is complete with zero stubs.
- PASS: exported IPC shims now retain the scheduler and IPC manager returned by
  send, receive, create, and connect handlers. The modern
  `ipc_shim_state_spec.spl` reproduced discarded state as `1 == 2`, then passed
  1/1 after the shared shim fix; its generated manual is complete with zero
  stubs.
- FAIL: the production screen-to-remote-client chain remains blocked after the
  queue/state fixes. Syscall send still does not safely copy the WM wire bytes,
  receive lacks bounded user copyout, create/connect still use the literal
  `"port"`, WM array pointers address the array header, and the prefixed method
  word is parsed inconsistently. The disk browser remains a marker-only SMF,
  so QEMU must not claim client receipt or framebuffer mutation yet.
- IMPLEMENTED, RERUN PENDING: added bounded
  `vmm_copyout_bytes_to_space` beside the real copy-in owner. Its modern SSpec
  preflights writable VMAs/PTEs, crosses two mapped pages, and reads exact bytes
  back through production copy-in. The first post-implementation diagnostic run
  exposed a pre-existing VMM builder bug: successful copy-in discarded `push`
  results and returned an empty byte array. All local byte/text/vector builders
  now retain their returned values. The three-cycle cap prevents another run in
  this session; resume exactly with
  `build/bootstrap/repair-full/x86_64-unknown-linux-gnu/simple test test/01_unit/os/kernel/memory/vmm_copyin_spec.spl --mode=interpreter`.
- IMPLEMENTED, RERUN PENDING: added `IPC_WIRE_V1_FLAG` so legacy driver
  metadata IPC remains unchanged while WM uses authenticated reply ports,
  mapped method-prefixed copyin, kernel-owned payloads, fixed 32-byte headers,
  and bounded caller-buffer copyout. WmService and WindowClient now use
  4128-byte receive buffers and parse methods from the envelope header. The
  no-middle-mock syscall SSpec spans real VMM page walks, send, queue, receive,
  copyout, and exact readback. Its reproduce-before run failed; the next run
  exposed discarded VMA test setup, now fixed. The three-cycle cap defers the
  final run:
  `build/bootstrap/repair-full/x86_64-unknown-linux-gnu/simple test test/01_unit/os/kernel/ipc/ipc_syscall_wire_spec.spl --mode=interpreter`.
- IMPLEMENTED, RERUN PENDING: syscall create/connect now copy a non-NUL name of
  at most 64 bytes through the registered task VM space; anonymous create
  remains valid, while empty connect, unmapped pointers, embedded NUL, and
  oversized names fail closed. WmService and WindowClient pass first-element
  byte-array pointers rather than string/array headers. The mapped-name SSpec
  reproduced the literal `"port"` bug; its next run reached the manager but
  exposed an immutable test-field method call, now fixed. The three-cycle cap
  defers the final run:
  `build/bootstrap/repair-full/x86_64-unknown-linux-gnu/simple test test/01_unit/os/kernel/ipc/ipc_named_port_wire_spec.spl --mode=interpreter`.
- STATIC COVERAGE INTENT: added the four missing pure host-contract cases:
  accepted `fail`, nested invalid-row propagation, height-only invalid
  dimensions, and multi-row JSON serialization. The refreshed manual is
  complete with zero stubs. No coverage SDN exists, so this is not a measured
  98/100% claim.
- PASS: the six `engine.spl` conflict hunks were resolved exactly to the
  parent/origin implementation. The previously-red facade clip/mask gate now
  passes 8/8.
- PASS: the facade scaled-image case now exercises real 2x2-to-4x2 resampling,
  clip, mask, software, and CPU-SIMD paths instead of the equal-size shortcut.
- PASS: current-host SIMD aggregate reports AVX2 executed, exact scalar parity,
  zero fill/copy/alpha/scroll/diagram mismatches, and positive kernel hits.
- PASS: the refreshed facade manual exposes all eight scenario steps and
  reports zero stubs. Final docgen qualification remains blocked because the
  deployed `bin/simple` is the Rust seed.
- PASS: the missing Simple RenderDoc aggregate checker now exists, passes its
  fail-closed shell self-test, and its modern SSpec passes 2/2 diagnostically.
  It reports 18 retained rows with timing/RSS/path/REQ fields.
- FAIL: the focused Simple RenderDoc aggregate is honestly blocked: deployed
  `bin/simple` is a Rust seed, local production/QEMU/manual specs retain
  explicit fail helpers, and the external RenderDoc capture is unavailable.
- PASS: the manual/workflow audit placeholder was replaced with real pairing,
  modern-source, generated-layout, and cooperative-review assertions; its
  refreshed manual reports zero stubs.
- FAIL: the manual audit passes 3/4 diagnostically and rejects the remaining
  `pending_*` helpers across production, replay, QEMU, board, and SIMD specs.
- Context: multiple independent Codex/Claude builds and long-running checks are
  active in the shared worktree.

## Log
- dev: Created state file with 12 independently testable acceptance criteria (type: feature).
- research: Reused 12 existing owner/test surfaces, identified 6 concrete gaps, and produced feature/NFR options with authoritative web sources.
- requirements: User selected Feature B and NFR B; wrote final feature/NFR requirements and deleted option drafts.
- arch: Designed the hosted-only semantic bridge, pure receipt validation, real Linux system flow, cross-host blocker matrix, and sidecar/merge ownership.
- spec: Added failing unit, component, and modern SSpec system scenarios for the selected Feature B/NFR B contract.
- implement: Added the pure host contract, retained capability aggregate, real hosted BrowserSession event bridge, semantic receipt, and live wrapper gate.
- verify: Restored coverage hooks and stable decision retention, replaced raw WM pixel memory externs with runtime owners, passed focused 4/4 and 2/2 checks, and generated the buffer manual; rebuilt-runtime coverage, RenderDoc, deployed-runtime perf, live lock, strict workspace, and source-coupling remain release-blocking.
- verify: Executed x86 AVX2, ARM NEON, and RISC-V RVV parity, fixed false RVV path labeling, added retained path-marker gates, and wired honest QEMU/native distinctions into `test_host_env`.
- verify: Resolved the Engine2D parse conflict without changing parent behavior,
  strengthened the scaled clip/mask SSpec, passed the focused 8/8 and current
  x86 AVX2 aggregate gates, and refreshed its zero-stub manual.
- implement: Added the canonical Simple RenderDoc aggregate by reusing existing
  leaf specs and capture keys; it rejects non-Stage-4 binaries and preserves
  every local, QEMU, and external blocker instead of promoting missing evidence.
- implement: Replaced the Simple RenderDoc manual-contract placeholder with a
  real 14-spec audit; it now fails only on remaining counterpart placeholders.
- implement: Added the production Engine2D backend-render capture adapter,
  retained concrete Vulkan owners for both compatibility lanes, and replaced
  the provenance matrix placeholder with real facade/readback/fallback checks.
  The generated manual has zero stubs.
- verify: The focused provenance source parses and its pure classification path
  runs, but live interpreter cases hit the diagnostic binary's stale
  `rt_is_interpreter_runtime` extern table. Native SSpec mode delegates to the
  forbidden Rust seed without a source argument. Both are tracked as a fresh
  Stage-4 environment prerequisite and were not retried.
- implement: Replaced the production surface-matrix placeholder with exact
  facade anchors, invalid input/proof rejection, deterministic replay, and 100
  fresh frames. The focused software-only matrix passes 5/5.
- implement: Added strict architecture-specific SIMD facade admission using
  real native-hit and bit-exact evidence. The x86 facade-vs-scalar integration
  spec has no pending helper and passes 4/4; its manual has zero stubs.
- implement: Removed all remaining `pending_*` helpers from the four
  SimpleOS/QEMU/board counterpart specs without promoting unavailable hosts.
  Production validation now rejects zero guest receipt hashes and binds serial
  boot/frame identities to capture boot/frame identities.
- verify: Portable render/SIMD validation passes 14/14; the manual/contract
  audit passes 4/4 and verifies both canonical and legacy manuals. Diagnostic
  system results are protocol 3/4, guest 1/5, board 3/4, and SIMD 2/6; every
  remaining failure is an explicit live QEMU, complete guest SIMD receipt, or
  physical-board prerequisite recorded in the external-host TODO.
- verify: RenderDoc replay inspection passes 4/4. Fresh Stage-4, RenderDoc,
  native ARM/RVV, live QEMU receipt, physical-board, coverage, and performance
  rows remain active and block completion.
- bug: Recorded the zero-production-caller receipt producer/parser gap in
  `doc/08_tracking/bug/simpleos_backend_render_receipt_producer_parser_missing_2026-07-27.md`
  with exact live-QEMU acceptance criteria.
- implement: Added complete 256-bit receipt digests, a fixed-width no-allocation
  UART byte codec, bounded host parser, and target-evidence join. Separated
  retained PPM artifact integrity from decoded raw-pixel integrity.
- verify: Receipt codec passed 5/5 before the target-evidence join. The third
  cycle found a multi-line-condition parse error; source is corrected and the
  exact fresh-run command is tracked, but the mandatory three-cycle cap stops
  further execution this session.
- bugfix: VirtIO-GPU full/damage flush now returns checked results, validates
  transfer plus resource-flush responses, rejects cache/range failures, and
  logs compatibility-wrapper errors. Its focused recovery/response spec passes
  12/12; live device evidence remains pending.
- implement: Added bounded kernel-owned IPC envelopes and preserved state across
  all four exported IPC shim operations. Modern payload and shim-state SSPecs
  have reproduce-before/fix-after evidence and zero-stub generated manuals.
- verify: Refreshed the host-environment aggregate once after the SIMD evidence
  changed. x86 SIMD is PASS; native ARM/RISC-V, Vulkan, RenderDoc,
  display/input, framebuffer readback, and measured branch coverage remain
  honest blockers rather than mock or fallback passes.
- bugfix: Added safe explicit-address-space copyout and cross-page modern SSpec
  coverage. The regression also found and fixed empty-success results from all
  VMM byte/text/vector builders; source is corrected, but the mandatory bounded
  iteration cap defers the final rerun.
- implement: Added the versioned bounded IPC envelope path and migrated WM send,
  receive, reply, input, close, and focus traffic without changing legacy
  driver-service behavior. Its zero-stub manual is generated; final execution
  is deferred by the bounded iteration cap.
- bugfix: Replaced hardcoded IPC service names with bounded VMM copyin and
  corrected WM/client first-element pointers. Added a zero-stub mapped-name
  SSpec; final execution is deferred by the bounded iteration cap.
- spec: Filled the remaining visible host-contract branch-intent cases without
  promoting static inspection to measured coverage.
- implement: Built and exactly staged a real freestanding x86_64 browser-demo
  ELF, migrated its bounded userspace receive path to the versioned WM wire,
  and added bounded guest polling plus correlated ready/event/content-applied
  markers and content-region framebuffer-delta admission.
- verify: The refreshed browser guest/staging contract passes 1/1 and its
  generated manual is complete with zero stubs. The focused Simple shell check
  terminated with exit 255 after unrelated compiler warnings, so it is not
  qualification evidence. A real QEMU rerun remains required to verify the
  pointer-release repaint fix and correlated client mutation/readback:
  `sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
- bugfix: Missing native ARM/RISC-V SIMD rows now retain the canonical SIMD
  matrix evidence path instead of self-referencing the aggregate
  `test_host_env` output. The focused modern unit source contract passes 1/1
  and its generated manual is complete with zero stubs. Regenerating the
  fullscreen evidence manual also removed two stale merge-conflict markers.
- perf-bugfix: `HostCompositor.render_frame_engine2d` now returns on settled
  damage before advancing the scene revision, reading the clock, or rebuilding
  Web content frames and their caches. The focused source-order contract passes
  1/1 with a zero-stub manual. The real software-backend behavioral regression
  is present, but the diagnostic runner timed out at 120 seconds before
  executing it; TODO 572 retains the admitted pure-Simple rerun requirement.
- bugfix: SimpleOS browser-event evidence no longer admits a stale pre-click
  client marker followed by an unrelated window update. The client marker now
  carries the real window id, the shell arms and accepts `update_tree` only for
  the clicked remote window, and the QMP parser scans only post-click serial
  bytes with strict client-event-before-content-applied ordering. The rebuilt
  freestanding ELF and focused modern contract pass; live QEMU remains pending.
- bugfix: Host capability evidence classification now requires exact unique
  retained keys instead of substring matches. Prefixed aliases, contradictory
  duplicate Vulkan status, prefixed RenderDoc magic, and an empty semantic
  target all fail closed; the previously uncovered `fail`-without-reason cell
  is also asserted. The pure owner spec passes 12/12 with a zero-stub manual.
  This closes visible branch intent but is not a measured 98% coverage claim.
- bugfix: Simple RenderDoc target validation now requires a valid guest
  rendering-buffer SHA-256 before comparing it with the capture and oracle.
  An empty guest hash can no longer produce `qemu-verified`; the pure portable
  render/SIMD spec also rejects CPU-mirror guest readback instead of accepting
  its hash as device evidence and rejects noncanonical pixel formats before
  correlating hashes. It passes 17/17 with a refreshed zero-stub manual.
- verify: The exact-key host-evidence unit now exercises retained CRLF input;
  all 12 cases still pass. This covers the explicit normalization branch but
  does not substitute for a measured whole-contract branch-coverage report.
- bugfix: Simple RenderDoc device-readback admission now requires a nonempty
  guest driver identity; anonymous device receipts can no longer become
  `qemu-verified`. The pure spec also covers the previously untested missing
  external capture-pixel hash branch and passes 19/19 with a zero-stub manual.
- verify: A scoped host-contract run with `--coverage` passed 12/12 but the
  available diagnostic binary emitted no coverage summary and created none of
  `build/coverage/coverage.sdn`, `summary.md`, or `uncovered.md`. The RenderDoc
  target now declares 100% cover intent; TODO 586 records the exact accepted
  pure-runtime commands and 98% threshold. No measured percentage is claimed.
- bugfix: REQ-018 render-target admission now requires complete guest
  display-path identity (controller plus positive scanout/resource IDs) and
  memory-path identity (DMA/cache/IOMMU modes), with exact failing field paths.
  The portable pure spec passes 21/21 and its manual remains zero-stub.
- bugfix: Boot transport and external capture-tool identity are now mandatory
  for both QEMU and physical-board render evidence instead of being enforced
  only for boards. The portable pure spec passes 23/23 with exact failure paths
  and a refreshed zero-stub manual.
- bugfix: Rendering-buffer geometry validation now checks positive fields and
  guards row-byte and total-frame-byte arithmetic with division before
  multiplication. Oversized untrusted dimensions can no longer wrap `i64` and
  reach `qemu-verified`; the portable pure spec passes 25/25.
- bugfix: Platform model and revision are now required for QEMU as machine
  identity and for physical boards as board identity; board ID and serial hash
  remain physical-only. The portable pure spec passes 26/26 with exact paths.
- bugfix: Physical-board serial-digest failures now report
  `board_serial_hash` instead of the unrelated `board_id` path. A
  reproduce-first diagnostic run failed 26/27 at that assertion; the owner
  guard was split and the expanded runtime/architecture/firmware truth table
  then passed 28/28. The refreshed manual is complete with zero stubs. This is
  diagnostic seed evidence only; TODO 572 and TODO 586 still require an
  accepted pure-Simple runner and measured coverage artifacts.
- audit: Remaining host-independent wrong-path candidates are the compound
  capture-correlation, frame-completion, serial, capture, and oracle guards.
  They remain locally actionable; live QEMU, native ARM/RISC-V, physical-board,
  Vulkan, RenderDoc, display/input, and measured coverage remain environment
  gates rather than exclusions.
- bugfix: The remaining compound render-receipt guards now report the exact
  invalid field for frame/capture correlation, surface/present completion,
  serial evidence, capture evidence, and oracle evidence. One reproduce-first
  diagnostic run failed 28/29; the shared validator guards were split and the
  expanded spec then passed 29/29. Docgen produced one complete 290-line manual
  with zero stubs. The diagnostic seed still does not qualify TODO 572 or
  measured-coverage TODO 586.
- bugfix: The live QEMU wrapper no longer admits an Engine2D provenance marker
  from any/stale window after a remote-browser click. It extracts the positive
  window ID from the correlated ready marker, requires that exact
  `window_id` in the final `content-presented` receipt, and records it in
  `evidence.env`. The live SSpec now binds ready/event/applied/provenance
  markers and the changed content-buffer hashes to that one window.
  `sh -n` plus the exact/negative source invariant passed.
- test-infra: The broader QEMU source-contract SSpec is green again at 14/14
  under the diagnostic `run` evaluator. Its seven failures were test drift:
  brace interpolation in source and shell fixtures, renamed input-compositor
  owners, the correlated pointer-release argument, and the current themed
  full-height Web render call. The run also exposed that disk SHA-256 was
  recorded only after browser staging; hash capture now precedes that
  fail-closed gate, so failure evidence retains the real disk identity.
  Docgen remains complete with zero stubs and one existing short-manual warning.
  Another active session owns the stale-admission rebuild and live TODO 585
  QEMU run; diagnostic source coverage is not live guest evidence.
- live-qemu: The externally owned TODO 585 run completed. Its exact retained
  kernel SHA-256 is
  `9d6da02634c90a1e68e2105b21f35050f3411bd9b85dbb20ec8c42097d3cd1ec`;
  it reached the 3840x2160 ARGB scanout and then trapped at `0x08530b3b`
  before production readiness or any QMP capture. Address mapping against that
  exact ELF identifies `_engine2d_draw_ir_render_batch_embedded`; the trap
  string is the compiler's impl-less duck-dispatch diagnostic.
- bugfix: The live trap was the first `batch.commands.len()` field-projection
  call. The shared batch renderer now binds one explicitly typed
  `[DrawIrCommand]` local and routes all length/render branches through it,
  matching the existing typed embedding guard and preserving rendering
  semantics for every caller.
- verify-gap: Docgen refreshed the two-scenario Engine2D compositor contract
  with zero stubs. The direct evaluator proved the pre-existing settled-frame
  scenario is green and isolated the new scenario's failure to an absence
  check matching the explanatory comment rather than executable code. The
  check now targets only executable call shapes; it was not rerun after the
  three-cycle cap, so no final PASS is claimed. The broader Draw IR unit spec
  currently fails parsing before execution, and the long fullscreen
  source-contract hit its 120-second per-file runner ceiling. Rebuild one fresh
  admitted kernel and rerun the live wrapper once; do not reuse the old trap
  address with a different ELF.
- test-infra: Removed the extra closing bracket that prevented
  `draw_ir_adv_spec.spl` from parsing. The spec now executes all 20 scenarios.
  Its stale transactional-preflight scenario now verifies the implemented
  per-command contract: supported commands paint while unsupported siblings
  are skipped and reported. Composition execution also restores the
  GPU-unavailable fallback flag from original scalar inputs when the returned
  cross-module plan loses that bool. The final diagnostic run reached 19/20;
  one unnamed result-contract assertion remains red at the three-cycle cap.
  Docgen refreshed the complete zero-stub 20-scenario manual.
- coverage-infra: Traced the current pure-Simple coverage route end to end.
  `--coverage` is preserved and parsed, collection markers are merged, and the
  three report files are written unconditionally; the prior diagnostic runner
  predates that source and contains no report signature. An isolated full-CLI
  bootstrap repaired two literal conflict-marker hunks in the shared bootstrap
  script, passed Stage 2 sanity, and produced a Stage 3 compiler that passed
  sanity. Admission then failed closed because another workspace changed Git
  state during the build (`git-head-or-dirty-state-changed-during-bootstrap`).
  TODO 586 retains the exact stable-revision rebuild and two-report commands;
  measured 98/100% coverage remains unclaimed.
- sync: Refreshed the stale default workspace and semantically resolved all
  eight resulting QEMU/Web/Draw-IR/compositor conflicts. Marker checks,
  `git diff --check`, QEMU wrapper syntax/mode, and its guest-ISA self-test
  pass. Committed `main` is synchronized with GitHub at `2dbe6a0dc14f`; the
  remaining 558-path mixed working snapshot was not bulk-committed.
- coverage-infra: A detached exact-source worktree removed the concurrent-Git
  provenance race. It rebuilt Rust authority, passed Stage 2 sanity, and passed
  canonical Stage 3 provenance; the accepted compiler SHA-256 is
  `af6a3e1b19156793bba13f7294ba60319cca1c31abdfffed68a7f49472f862e9`.
  Binary, provenance, and Stage 4 log are retained under
  `build/coverage-bootstrap-586-pinned/`. Stage 4 then failed on the reserved
  identifier `match` in pinned `gzip/lz77.spl`; the live worktree already uses
  `matched`. The third-cycle cap prevents another full-CLI build, so no
  coverage artifact smoke or measured 98/100% claim is made this session.
- perf-evidence: The retained showcase wrapper was fabricating
  `frame_p50_ns` and `frame_p95_ns` by copying the mean. The producer now
  records every one of 200 post-warmup presents, computes real p50/p95, and
  reports the sample and warmup counts; the wrapper rejects missing, partial,
  or inverted distributions. The focused SSpec reached 7/9 on all three
  allowed cycles with scenario names suppressed by the diagnostic runner.
  A later stale-workspace refresh restored the pre-fix files, so the root fix
  and aggregate gate were reapplied and pass shell syntax/diff checks, but the
  capped SSpec was not rerun. No native 4K/8K performance PASS is claimed.
  Continue from
  `doc/08_tracking/bug/widget_showcase_frame_distribution_unverified_2026-07-27.md`.
- bugfix: Split the SimpleOS render-evidence capture correlation guard so a
  boot mismatch reports `capture_boot_id` and a frame mismatch reports
  `capture_frame_id`. The existing identity-disagreement SSpec now exercises
  both paths and passes 29/29 under the diagnostic interpreter. Docgen
  refreshed one complete manual with zero stubs. This is source/test evidence,
  not accepted-runtime, live Vulkan, QEMU, or RenderDoc qualification.
- bugfix: Split the SimpleOS SIMD guest-identity guard so invalid image hash,
  missing boot/frame identity, and missing surface handle report their exact
  discriminator instead of an empty operation. The x86/ARM/RISC-V evidence
  SSpec now covers all four field paths and passes 30/30 under the diagnostic
  interpreter; docgen refreshed one complete manual with zero stubs. Live
  target-native SIMD execution and accepted-runtime coverage remain separate
  TODO 580/TODO 586 gates.
- bugfix: Split the SIMD pixel-evidence hash guard so malformed scalar-oracle,
  SIMD-output, and QMP-capture hashes identify the exact field. The existing
  exact-pixel disagreement scenario now covers all three invalid-hash branches;
  the focused diagnostic SSpec remains green at 30/30 and its refreshed manual
  is complete with zero stubs.
- bugfix: Split the remaining SIMD result-correlation and required-operation
  compound guards. Scalar-to-SIMD, SIMD-to-QMP, and mismatch-count failures now
  name their exact field; missing fill/copy/alpha/scroll kernels now name the
  absent operation. The focused diagnostic SSpec remains green at 30/30 and
  docgen produced one complete manual with zero stubs.
- bugfix: Completed the SIMD compound-guard discriminator pass. Requested vs
  detected ISA and architecture/ISA incompatibility are distinct; invalid
  dispatch count, vector chunk count, and lane width name the exact counter;
  scalar fallback count and reason are independently reported. The focused
  diagnostic SSpec passes 30/30 and docgen produced one complete manual with
  zero stubs. This remains source-level evidence pending accepted target-native
  x86/AArch64/RV64 runs and measured TODO 586 coverage.
- bugfix: Split backend receipt event ordering from event-capacity admission.
  A correctly ordered 65th event now reports `too-many-events` instead of the
  false `event-out-of-order` reason. The bounded receipt component SSpec passes
  5/5 under the diagnostic interpreter and docgen refreshed one complete manual
  with zero stubs.
- bugfix: Closed a screen-to-WM-to-Web wrong-path admission in the freestanding
  browser client. Relative motion precedes button-down in the QEMU harness, but
  the client previously mutated content on the first input message; it now
  requires a complete 28-byte `MouseDown` wire payload before emitting the
  browser event marker or updating pixels. The focused staging SSpec passes
  1/1, the real x86_64 freestanding browser ELF rebuild succeeds, and docgen
  produced one complete manual with zero stubs. A fresh live QEMU click/readback
  remains under TODO 585.
- bugfix: Advanced the QMP click correlation floor from restore press to the
  already-proven restore release sequence. This prevents an intervening
  same-window press from being spliced with the later real MouseDown/content
  mutation. Shell syntax and the direct positive/negative source invariant
  pass. The long fullscreen SSpec hit its known 120-second file ceiling at
  0/1 and was not rerun; docgen still produced one complete manual with zero
  stubs. No live QEMU claim is made.
- bugfix: Made WM pointer-state receipts use the authoritative hit-tested
  pending window ID captured with the IRQ instead of synthesizing identity from
  the currently focused surface after routing. Misrouted/off-window releases
  can no longer masquerade as browser-window releases. The smaller browser
  staging SSpec passes 1/1 after correcting literal-brace interpolation, and
  docgen produced one complete manual with zero stubs. The unrelated existing
  conflict hunk in `src/os/desktop/shell.spl` was then semantically resolved:
  queued input still bypasses the idle `continue`, while idle iterations retain
  bounded remote bootstrap/event polling and define `ps2_byte_ready` for the
  subsequent decode. Source/diff checks pass. A stale 7.3 MB `.git/index.lock`
  with no owning Git/jj process was removed; jj now reports nine other
  unresolved paths, with `shell.spl` no longer among them.
- sync: Resolved the remaining nine Vulkan/Metal/render-evidence conflicts.
  Removed four orphaned macOS micro-probe specs/manuals whose producer and
  checker no longer exist; retained the current Linux Vulkan injection plan,
  typed macOS backend-failure spec, and ProcessingIR readback parity spec;
  merged dated WM evidence history; and preserved the colliding no-stub runtime
  task as unique TODO 588 while keeping TODOs 585-587 stable. The two retained
  focused specs pass 5/5 each. Their manuals are complete with zero stubs,
  conflict markers/diff checks pass, and `doc/06_spec` contains zero executable
  `_spec.spl` files. A typo-generated stub manual was deleted before the correct
  manual was regenerated.
- bugfix: Bound the WM apply receipt to the exact correlated pointer sequence.
  The shell now stores `remote_event_input_seq` when arming the browser event,
  emits it with the first authorized same-window `update_tree`, and clears it
  on consume; the QEMU harness requires `input_seq=pointer_seq` in that marker.
  This prevents a valid press from being spliced with an unrelated later
  same-window repaint. Shell syntax and the focused staging SSpec pass 1/1;
  docgen produced one complete manual with zero stubs. Live QEMU framebuffer
  evidence remains under TODO 585.
- bugfix: Turned browser content apply into a real frame-completion barrier.
  The shell now renders first and emits
  `remote-browser-content-presented` only for a positive generation, carrying
  the exact window and pointer sequence. Python waits for that exact ordered
  marker before release/capture and exports the generation; the live system
  SSpec requires the same sequence and positive generation. Shell syntax and
  the focused staging SSpec pass 1/1; both refreshed manuals are complete with
  zero stubs. The live QEMU scenario was not rerun under the existing cap.
- bugfix: Closed release-receipt replay after the content-presented barrier.
  The harness records the serial offset immediately before QMP button-up and
  searches IRQ/state/frame receipts only in that post-submission slice while
  still requiring `seq > pointer_seq` and the authoritative target window.
  Shell syntax and the runnable staging contract pass 1/1; both refreshed
  manuals are complete with zero stubs. The capped long source/live scenario
  was not rerun.
- bugfix: Bound final Engine2D content provenance to the exact presented frame
  generation. The wrapper validates the parsed generation as positive and
  requires the full `content-presented` receipt to match that scene revision,
  browser window, theme/source, backend path, and material hash; the previous
  any-positive-revision regex is rejected. Shell syntax and the runnable
  staging contract pass 1/1. All three affected manuals are complete with zero
  stubs; capped source/live QEMU scenarios were not rerun.
- bugfix: Bound the browser framebuffer artifact to that same presented
  generation. `pmemsave` now runs immediately after the presented barrier and
  before button-up/release handling; the crop/hash delta receipt carries the
  generation, outer admission requires it to equal the presented generation,
  and the live SSpec requires both statuses. Shell syntax and the runnable
  staging contract pass 1/1; both refreshed manuals are complete with zero
  stubs. Live QEMU remains capped and unclaimed.
- bugfix: Closed the shared `display_input` classifier's partial-receipt
  admission. It now requires all 13 live-wrapper receipts: overall/input/
  semantic/text pass, screen origin, positive event and WM target IDs, exact
  `host-proof`, one callback and mutation, replay rejection, frame marker, and
  frame correlation. The reproduce-first diagnostic run failed 12/13 before
  the owner fix and passed 13/13 afterward. Docgen produced one complete
  operator manual with zero stubs. The runner was the diagnostic repair CLI,
  so accepted pure-Simple qualification and fresh live screen/QEMU evidence
  remain open.
- bugfix: Closed the Linux Vulkan aggregate's Simple RenderDoc magic-only
  admission. A claimed Simple capture now also requires replay PASS and owner/
  capture-frame agreement; the aggregate exposes both rows and blocks
  `renderdoc-simple-rdc` when either is absent. The final allowed focused run
  passed 14/14 after adding the missing ARGB viewport rows only to the valid
  main-browser fixture. Docgen produced one complete manual with zero stubs.
  This is diagnostic-runner contract evidence; a fresh native `.rdc` remains
  required for live completion.
- bugfix: Reframed the HTML and widget goal specs so magic-only Simple `.rdc`
  fixtures remain blockers even when Chrome/Electron fixture rows pass. The
  capped diagnostic runs ended at HTML 3/4 and widget 4/6; retained-output
  comparison aligned the remaining expected property count and blocker text,
  but those edits were not rerun and no green qualification is claimed. Both
  manuals were regenerated with zero stubs.
- verify-gap: A foreign session still owns the active fullscreen/QEMU rebuild,
  so no competing VM/build was launched. There is still no source-matched
  accepted pure-Simple full CLI or measured coverage artifact; the broader GUI
  feature-coverage spec also retains synthetic-completion scenarios for a
  later uncapped environment.
- bugfix: Closed the broader GUI aggregate's stale nested-gate cache and
  synthetic-completion expectations. HTML and widget RenderDoc admission now
  rerun instead of reusing an older pass after gate/replay/capture changes; the
  focused fixture confirms `capture-not-active-before-end`, two HTML blockers,
  and final `missing-simple-widget-renderdoc`. The full broad spec reached its
  120-second resource ceiling at 0/1, so no suite PASS is claimed. Docgen
  produced one 184-line manual with zero stubs; the contradictory legacy
  duplicate manual was removed.
- verify-gap: The completed fullscreen QEMU artifact reached 3840x2160 but
  failed `guest-render-fault`: three CPU-material witnesses retained the
  contract attributes while returned `Style` entries lost background/backdrop
  fields, yielding `fallback=none material=` and rejecting every WM frame.
  The source-matched artifact was already stale, and a new foreign wrapper run
  now owns the VM/build. Do not rerun or edit that source lane concurrently;
  the next owner fix is the existing freestanding-safe style material side
  channel, followed by its focused material/frame specs and one QEMU resume.
  Accepted-current full CLI coverage artifacts remain absent.
- bugfix: Moved WM Web material witness construction to the existing
  freestanding-safe loop-local style boundary. CPU-composited and solid
  canonical entries now cross as two text slots plus proven mutable `i64`
  counts; the two draw-IR/software consumers hash those entries after the
  unsafe `[Style]` boundary. The byte-exact backdrop grammar is shared by
  witness and Draw IR, and animated material fails closed until a
  post-animation channel exists. Architecture, SimpleOS Web WM guide, focused
  specs, and their canonical manuals were refreshed; two stale duplicate
  manuals were removed.
- verify-gap: The focused test runner failed before execution because the
  diagnostic CLI lacks its required `simple_seed` sibling. Direct interpreter
  execution then reproduced the known 10-second web budget expiry, and the one
  budget-raised retry reached the scenario but hit the 240-second cap. The
  three-cycle limit is exhausted: source compiles and the regression remains
  unqualified. Do not rerun this fixture in this session; resume with the
  accepted-current pure-Simple CLI or one post-fix QEMU run after source/build
  ownership is clear.
- verify-gap: The one changed-file lint attempt also delegated through the
  missing seed sibling and then failed inside the diagnostic lint stack with
  `method get not found on type str (receiver value: HNode)`. Direct-runtime
  guards and diff/layout checks remain usable, but lint is not claimed.
- bugfix: Made the hosted WM's physical framebuffer commit fail closed after
  both full live-frame and motion-only rendering. A failed winit pixel present
  now stops the loop before warmup or evidence capture can claim that frame;
  the focused SSpec pins both guarded paths without a middle mock. Its generated
  manual is complete with zero stubs. The one diagnostic interpreter run
  reached the test loop but timed out at 120 seconds before any scenario
  result, so accepted pure-Simple qualification remains open.
- bugfix: Bound screen-input admission to an actual framebuffer mutation. The
  Linux live wrapper now requires the input Engine2D checksum and retained
  capture SHA to both differ from baseline before frame correlation can pass.
  The existing SSpec pins both inequalities and no middle mock was added. Its
  stale interpolating source needle was also corrected so `comp` is no longer
  parsed as a test variable. Shell syntax and the wrapper self-test pass, and
  docgen produced one complete manual with zero stubs. The diagnostic SSpec
  runner remains unqualified: after the parser fix it failed only because its
  required `/usr/bin/simple_seed` sibling is absent.
- bugfix: Closed the cross-architecture SIMD frame-ownership false-green. Four
  small read-only lanes audited the producer, classifier, host rows, and docs;
  the shared fix restores the tracked canonical evidence source, hashes that
  source and the selected Simple compiler, recomputes an architecture/feature/
  diagram-checksum receipt, and rejects matrix arch/path/hash splices. Target C
  binaries can no longer override missing Simple-rendered frames. The common
  classifier now requires positive/equal fill, copy, alpha, alpha-edge, scroll,
  and diagram checksums plus native hits and no-middle facade evidence for x86,
  ARM, and RISC-V. `test_host_env` consumes exact ARM/RISC-V child receipts and
  no longer passes from `native_simd_pixel_evidence` or matrix substrings.
  Focused contract tests pass 13/13 and app source tests pass 1/1; the producer/
  matrix system contract reached 2/3, with only the diagnostic runner's known
  missing `/usr/bin/simple_seed` failure in its intentional forbidden-seed
  subprocess. Shell syntax passes and docgen produced five complete manuals
  with zero stubs. Live native/QEMU frame evidence was not rerun.
- bugfix: Closed the Simple RenderDoc metadata false-green. Four small
  read-only audit lanes reviewed replay identity, rendering performance,
  coverage, and live-capture gaps; the selected root fix now counts Vulkan
  actions and resources only from RenderDoc `<chunk name=...>` records, so
  metadata text cannot fabricate replay evidence. Focused unit tests pass 7/7,
  the no-GPU system contract passes 5/5, and docgen produced two complete
  manuals with zero stubs. Live GPU/QEMU capture evidence was not rerun.
- bugfix: Closed the hosted framebuffer readback identity false-green found by
  the parallel readback audit. The shared classifier now reuses the complete
  screen-to-WM semantic receipt and requires exact glyph hashes, changed
  baseline/input revisions, frame checksums, and capture hashes, stable backend
  and handle identity, and device readback for both frames. The focused unit
  suite passes 13/13; docgen updated the unit and umbrella system manuals with
  zero stubs. The umbrella live-host scenario was not rerun because its native
  display/GPU receipts are environment-owned.
- bugfix: Closed retained-frame percentile fabrication found by the parallel
  performance audit. The 4K/8K wrapper now consumes the producer's post-warmup
  p50/p95 and exact sample count instead of copying the average, and the
  aggregate no longer fills missing percentiles from average timing. Shell
  syntax and plan-only evidence pass; the existing modern SSpec pins the real
  producer/wrapper/aggregate flow and docgen reports one complete manual with
  zero stubs. The capped live 4K/8K environment suite was not rerun.
- coverage: Restored the lost host-evidence coverage blocker as collision-free
  TODO589 after auditing recent `todo_db.sdn` heads through TODO588, and mapped
  the existing SimpleOS evidence spec to the SIMD evidence owner at 100% intent.
  Host classification remains behaviorally green at 13/13. The isolated
  SimpleOS spec did not execute because the diagnostic runtime attempted the
  absent `/usr/bin/simple_seed`; no SimpleOS PASS or decision percentage is
  claimed. TODO589 records the accepted-runtime commands, separate artifact
  preservation, and >=98% per-owner decision threshold.
- perf: Closed the retained-tail-latency false-green found by the second small
  audit wave. The wrapper now derives a 5,000,000 ns frame budget at the
  selected 200 fps target, emits it, and rejects measured p95 above that bound;
  the aggregate independently derives and enforces the same 4K/8K budget.
  Average FPS can no longer hide a slow tail. Wrapper shell syntax, aggregate
  shell/Python syntax, and 4K plan-only budget evidence pass. The modern SSpec
  and complete manual pin both consumers; capped live perf runs were not rerun.
- coverage-infra: Restored the existing coverage lifecycle in both runner
  entrypoints and routed all three extracted child payloads into the shared
  aggregator. Coverage requests now bypass fork mode because its result path
  cannot return those payloads. A focused regression merges opposite child outcomes and checks
  both file and aggregate decision totals at 100%. Its diagnostic run timed
  out after 90 seconds before a result, and docgen hit the unavailable seed
  path, so manuals were synchronized directly and no PASS or percentage is
  claimed. TODO589 retains the accepted-runtime resume commands.
- readback-identity: Bound the latest semantic event and mutation revision to
  the successful full-frame presentation, serialized both under `render`, and
  required the retained input snapshot, acknowledgment, emitted environment,
  and host classifier to agree with the screen receipt. Two mismatch negatives
  and the modern system contract fail closed on a bridged unrelated receipt.
- simple-renderdoc-identity: Reused RenderDoc's capture-path template to embed
  the owner frame nonce in the actual regular RDC filename. The capture helper
  now accepts exactly one matching artifact, the gate requires template setup
  and path agreement, and the host classifier requires the emitted identity
  status. Equal echoed IDs paired with a different frame path fail closed.
- vulkan-aggregate: Closed a host-env false-green that trusted producer PASS
  labels without consuming the retained framebuffer oracle. Vulkan admission
  now requires positive clear/rect pixel counts, exact expected/actual
  checksums, zero mismatches, stable device identity, no tolerance, and the
  CPU/Vulkan parity exit in addition to strict device-origin provenance.
- simd-origin: Replaced the coordinator-architecture proxy with receipt-owned
  execution provenance. The producer compares shell and executed architectures,
  binds `native_host` or `emulated` into the frame hash, and the aggregate
  accepts retained native ARM/RISC-V receipts from any coordinator while
  keeping emulated receipts blocked.
- render-matrices: Removed both unconditional integration fail helpers. The
  provenance matrix now exercises real strict/translated Engine2D facade paths,
  and the surface matrix retains a frozen 4x3 absolute oracle across 100 real
  CPU Engine2D present/readback frames. Separate physical/software Vulkan ICD
  qualification remains in the external-host TODO rather than being fabricated
  inside one process.
