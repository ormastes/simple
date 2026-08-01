# macOS Vulkan/Metal and SimpleOS QEMU Rendering Completion

Updated: 2026-08-01

## 2026-07-27 Stage 3 admission attempt

- The existing clean-worktree bootstrap at commit `98082021c3` completed
  Stage 2 and Stage 3 native compilation with 687 files, zero compile
  failures, and a passing Stage 3 sanity receipt.
- It did **not** emit the required adjacent `provenance.env`. The 128 MB
  Stage 3 binary is therefore untrusted and must not be selected by the
  macOS GPU builder or used to claim live evidence.
- Post-run admission inspection found the producer's original seed,
  `libsimple_native_all.a`, and seed input stamp absent from
  `src/compiler_rust/target/bootstrap`, while their private Stage 2 runtime
  snapshot remained. The manifest writer correctly rejects a missing original
  authority input; this was a concurrent authority-lifecycle failure, not a
  Stage 2/3 compile or sanity failure.
- The source snapshot is also behind the current GitHub revision, including
  later compiler, browser, WM, and GPU-evidence changes. Do not backfill or
  synthesize provenance. Diagnose the producer-side manifest failure, then
  run one clean current-source Stage 3 admission before Vulkan 2D.

## 2026-07-27 Authoritative Status and Remaining Work

This checkpoint supersedes stale status wording in the historical notes below.
The overall goal remains **FAIL / INCOMPLETE**. No current-revision,
manifest-bound Vulkan 2D live PASS exists, so no downstream lane may be marked
complete from source review, retained diagnostics, CPU mirrors, or unretained
peer reports.

### External bootstrap note (2026-08-01)

- The bootstrap Stage 3 source-admission process is currently running in a separate
  agent session (`/root/bootstrap_early_exit_diagnosis`) and is progressing through
  Stage 2/3 snapshot generation. To avoid duplicate and conflicting builds, this
  session is not rerunning bootstrap.
- As of this session, the bootstrap process reported that the Stage-2 portion is
  active and progressing; the host lane will continue with non-bootstrap evidence
  tasks only until a shared, manifest-bound trusted Stage 3 arrives.
- Non-bootstrap work will proceed in order on this lane while bootstrap is active:
  manifest-bound Vulkan 2D evidence → Vulkan web/gui/host WM → Metal → QEMU.

### 2026-08-01 evidence status (non-bootstrap work)

- Added evidence artifacts for:
  - `doc/09_report/macos_vulkan_web_live_evidence_2026-08-01.md`
  - `doc/09_report/macos_vulkan_gui_widget_live_evidence_2026-08-01.md`
  - `doc/09_report/hosted_wm_capture_evidence_2026-08-01.md`
- Current failure pattern in hosted WM evidence is stable and non-actionable from this
  lane: the selected runtime still reports `runtime-rust-seed-forbidden` and
  local-raster fallback for capture readback.
- The ordered lane remains unchanged: Vulkan/Metal 2D and web/GUI are blocked on
  manifest-bound vector-font 300-DPI runtime evidence; QEMU remains blocked by those
  upstream dependencies.

### 2026-08-01 incremental host-gate checkpoint

- The Vulkan readback gate reached source execution but failed fail-closed because
  the deployed pure-Simple binary predates `rt_is_interpreter_runtime`; its source
  declaration and both hosted runtime implementations exist, but the deployed
  binary exports neither symbol. This is a stale deployment/linkage blocker, not
  Vulkan evidence or a renderer-source defect.
- The supported repair is the incremental dynload Stage2/Stage3/Stage4 redeploy
  with provenance, not an ad-hoc native-build and not a Rust-seed tool fallback.
  A separate bootstrap/redeploy owner is already active, so this lane must wait
  for its admitted artifact rather than duplicate the build.
- Metal host prerequisites are present (Apple Metal toolchain), but its canonical
  build refuses to run until the same manifest-bound Stage3 artifact exists.

### Render design / IR alignment addendum (2026-08-01)

- DrawIR/GPU design control changed in the local branch and is now the source
  baseline for this lane:
  - `doc/04_architecture/ui/gpu_web_scene_ports.md`
  - `doc/05_design/ui/gpu_web_scene_contracts.md`
  - `doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn`
  - `doc/03_plan/ui/unified_2d_engine/drawir_feature_gap_2026-07-31.md`
- The `src/compiler/50.mir/_MirLowering/module_lowering.spl` stabilization is a
  build-integrity change (module-init lowering/name determinism) and does not
  replace missing Vulkan/Metal runtime evidence.
- Keep `gpu_web_scene` and DrawIR-v3 C0 contract files read-only unless a schema
  bump is performed with an explicit version bump plan.

### Current design/IR contract check (2026-08-01)

- Reviewed the live IR and rendering design artifacts:
  - `doc/04_architecture/ui/gpu_web_scene_ports.md`
  - `doc/05_design/ui/gpu_web_scene_contracts.md`
  - `doc/03_plan/ui/unified_2d_engine/drawir_feature_gap_2026-07-31.md`
  - `src/lib/common/ui/draw_ir_v3_execution_route.spl`
  - `src/lib/common/ui/draw_ir_v3_ports.spl`
  - `src/lib/common/ui/gpu_web_ports.spl`
- These changes are already reflected in the branch and do not require edits to
  runtime evidence lanes yet; they mainly tighten schema/route semantics and
  fallback accounting.
- Plan impact:
  - Do not apply any additional `gpu_web`/DrawIR contract edits in this lane
    unless a schema-bump plan is created and approved.
  - Vulkan/Metal/host WM execution work must continue to treat route/classification
    evidence (`GPU_ROUTE_*`, `DrawIrV3ExecutionRoute`) as hard requirements, not
    optional diagnostics.
  - The canonical text path remains `DrawIrComposition` →
    `Engine2D.draw_text` → transient `FontRenderer`/`FontRenderBatch` material.
    Atlas/cache state must not enter Draw IR, and this lane must not add a
    private parallel font draw path.
  - Strict Vulkan/Metal web acceptance must retain the DrawIR-v3 execution
    profile, requested and executed modes, route, reason code, fallback level,
    `accepted`, `strict_pass`, and deterministic hash. Full-offload evidence
    requires `GPU_ROUTE_GPU`, reason `NONE`, and `strict_pass=true`.
    `CPU_SELECTED` is policy evidence only; `GPU_FALLBACK` is a failure and
    must retain a denial reason in the 200–299 range.
  - Web events must prove one sealed/coalesced input batch per epoch with scene
    generation and sequence, CPU/GPU mutation-journal byte parity, one epoch
    receipt, and explicit host-effect, fault, and overflow receipts. Production
    evidence uses checksums/hashes; any pixel capture must be labeled
    test/shadow readback.
  - Do not use a WM child-web capture as Vulkan/Metal evidence when its bridge
    selected `cpu_simd` or dropped backend forwarding. The standalone selected-
    backend web and GUI gates remain mandatory before the host-WM gate.
  - `draw_ir_v3_execution_route.spl` is a CPU-reference contract, not proof of
    a live GPU backend. Capacity-overflow acceptance remains pending until the
    frozen capacity-manifest parser defect is repaired and a real
    `GpuOverflowReceipt(bound, requested, limit)` is wired. This requires an
    explicit schema-version plan; do not edit C0 contracts in this lane.

The latest bounded producer work is recorded in cycles 25–27 below and
supersedes the older diagnostic summaries. Parsing, cmap, tables, metrics,
and outline geometry remain localized. A focused cross-module native fixture
now proves that caller-owned `[i64]`/`[u8]` arrays survive both scalar and
32-byte aggregate-return calls on Cranelift and LLVM, disproving the prior
mutable-slice-lifetime diagnosis. The remaining failure is inside the selected
SFNT measure publication: the isolated Bungee into-probe exits before the
measure cookie, and the fail-closed producer stops at
`fail-glyph-bitmap-return`. No cycle-25–27 font integration is accepted as a
fix.

### Verified current state

- Source parser, runtime-owned ordered-event correlation, and 300-DPI receipt
  hardening are done and integrated. These source/contract results are not a
  Vulkan live PASS.
- Three bounded current-source native diagnostics ran without bootstrapping.
  Cycle 1 compiled 185 modules with zero compile failures in approximately
  9.9 seconds, but its standard output was empty. Cycle 2 compiled 184 modules
  in 10.2 seconds; its entry and receipt sentinels succeeded and it selected
  the exact Bungee face at 100 px.
- Cycle 2 could not produce trustworthy producer-state evidence: layout,
  raster, local, inbound, staged, stage-return, and alpha scalar checkpoints
  serialized as empty, while `post_engine_fonts` and
  `post_install_retrieve` reported the nil sentinel
  `2305843009213693951` (`0x1fffffffffffffff`).
- Cycle 3 started from `bb9a9b60edcc572e86555e8c929bfabc20b74a62`
  and used explicitly initialized scalar fields plus individual direct-owner
  `i64` getters. Its no-bootstrap build compiled 184 modules with zero failures
  and linked a 654 KB binary with SHA-256
  `8460a54790068788b5c4997b59ad0d04ed73e863f5d281a48f7d34a7f3f1164a`.
  The run exited 132 with `runtime error: field access on nil receiver` before
  any checkpoint output.
- All Cycle 3 diagnostic edits were reverted. The binary hash is an exact
  failed-diagnostic receipt, not a manifest binding or Vulkan live evidence.
  The three-cycle cap is exhausted, so there will be no retry, bootstrap,
  source fix, or live gate in this session.
- The zero-quad cause therefore remains unproven. The leading suspected seam is
  `local quads -> FontRenderBatch.quads -> _stage_batch`, but a layout or
  raster failure remains possible. Native scalar diagnostic corruption is the
  active blocker; no renderer fix or live evidence resulted.
- The diagnostic path
  `/private/tmp/simple-font-zero-quads-evidence-448d2a5` is ephemeral. This
  tracked summary records the observations without claiming retained artifact
  provenance.
- A retained pure-Simple Stage3 artifact can diagnose source, but its provenance
  is bound to an older revision. It cannot authenticate the current `main`.
  A canonical bootstrap may be run later only if essential or required by the
  production builder, and only after the focused current-source producer
  passes.
- Exact runtime-owned key/text origin correlation was high-capability reviewed
  and pushed to `main` as `d00e71c11d`. Live ordered-event evidence remains
  required; the accepted source change is not a Vulkan event PASS.
- The 300-DPI receipt hardening was high-capability reviewed and integrated as
  contract enforcement. It is not accepted live evidence or a substitute for
  the canonical live vector-font gate.
- QEMU SimpleOS/WM PASS claims remain unsupported: no retained canonical live
  receipt proves guest framebuffer, input, SIMD, ARM, and artifact identity.
  Treat the affected matrix cell and the goal as FAIL until such evidence is
  generated and retained.
- Vulkan web/GUI/host-WM, all Metal parity work, and x86/ARM QEMU acceptance
  remain pending behind the Vulkan 2D gate.

### Ordered remaining tasks

1. In a fresh session, add monotonic fixed-slot phase stamps inside
   `_sfnt_glyf_measure_query_into`: entry, blob/size validation, offset-table
   parse, cmap/glyph selection, intra-module raster result, and final metadata
   publication. Run the isolated Bungee into-probe once; do not repeat cycles
   25–27 unchanged.
2. Fix only the phase identified by that probe, then run one focused
   current-source producer check and require exact Bungee
   24 pt at 300 DPI = 100 px, plan admission, positive staged quads, atlas ROI
   alpha, cold rasterizations, warm zero rasterizations plus positive hits,
   stable identity, and CPU producer execution.
3. If the producer fails, distinguish cache write-back from
   `local quads -> FontRenderBatch.quads -> _stage_batch` with the existing
   boolean receipts; stop after the bounded cycle rather than broad retries.
4. After that focused producer PASS, produce one canonical, manifest-attested
   pure-Simple Stage3 only if required by the production builder. Do not use
   the Rust seed as normal tooling and do not synthesize or reuse stale
   provenance.
5. Build and run the manifest-bound Vulkan 2D gate. Require MoltenVK identity,
   positive backend/device handles, same-frame device readback, semantic
   pixels, durable capture, canonical `FontRenderer` vector text at 300 DPI,
   cold/warm font-cache receipts, and ordered focus/pointer/key/text events.
6. Validate the accepted runtime-owned key/text origin correlation from
   `d00e71c11d` in the live gate and prove ordered delivery without a synthetic
   shortcut.
7. Run Vulkan web, then Vulkan widget GUI, then host-WM live gates. Each must
   preserve Draw IR ownership, use real device output, and retain capture and
   event receipts; GUI must repeat the vector-font proof at 300 DPI.
8. Only after all Vulkan host lanes pass, run like-for-like Metal
   2D/web/GUI/host-WM gates and require pixel/event/font parity without a CPU
   mirror.
9. Only after host-WM passes, run x86 QEMU SimpleOS 2D/SIMD, ARM QEMU
   SimpleOS 2D/SIMD, and QEMU WM. Retain canonical artifact hashes, guest
   framebuffer dimensions/bounds, input receipts, runtime SIMD receipts, and
   captures. Correct any unsupported PASS documentation before acceptance.
10. Run the scoped verification/audit gates once, obtain `STATUS: PASS`, then
   linearly sync and push the isolated verified changes.
11. Before accepting any new web/render/IR work on this lane, ensure C0 contract
   scope and schema versioning constraints are enforced in source and plan.

### Agent lanes and acceptance ownership

| Lane | Sidecar task | Merge owner | Final reviewer |
|---|---|---|---|
| Typed scalar diagnostic | Establish a trustworthy typed checkpoint and localize producer vs staging failure | Primary rendering agent | Highest-capability primary reviewer |
| Focused Draw IR/font producer | After typed diagnostics are trustworthy, prove positive quads and non-nil renderer state | Primary rendering agent | Highest-capability primary reviewer |
| Vulkan 2D + ordered events | Produce manifest-bound live render/readback/font/event evidence | Primary rendering agent | Highest-capability primary reviewer |
| Vulkan web/GUI/host-WM | Run sequentially after Vulkan 2D PASS; parallel source-only preparation is allowed | Primary rendering agent | Highest-capability primary reviewer |
| Metal parity | Prepare source/contracts only until Vulkan host PASS, then run parity gates | Existing local comparison agent; primary integrates only committed isolated work | Highest-capability primary reviewer |
| x86/ARM QEMU + WM | Audit contracts/evidence in parallel; live acceptance follows host-WM PASS | Primary rendering agent | Highest-capability primary reviewer |
| Documentation/evidence audit | Remove unsupported PASS claims and bind reports to retained artifacts | Primary rendering agent | Highest-capability primary reviewer |
| Contract control / DrawIR design | Enforce C0 freeze rules and route/fallback contract adherence while this lane is active | C0 contract owner + primary rendering merge owner | Highest-capability primary reviewer |

Parallel agents may prepare independent source/contracts and audit retained
evidence, but the live acceptance order is strict: Vulkan 2D → Vulkan web →
Vulkan GUI → host WM → Metal parity → QEMU. Merge only isolated, reviewed
commits; never absorb another agent's unrelated dirty files.

## 2026-07-25 Live iteration notes

- Implemented: `scripts/gui/macos-gui-run.shs` now resolves the GUI driver using:
  - explicit `SIMPLE_GUI_BINARY` and `SIMPLE_BIN` overrides when present,
  - preferred self-hosted candidates (`bin/simple`, `bin/release/*/simple`, `release/*/simple`, `build/bootstrap/stage3/simple`),
  - optional rust-driver compatibility fallback when `SIMPLE_GUI_ALLOW_RUST_DRIVER=1`,
  - explicit errors when an override is non-executable, non-WINIT, or rust-seed in strict mode.
- Remains:
  - verify Vulkan and Metal 4K/300-DPI live 2D evidence and GUI widget/web 300-DPI vector-font paths on macOS.
  - re-run native-process-lifecycle checks (`launched-process-missing`, PID identity, event sequence, font cache transitions).
  - refresh SimpleOS QEMU ARM SIMD rendering evidence after host lanes close.

### 2026-07-25 Current Vulkan 2D checkpoint

#### Runtime gate and final bounded diagnostic

- Fixed Engine2D backend option ownership: Vulkan and Metal constructors and
  writebacks now store `Some(backend)` consistently and initialize all
  optional/font state explicitly.
- Replaced the invalid eager Simple mutex used by Vulkan dependency quarantine
  with a dedicated runtime-owned static gate. Rust native, interpreter, runtime
  symbol registration, and core-C parity are implemented and high-capability
  review accepted the ABI, lock balance, and deadlock separation from Vulkan
  `STATE`.
- The Vulkan runtime provider and a pure-Stage3 diagnostic closure rebuilt
  successfully with the new gate symbols. This is diagnostic build evidence,
  not canonical Stage3 provenance attestation.
- The third and final live launch ran exactly once and then stopped under the
  mandatory cycle cap. It advanced beyond both earlier nil-receiver failures,
  then crashed at a null call target from `Engine2D.draw_gradient_rect` before
  render-ready. No receipt, window, capture, ordered events, device-readback,
  vector-font cache, or 300-DPI evidence was produced. Diagnostic artifacts:
  `build/tmp/macos_vulkan_2d_runtime_gate_diagnostic_20260725/`.
- Next session: diagnose the gradient dispatch target without relaunching,
  implement one scoped repair, rebuild from an accepted Stage3 artifact, then
  permit one bounded Vulkan 2D live launch. Web/GUI/WM, Metal, and QEMU remain
  gated until that launch passes.

- GitHub `main` now contains provider checkpoint `c103e8ad001e` and shared
  dimension checkpoint `5dbb483e7440`.
- The hosted provider is built with Cargo features
  `runtime-symbol-table,vulkan`; both macOS runtime dylibs use stable `@rpath`
  identities. A fresh pure-Stage3 closure advanced past the earlier
  `availability` rejection.
- The third and final bounded launch for this session reached Vulkan backend
  creation and failed with `Vulkan framebuffer dimensions are invalid`.
  Disassembly showed that the imported module-global 3840x2160 aliases were
  emitted in BSS and never initialized. The shared Vulkan/Metal harness now
  uses function-local literal-backed 3840x2160 dimensions throughout creation,
  probes, readback validation, capture, and receipts. The corrected closure
  compiles and links, and high-capability source review accepts the fix.
- The mandatory three-cycle guard is exhausted. Do not claim live success or
  relaunch in this session. A fresh scoped session must perform exactly one
  Vulkan 2D live launch from a newly attested canonical Stage3 build. Until
  that produces device readback, a real window/capture, ordered events, and
  300-DPI vector-font receipts, Vulkan web/GUI/WM, Metal, and QEMU live
  acceptance remain gated.
- QEMU ARM source attestation checkpoint `1b66b7f093b1` is on GitHub `main`.
  It validates the deployed compiler's native format/host architecture, forces
  kernel/disk/writer rebuilds, fingerprints disk/font inputs, and correlates a
  guest-owned RAMFB visual commit with QMP input/frame/capture evidence. This
  is reviewed source/manual infrastructure only; no QEMU live PASS was run.
- Stage3 provenance remains local and unpushed after the third review cycle.
  Remaining blockers are: the seed/native-all fingerprint omits the
  unconditional `src/runtime/hosted` Rust/Cargo path dependency; inherited
  environment records are discarded rather than exactly validated; and the
  self-test does not exercise seed tampering, frontend replay, transcript or
  canonical-path rejection, or private compiler/provenance freezing. Stop
  this lane for the session under the mandatory three-cycle guard.

- Host Vulkan installation is healthy: MoltenVK 1.4.1, Vulkan loader/tools
  1.4.350.1, validation layer 1.4.350, and Apple M4 device enumeration pass.
- The shared Vulkan/Metal live harness now:
  - renders one full-target 3840x2160 `DrawIrComposition` through the parent
    Engine2D, preserving the selected Bungee `FontRenderer`;
  - derives 100 physical pixels from 24 points at 300 DPI and embeds/verifies
    300x300 DPI PNG metadata;
  - maps the observed native winit focus event through
    `UIEvent.FocusEvent -> process_event -> UIState`, then derives the DrawIR
    action accent from that state;
  - records ordered pointer/key delivery separately without claiming an
    unimplemented UI-state reduction;
  - emits stage-specific failure receipts, exact provider hashes, repository
    revision, and a backend-independent shared-scene fingerprint.
- A fail-closed Vulkan/Metal aggregate now requires equal metadata, provider
  hashes, font metrics, DrawIR identity/count/readback, semantic mutation,
  ordered events, bounds, and raw PPM pixels with mismatch count 0, maximum
  channel delta 0, and tolerance 0. Behavioral tests cover semantic mismatch
  and evidence/output alias rejection.
- Native binaries are no longer admitted merely because they are under
  `build/`. `build-macos-gpu-2d-live-native.shs` must build the canonical
  output and atomically bind compiler, sources, providers, arguments, output,
  and hashes in a verified manifest.
- Current blocker: the canonical Vulkan native build resolved the earlier
  module-root error after moving the shared fixture beside the live harness,
  but both the cold and cached/four-thread builds exceeded the bounded
  180-second verification window without producing an output or manifest.
  The three-cycle cap is exhausted for this session. Therefore no current
  Vulkan device-readback/window/event PASS exists, and web/GUI/WM/Metal live
  lanes remain gated.
- Generated manuals for the new DrawIR fixture and parity contract/behavior
  specs remain pending. The available release binary identifies itself as a
  Rust bootstrap seed during `spipe-docgen`; its generated output was rejected
  and removed rather than accepted as pure-Simple verification evidence.

## Goal

Prove equivalent Simple 2D, web, GUI, vector-font, and event behavior through
Vulkan (MoltenVK) and Metal on macOS, then prove the applicable WM/2D behavior
on SimpleOS under QEMU. Evidence must include real backend initialization,
positive backend identity, device readback, semantic pixel checks, visible
capture, and keyboard/pointer/click delivery. Vector-font evidence must use the
canonical `FontRenderer` path and include the requested 300 DPI configuration.

## Checkpoint and Overall Status

- WIP checkpoint `84397f04ba` (`wip(rendering): checkpoint Vulkan host and WM
  fixes`) is pushed to `origin/main`. It is a recoverable checkpoint, not
  completion evidence.
- The later wrapper-hardening work is rebased in this isolated worktree and
  remains unverified.
- The strict host/QEMU 2D aggregate currently reports **FAIL**. Static source
  prerequisites and prior partial receipts do not substitute for live guest
  framebuffer, bounds, hash, SIMD-runtime, and input receipts.
- The overall goal remains **FAIL / INCOMPLETE**. Vulkan live web, GUI, 300 DPI,
  and host WM must pass before equivalent Metal checks; QEMU WM must follow a
  host-WM PASS.

## Authoritative Lane State

| Lane | State | Current evidence or blocker |
|---|---|---|
| macOS Vulkan environment | PASS | MoltenVK initializes on Apple M4 through `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`. |
| Vulkan vector pipeline creation | PASS (focused only) | A minimal provider probe initialized Vulkan and created the precompiled-SPIR-V pipeline on Apple M4. This does not prove live composite/capture/events. |
| Vulkan vector composite/readback | FIXED, NOT REVERIFIED | Descriptor bindings 0–2 and returned-byte readback are implemented; promoted device execution, fence completion, nonzero exact bytes, and oracle checksum parity still need one fresh proof. |
| Vulkan 2D render/events | FAIL — SAFE PIPELINE REFLECTION FIX NOT REVERIFIED | The Vulkan-enabled provider now compiles and exports raw pointer/length bridges for SPIR-V, push constants, upload, and download. Core-C now packs widened `[u8]` slots in thread-local storage, and the focused runtime/provider compile gates pass. A retained pure-Simple closure was relinked with Apple `ld_new`, the corrected core-C object, and the raw provider bridges. The strict live run advanced through shader-module creation but aborted inside the C `spirv-reflect` parser before a receipt or window. All eight Engine2D SPIR-V source blobs independently pass `spirv-val`, so `ComputePipeline` now derives set-0 storage bindings with a bounds-checked Rust SPIR-V instruction scan instead of the aborting parser. That final fix is formatted but not rebuilt/live-tested because the three-cycle cap is reached. No capture/events exist. |
| Vulkan web render/events | FAIL | No accepted live window/capture/event proof. Asset-root, stamped rerender, readback checksum, bounded failure, exact PID/window capture, and input checks are implemented. |
| Vulkan widget GUI/render/events | FAIL | Earlier 320×240/96 DPI device-frame and font-cache receipts ended before accepted window/event evidence. Exact PID/window capture, Retina backing-scale, checksum, and input fixes are present but unverified. |
| 300 DPI vector GUI | NOT PROVEN | Earlier 1200×900/300 DPI source interpretation exceeded about 1.5 GiB before window discovery. Provider-first `dlopen` reduced the smaller path's RSS, but no 300 DPI live PASS exists. |
| Metal host lanes | PENDING AFTER VULKAN | Do not infer Metal parity from Vulkan or CPU mirrors. Preserve and review the local 2D comparison lane separately. |
| Host WM | FAIL | Source and fail-closed wrapper fixes are present. The contract currently reaches 5/6 through a Rust seed; the negative artifact fixture must be made worktree-independent and live production evidence still needs a qualifying native artifact. |
| QEMU SimpleOS 2D/SIMD | FAIL | The strict aggregate is negative; live guest framebuffer, exact hashes/bounds, event delivery, and runtime SIMD receipts are missing or incomplete. |
| QEMU WM | NOT STARTED | Must follow a host-WM PASS. |

## Bootstrap State

The rendering gates are currently blocked on producing a qualifying full
self-hosted CLI/native artifact, not on the stale primitive-vtable diagnosis:

1. An older bootstrap run passed Stages 2 and 3.
2. Its Stage 4 one-binary build reached approximately **3.3 GiB RSS** and was
   terminated for OOM/resource safety. That path is not accepted as a PASS.
3. Dynload bootstrap cycles 1 and 2 stayed below **1 GiB RSS**, but both were
   blocked because the deployed Stage 3 compiler used stale vtable-owner logic
   and diagnosed primitive owner `i32` incorrectly.
4. The upstream source fix is commit `c120be52f7`
   (`fix(seed): primitive/generic vtable owners fall back to legacy
   module-prefix ownership`).
5. The refreshed Stage 3 compiler passed its sanity probe. Its SHA-256 is
   `35174afcc5aa1a3599f85b3455b77f9a8db538c42b34616ebbf342ffadd5cf17`.
6. Dynload cycle 3 passed the vtable failure and generated the full object
   closure under **1 GiB RSS**, then failed link with 220 unresolved hosted
   runtime symbols. The three-cycle dynload cap is exhausted for this session;
   do not repeat that full-CLI probe.

Do not treat the old Stage 2/3 PASS as proof that the current source or Stage 4
is deployable. Do not retry the 3.3 GiB one-binary path merely to reproduce the
same failure.

## Implemented but Unverified

- The macOS GUI launcher forwards repository asset roots and bounded
  backend/event evidence settings.
- Vulkan web examples rerender after stamped input and cross-check renderer and
  device-readback checksums.
- Web, widget-GUI, and host-WM live wrappers now fail closed, bound RSS/time,
  retain diagnostic output, and reject missing capture/input/device identity.
- Both macOS wrapper contract specs now exist:
  `macos_vulkan_web_live_evidence_contract_spec.spl` and
  `macos_vulkan_gui_widget_live_evidence_contract_spec.spl`. The earlier claim
  that the web spec was missing is stale. The new GUI spec and the hardened
  wrappers have not yet completed their required verification/manual refresh.
- Font probing opens the provider before loading the large font, preventing
  repeated boxed copies when a provider candidate is absent.
- The macOS Vulkan provider exposes storage-buffer bindings 0, 1, and 2 for the
  shared vector-font shader.
- Vulkan font readback uses the canonical returned-byte API.
- Host WM uses stable executor accessors, receiver-local window projection, and
  sequential JSON escaping; its evidence wrapper requires the intended native
  artifact and routed input.

## Exact Next Steps

### 2026-07-24 Safe-Reflection Checkpoint

- Replaced the aborting SPIR-V reflection path with bounded direct parsing and
  added set-zero, contiguous-binding, malformed-module, and raw-pointer guard
  coverage. Focused Rust results: 7 parser tests and 3 raw-ABI guard tests
  passed.
- Rebuilt and staged the Vulkan runtime provider; its build now fails closed
  unless all four raw Engine2D ABI symbols are exported.
- The strict pure-Simple 4K/300-DPI Vulkan launch advanced past the former
  `spirv-reflect` abort, but MoltenVK rejected the submitted shader with
  `SPIR-V to MSL conversion error: Currently no block to insert opcode.` The
  gate therefore remains FAIL (`launched-process-missing`); see
  `doc/09_report/macos_vulkan_2d_live_evidence_safe_reflect_2026-07-24.md`.
- Next isolate the exact submitted byte stream at the raw compile boundary and
  validate that captured stream with `spirv-val`/SPIRV-Cross. Do not proceed to
  Vulkan web/GUI/WM or Metal until this first live 2D gate passes.
- Follow-up capture isolated the failure to the eleventh compile call: the
  vector-font head/tail append loop corrupted raw iterated bytes at the generic
  tagged `array.push` boundary. The byte-array concat fix now emits the exact
  pinned 10,884-byte module and passes `spirv-val`. The next blocker is the
  freshly built closure: its default link omits explicit provider dependencies,
  and diagnostic provider injection traps in `VulkanBackend.clear` because the
  backend receiver is nil. Fix the source-root/module identity or native-link
  closure so the strict wrapper can launch an explicitly provider-linked
  binary; then rerun the live gate in a fresh bounded session.

1. In a fresh bounded verification session, run the focused
   `storage_binding_numbers` unit tests and rebuild the Vulkan-enabled runtime
   provider. Require the four raw Engine2D ABI exports. Build the pure-Simple
   `macos_vulkan_session_live_probe.spl` and strict harness with a compiler that
   includes the `nil.id` semantic-build fix; the currently deployed compiler
   cannot resolve a fresh closure. Require session status 0, nonempty device
   identity, and no `shader-*`/`pipeline-*` label. If `ld_classic` stalls,
   relink retained objects with Apple `ld_new` plus the Command Line Tools SDK;
   do not use dynamic-lookup. Separately replace the unconditional
   `-ld_classic` compiler policy with a tested current-linker option. Do not
   rebuild again in the current session: all three targeted cycles have been
   consumed.
2. Launch Vulkan 2D first. Require a real MoltenVK device, positive handle,
   same-frame device readback, durable before/after capture, vector-font
   identity at 300 DPI, and ordered focus/pointer/key receipts.
3. Verify the hardened web, widget-GUI, and WM contract specs once and generate
   or refresh their mirrored manuals. Require real assertions and zero
   placeholder passes.
4. Run the focused Vulkan font composite/readback proof once. Require promoted
   Vulkan execution, fence completion, positive backend handle, nonzero exact
   readback bytes, and matching device/oracle checksums.
5. Run Vulkan web and widget-GUI live gates. Require visible capture plus focus,
   keyboard/text, pointer, and click receipts. Then repeat widget GUI at
   300 DPI with the selected vector-font identity and cold/warm cache receipts.
6. Run the host-WM production fullscreen gate and require the native artifact,
   semantic capture, taskbar/window evidence, and routed input.
7. Only after Vulkan passes, run equivalent Metal 2D/web/GUI/WM rendering and
   event gates and review the existing local agent's 2D comparison commit
   without absorbing its uncommitted work.
8. Run the strict QEMU SimpleOS 2D/SIMD aggregate until it has real guest
   framebuffer, dimensions/bounds, exact hashes, input delivery, and runtime
   SIMD receipts. Then run QEMU WM after host WM passes.
9. Run rendering coupling, direct-runtime, numbered-artifact, spec-layout,
    compiler/core/lib/MCP/LSP, and scoped production verification gates.
    `STATUS: PASS` is required before a completion commit or release.
10. Commit only the isolated verified lane, fetch/rebase linearly onto
    `main@origin`, apply the file-count guard, set `main`, and push.

### 2026-07-25 Pure-Compiler and Evidence Checkpoint

- MoltenVK and the macOS Vulkan loader remain installed and enumerate Apple M4.
- Pushed `e1950d5fff9f`: batched deterministic source attestation plus bounded
  native-build diagnostics.
- Pushed `fab839240d9e`: Vulkan-web raw focus/blur reduction, strict event
  revision ordering, and post-render 24pt-at-300-DPI Bungee batch evidence.
  This is a reviewed source checkpoint, not a live Vulkan PASS. The final
  contract run stopped at 9/10 for a stale source-text assertion; that exact
  assertion was corrected without another run because the three-cycle cap was
  reached.
- The deployed `bin/simple` still identifies itself as Rust-seed-backed for
  normal commands. An isolated clean normal bootstrap refused stale
  seed/backfill inputs. Another local lane produced a pure-Simple Stage 3
  compiler, while its full Stage 4 CLI build was killed during the 547 KiB
  `src/app/ui.web/html.spl` parse after roughly 263 seconds.
- The pure-Simple Stage 3 compiler built the Vulkan 2D harness closure
  successfully: 211/211 modules, then a cached rebuild linked in 11.4 seconds.
  The decisive link fix was to omit `--runtime-path build/sffi`; that override
  prevented `--runtime-bundle core-c-bootstrap` from adding the required
  `runtime_native` archive. The resulting binary is diagnostic only because
  the Stage 3 compiler lacks a canonical bootstrap provenance manifest and the
  production builder still admits only the deployed release compiler.
- The canonical bootstrap now produces
  `build/wm-to-i64-bootstrap/stage3/<platform>/provenance.env` only after
  identical pre/post snapshots of every `.spl` file under `src/compiler`,
  `src/app`, and `src/lib`. The manifest binds the seed input stamp, seed,
  native-all archive, optional compiler backfill, Stage 2 producer, both exact
  staged command digests and logs, bootstrap/provenance helper bytes, Stage 3
  output, and successful sanity gates. Consumers re-derive mutable hashes and
  reject a symlink, stale source tree, stale seed stamp, or noncanonical path.
- The GPU 2D producer now admits only that manifest-attested Stage 3 path and
  labels its full-CLI state `separate-not-proven`; it does not deploy the
  bootstrap CLI as `bin/simple`. Its explicit-entry native-build route uses the
  bound bootstrap native-all backfill, which is disclosed in both manifests.
  A new Stage 2/3 bootstrap run is still required to create the manifest before
  the production Vulkan build can proceed.
- Stage 4's memory failure is not evidence that the CLI entry closure is
  intrinsically too large. The log reaches `src/app/ui.web/html.spl` through
  eager optional CLI imports (including UI/browser command capsules). The
  correct follow-up is to make optional command owners lazy/dynload capsules
  while preserving the full CLI surface, then rerun the entry-seeded
  `aot_native_project_with_backend_fixed` path. Excluding UI/web source roots
  or deploying `bootstrap_main.spl` as the normal CLI would weaken scope and is
  not an acceptable workaround.
- Before the next Vulkan run, update and review the production builder so the
  core-C runtime bundle is not shadowed by `--runtime-path`. Recover a
  manifest-attested pure-Simple compiler at the canonical path; do not weaken
  compiler provenance to admit an arbitrary binary.
- The ARM64 QMP/RAMFB source lane now has a proposed attested build producer,
  exact artifact/source/HEAD validation, real QMP injection, and guest visual
  commit correlation, but it is not mergeable yet. Final review found two
  fail-closed defects in
  `scripts/check/lib/simpleos-arm64-guest-source-fingerprint.shs`: failed
  `git status` and failed enumeration/sort/hash commands can be mistaken for a
  clean/complete snapshot inside a caller-tested shell function. The
  three-cycle cap is exhausted; fix these in a fresh session, then implement
  the missing guest `[ramfb-visual-commit]` producer before any QEMU PASS.
- Dedicated like-for-like Metal web/widget live wrappers still do not exist.
  Vulkan 2D must pass before Vulkan web/GUI/WM live gates and before starting
  Metal or QEMU acceptance runs.

### 2026-07-25 Font ownership checkpoint

- Vulkan live cycle 1 exposed AOT first-trait-vtable selection. Moving
  `impl Engine2DExtended` after `impl RenderBackend` restored the Vulkan
  `RenderBackend` vtable and advanced the harness through GPU primitives.
- Vulkan live cycle 2 exposed two hosted-native optional ownership faults:
  selected-font physical-path lookup unwrapped an `Option` as a boolean, then
  `Engine2D.draw_text` reused a narrowed boolean as the `FontRenderer`
  receiver. Direct indexed font lookup plus explicit `Some(FontRenderer)`
  stores and `Some` pattern reads now preserve the concrete renderer.
- The focused font-state probe then advanced to atlas invalidation and exposed
  the same class at mutex release. Shared font caches now acquire and return a
  concrete `Mutex`, store it as `Some(active)`, use the free
  `mutex_lock`/`mutex_unlock` facade, and release the exact acquired local.
  Highest-capability review accepted this backend-neutral Vulkan/Metal/CPU
  ownership pattern. Lazy first initialization still has its pre-existing
  hosted concurrency race and is not claimed generally thread-safe.
- Focused physical-path native probe: PASS. The replacement font-state native
  probe compile was stopped after a bounded resource window while still
  consuming 100% CPU and about 8.6 GB RSS; it produced no binary or diagnostic.
  A lightweight file check also stopped before the changed file on existing
  `src/compiler/10.frontend/core/lexer_struct.spl` diagnostics.
- Preserve Vulkan live cycle 3. Do not launch it until a fresh-session focused
  font-state native probe passes. Then build a fresh full harness and consume
  the one remaining live attempt. If it fails, record the result and stop
  under the three-cycle cap.

### 2026-07-25 Engine2D font-owner continuation

- Added the production `Engine2DFontOwner` capsule and routed Engine2D, Draw
  IR, live/perf/RSS probes, compositor provenance, and showcase apps through
  it. Owner operations use free functions with explicit concrete arguments;
  this avoids the hosted AOT bug that drops receivers for no-argument methods
  called through fields. All 23 canonical `Engine2D(...)` literals explicitly
  construct the owner; no callable field default remains.
- Focused owner/mutex native probe cycle 2: PASS. Production Engine2D
  delegation probe cycle 3: PASS after replacing field-method receiver calls
  with explicit free functions. Highest-capability source and disassembly
  review accepted constructor coverage, concrete `FontRenderer` receivers,
  owner clear/recreate, and concrete `mutex_unlock` argument preservation.
- Fresh full Vulkan harness compile: PASS, 212 files, output
  `build/macos_gpu_2d_live_native/stage3_font_owner_free_functions/macos_vulkan_2d_live_native`.
- Canonical live wrapper remains blocked before launch because the existing
  Stage3 compiler has no contemporaneous `provenance.env`. A canonical
  bootstrap producer attempt exited without producing evidence; the preceding
  local producer's retained log ends in 71 unresolved `_rt_cranelift_*`
  symbols plus `_rt_time_now_monotonic_ms`. Do not synthesize a manifest.
- The one remaining diagnostic Vulkan live cycle was consumed with the fresh
  binary packaged as a high-resolution macOS app. PID 3939 exited before
  `ready.env`, runtime receipt, capture, stdout, or stderr. Evidence directory:
  `build/tmp/macos_vulkan_2d_font_owner_live.iPxc00/`. The delayed crash report
  `~/Library/Logs/DiagnosticReports/SimpleGpu2d-2026-07-25-223435.ips` records
  `EXC_BAD_ACCESS` in `VulkanSession.is_valid`, reached through
  `font_atlas_pipeline_evidence` and Engine2D text composition. Receiver
  registers contain tagged text sentinels (`STR1`), so the next fix is Vulkan
  session field/receiver ownership or native struct layout, not FontRenderer
  ownership. No retry is allowed in this session. Vulkan
  rendering/events/vector-font/300-DPI status therefore remains FAIL/unproved;
  Metal, web, GUI, WM, and QEMU stay blocked behind it.
- Parallel source and native-disassembly review then proved the exact corruption:
  `VulkanBackend.init_with_session` stored the return register from
  `session.retain()` into its session slot, and hosted native code returned the
  bare `STR1` header there. The backend now retains separately and stores the
  preserved original session argument; its no-argument evidence method is also
  an explicit `me` receiver.
- `vulkan_session_retention_native_probe.spl` passes with the macOS runtime
  providers linked. Disassembly confirms the original session survives in
  `x28` and is stored at backend offset `+0x180`; the ownership byte is stored
  at `+0x188`. The self-hosted interpreter unit run was stopped as inconclusive
  after five minutes under the runaway guard, so it earns no additional PASS.
- The 72-symbol `driver-trace4` link failure is not the canonical Stage3 path:
  that driver correctly selected core-C, while canonical bootstrap Stage3 uses
  `SIMPLE_BOOTSTRAP=1`, `bootstrap_main.spl`, and native-all. Produce a fresh
  canonical Stage3 and manifest with the standard bootstrap script before the
  next live Vulkan run; never backfill or synthesize provenance.
- The next canonical producer ran through its silent fingerprint phase, then
  failed because provenance path discovery treated vendored
  `block`'s absent `test_utils` dev-dependency as a production input. A scoped
  classifier change now ignores only dev-dependency sections while keeping
  missing normal/build/workspace/patch paths fail-closed, with positive and
  negative fixtures added locally. The broader provenance self-test still
  returns failure without a diagnostic after the bounded repair cycle, so
  these provenance-helper edits remain uncommitted and the producer must not
  be retried again in this session.
- Fresh parallel review repaired the opaque helper failures: negative command
  validation is subshell-contained, BSD `env` receives no literal `--`, the
  combined provenance self-test passes, Darwin tool authority accepts
  non-GNU version behavior, nested authority copies populate before freezing,
  only exact Cargo `target` directories are pruned, and canonical source
  snapshots bind in-tree directory aliases while pruning generated VS Code
  trees. Focused tool and source authority snapshots pass.
- Three bounded canonical producer attempts then exposed and repaired, in
  order, a stale self-referential runtime symlink, unsupported source-directory
  symlinks/global shell output collision, and retry cleanup against the prior
  read-only admitted authority. The final attempt stopped during that cleanup,
  before Stage 2 compilation. A scoped thaw of only the private provenance
  output now passes its focused contract, but the producer must wait for a
  fresh session. The helper/producer bundle remains local and uncommitted until
  a real Stage3 manifest is produced and verified.
- The independent provider micro-probe is now implemented without Engine2D,
  winit, or a window. Its focused source contract passes 2/2, but the canonical
  self-hosted compiler stopped its only native build attempt with
  `Illegal instruction: 4` / `field access on nil receiver`. Do not rerun the
  exhausted full-live Vulkan command or substitute the Rust seed. Resume the
  micro-probe only with a healthy canonical self-hosted compiler, then require
  its provider availability, positive device count, dyld resolution, and
  provider-error fields before another full-live cycle.
- The provenance helper/producer bundle is now committed and rebased as
  `e97529a460` (not pushed). Its focused wrapper/provenance contract passes,
  including invariance under conflicting ambient `SDKROOT`, `CFLAGS`, and
  `LLVM_SYS_*` values. The exact ambient contaminant was Apple `cc --version`;
  selected real Rust/Cargo/CC/llvm-config probes now run under `env -i`.
- An isolated full Cranelift producer at
  `/private/tmp/simple-stage3-git-e975` completed Stage 2 and Stage 3 with 685
  files compiled and zero failures. Stage 3 sanity passed and emitted SHA-256
  `866e43930620393ecd5044684d6ea3d83b84675a2d0152df993d26c58542ee7a`.
  The fresh-shell standalone verifier correctly rejected the manifest:
  producer-time seed authority was
  `d0749dfc29e32998e6639a1ffbc21a5e146e22a595fa98ee0105a63ea7cee64e`,
  while ambient standalone re-derivation was
  `7cd28afe1eba2a356a0ff83d3102d31f706c5afb0e51331f0b4c3731b285a965`.
  Git head, dirty-byte fingerprint, helper bundle, and seed artifact stamp all
  matched. The remaining mismatch is PATH authority: platform detection puts
  LLVM 18's `llvm-config` on the producer PATH, while a fresh verifier shell
  does not. Re-derive the seed fingerprint under the Stage 2 transcript's
  recorded PATH (the exact PATH used by the build), regenerate the manifest,
  and require standalone PASS before pushing or launching Vulkan.
- The three-cycle cap is exhausted for this session. Two clean, inactive,
  detached generated worktrees (`simple-wm-e3e0c5c4` and `engine2d-vulkan`)
  were removed after an independent disk audit to recover about 13.6 GiB;
  their commits remain in Git. Dirty and branch-attached agent worktrees were
  preserved.

### 2026-07-27 native FontRenderer receiver-lowering checkpoint

- Three fresh-session, no-bootstrap focused builds each compiled 184 modules
  with zero failures. Their binaries and terminal results were:
  `3a4ac24823af1df930add1614d94db3affb66cea32409e6ab6d4f8da593d87bd`
  (exit 2, `fail-live-face`),
  `da4b24f203e7c626ea1b80db6b60d11914b241cde041520c568da22f4642869e`
  (exit 3, `fail-live-face`), and
  `6c0a0c8463428f9ba01ae1f0068db9c87ac8705f078e11b2e5010ae4bf686c29`
  (exit 3, `fail-live-face`).
- Cycle 1 proved the owner slot and renderer mutation existed, but a raw
  projected length `1` was compared with tagged literal `8`. Cycle 2 used a
  boolean owner predicate, which passed; `load_font()` returned true and the
  subsequent TTF predicate returned false. Static inspection found the
  decoded renderer in `x12` but no `mov x0, x12` before
  `FontRenderer.has_sffi_ttf`, leaving the enclosing `Engine2D` in `x0`.
- Cycle 3 used an explicitly typed `FontRenderer` local and still reproduced
  the same lowering defect. Final addresses are renderer payload
  `0x1003cc890`/`0x1003cc898`, indirect call `0x1003cc8a4` without receiver
  reload, and the correctly lowered `load_font` control at
  `0x1003d56f8`/`0x1003d5700` before call `0x1003d5710`.
- All product-source and probe edits from these cycles remain uncommitted and
  unaccepted. The three-cycle cap is exhausted. There is no focused font
  producer PASS, Vulkan live PASS, or bootstrap result.
- Next fresh session: fix compiler/backend method-receiver lowering first and
  add an exact native regression proving an array-element-to-typed-local
  receiver is placed in `x0`. Only after that focused compiler proof may the
  Bungee 100 px producer gate resume. A self-hosted rebuild or bootstrap may
  then be essential to deploy the compiler fix; it is not pre-authorized as
  already run.
- Preserve the required order without exception: Vulkan 2D rendering,
  capture, ordered events, vector font and 300-DPI evidence; then Vulkan web;
  Vulkan GUI; host WM; Metal parity in the same order; finally x86/ARM QEMU
  SimpleOS/WM.

### 2026-07-27 Cranelift receiver-argument fix and proof

- The missing receiver was localized below MIR lowering. Both Cranelift call
  builders evaluated each MIR argument and then discarded the array returned
  by `push`: the `CallIndirect` path and `cl_translate_call` in
  `cranelift_codegen_adapter.spl`. Both now rebind
  `arg_vals = arg_vals.push(...)`, preserving the receiver handle for ABI
  argument placement.
- The focused cross-module regression reproduces the exact failing shape
  inside an owner method: `Owner.active[0]` is bound to a typed receiver local
  and a zero-explicit-argument method is called. The target marker is `73`;
  the layout-compatible enclosing owner carries poison marker `11`, so a
  stale `self` cannot pass.
- The old deployed compiler failed this fixture with exit 132 and
  `field access on nil receiver`. An essential isolated bootstrap produced a
  pure-Simple Stage 3 compiler, passed Stage 2/Stage 3 compiler sanity, and
  emitted Stage 3 SHA-256
  `d030566ddab91c85606d9e209524d402cd30df5b4c1a92971732690cbadfa5d1`.
  That compiler passed the exact native fixture with
  `native_consecutive_zero_arg_receiver_status=pass`.
- Stage 4 did not deploy: full-CLI closure discovery stopped on the unrelated
  stale import `examples.browser.entity.dom.css_types` from
  `custom_properties.spl`. The shared root runtime and running MCP/LSP
  deployment were not changed. The broad Cranelift unit file also remains
  non-green on an existing adapter semantic failure (`variable name not
  found`), with 6 of 13 examples passing; it is not counted as PASS.
- Next: compile and run the existing focused Bungee 100 px producer with the
  proven Stage 3 compiler. Require positive quads, atlas/alpha, cold/warm cache
  evidence, and selected-renderer identity before the Vulkan device-readback
  gate. The ordered Vulkan -> web -> GUI -> host WM -> Metal -> QEMU sequence
  remains unchanged.

### 2026-07-27 post-fix font producer checkpoint

- The receiver fix is pushed on `main` as `fba1e6bcab`.
- Using the patched Stage 3 compiler plus the canonical Winit/WM/runtime
  providers, `engine2d_font_state_native_probe.spl` compiled 184 modules with
  zero failures and linked successfully. The native run no longer faults and
  passes font load, live TTF face, and exact selected-font identity.
- The run exits 4 at
  `engine2d_font_state_native_status=fail-cold-cache`: the first
  `Engine2D.draw_text` does not increase the observable rasterization count.
  This is the new leading producer seam. The probe still requests 24 px, not
  the required 24 pt / 300 DPI = 100 px, and it does not prove positive quads,
  atlas alpha, Vulkan execution, or device readback.
- Three producer cycles are consumed for this session: two link-only failures
  identified the required specialized runtime providers, and the third
  produced the runtime result above. Do not rerun this probe in the same
  session. A fresh session must distinguish draw/staging failure from
  cache-state write-back loss, then extend the focused receipt to Bungee
  100 px and positive batch/atlas evidence.
- The unrelated Stage 4 import blocker is source-fixed: browser custom
  properties now import the exact compatible `CSSValue`/`CSSDeclaration`
  owner from `style.animation`, not the deleted loose example module. A
  focused source contract pins `Initial` and `important` compatibility.
  Re-running bootstrap/deploy is deferred to a fresh bounded cycle.

## Required Evidence and Documentation

- `doc/04_architecture/shared_multilingual_gpu_fonts.md`
- `doc/05_design/shared_multilingual_gpu_fonts.md`
- `doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`
- `doc/07_guide/lib/shared_multilingual_gpu_fonts.md`
- `doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.md`
- `doc/06_spec/02_integration/rendering/vulkan_font_composite_classification_spec.md`
- `test/01_unit/lib/engine/font_ffi_spec.spl`
- `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl`
- `test/01_unit/os/compositor/host_compositor_entry_spec.spl`
- `doc/06_spec/01_unit/os/compositor/host_compositor_entry_spec.md`
- `test/03_system/check/macos_vulkan_web_live_evidence_contract_spec.spl`
- `test/03_system/check/macos_vulkan_gui_widget_live_evidence_contract_spec.spl`
- Mirrored manuals for both macOS Vulkan wrapper specs under
  `doc/06_spec/03_system/check/`

Refresh shared font documentation only after the current provider behavior is
proven; do not preserve obsolete SPIR-V hash/size or rejected semantic claims.

### 2026-07-27 Bungee producer cycles 4–6 and Vulkan installation

- macOS Vulkan installation is complete and healthy. Homebrew reports
  MoltenVK 1.4.1 plus Vulkan loader/tools 1.4.350.1. With
  `VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`,
  `vulkaninfo --summary` enumerates Apple M4 with
  `DRIVER_ID_MOLTENVK`, driver name MoltenVK, and driver info 1.4.1.
- All three fresh no-bootstrap producer builds used the retained pinned
  pure-Simple Stage3 diagnostic compiler (SHA-256
  `d030566ddab91c85606d9e209524d402cd30df5b4c1a92971732690cbadfa5d1`)
  and compiled
  184 modules with zero failures. This is diagnostic evidence, not
  current-main manifest attestation.
- Cycle 4 advanced past atomic cold-cache reset and configured staging, then
  faulted in the immutable zero-argument
  `Engine2D.font_receipt_size_100px` receiver. The crash report shows `x0=0`.
  Receipt methods now use the proven mutable-receiver ABI.
- Cycle 5 no longer faults and exits exactly at
  `engine2d_font_state_native_status=fail-positive-quads`. It proves exact
  Bungee identity, the local 24-point/300-DPI derivation, cold reset, draw
  admission, and the 100-pixel boolean receipt.
- Cycle 6 retains the same clean `fail-positive-quads` result after rebinding
  every returned array in the fallback layout, atlas metadata, quad, dirty,
  and glyph-cache insertion paths. Its binary SHA-256 is
  `746a2a08148b9b12ca41aa62ca932341418ac00c92cdebd40ff31fea89ccd283`.
- The selected renderer has exact Bungee identity; independently, the batch is
  staged-valid with a 1024² atlas allocation but still has zero quads. The
  three-cycle cap is exhausted.
  Do not rerun this producer in the same session. The next session must add
  boolean-only local/inbound/stored quad receipts around the
  `FontRenderBatch -> _stage_batch` boundary before attempting Vulkan live
  evidence. Atlas allocation alone is not glyph/alpha proof.
- Vulkan 2D/web/GUI/WM live gates remain blocked by the red producer gate and
  the absent current manifest-attested GUI-capable pure-Simple artifact.

### 2026-07-27 Bungee producer cycles 7–9

- Three boolean-only receipts now distinguish local quad production, inbound
  `FontRenderBatch.quads`, and stored `FontRenderer.staged_quads`. Required
  boolean arguments and mutable receiver methods avoid the known zero-argument
  immutable receiver ABI fault.
- Cycle 7 compiled 184 modules with zero failures and exited exactly at
  `fail-local-quads`. This proves the aggregate batch boundary was not yet
  reached with a nonempty local quad array.
- Second-level receipts distinguish layout, positive glyph dimensions, atlas
  index, and append reachability. Cycle 8 compiled 184 modules with zero
  failures and exited exactly at `fail-text-glyph`: layout is nonempty, but
  the glyph returned to `_stage_text_active` has no positive width/height.
- Rasterizer pixel arrays, WFFI argument arrays, SFFI layout arrays, glyph
  cache arrays, shaped identity arrays, and advance-layout arrays now preserve
  value-returning `push` results. Cycle 9 still exits exactly at
  `fail-text-glyph`. Cycle 8 and Cycle 9 binaries have the identical SHA-256
  `7db8cc35eeab4fd6e406711c043cfa64f16a437ae3ecf858e0d1926990c284dc`;
  on this closure those source corrections did not change emitted code and are
  not the remaining direct Bungee cause.
- The three-cycle cap is exhausted. The next session must add boolean-only
  checkpoints inside `get_glyph`: selected face maps the codepoint, rasterizer
  bitmap is non-nil, raw dimensions are positive, pixel count matches,
  reconstructed `CachedGlyph` is positive, and the returned glyph remains
  positive. Do not retry the current probe unchanged.

### 2026-07-27 Bungee producer cycles 10–12

- Boolean-only receipts now cover the selected-face mapping, non-nil bitmap,
  bitmap dimensions/pixels, adapter, same-module reconstruction, local return,
  first caller, and cache-hit boundaries. A parallel read-only audit confirmed
  the active macOS path is the built-in selected-outline rasterizer, not WFFI.
- Cycle 10 compiled 184 modules with zero failures and exited exactly at
  `fail-glyph-bitmap-pixels`. The selected face maps the codepoint and returns
  a non-nil bitmap with positive dimensions, but the pixel count is already
  inconsistent before `_sffi_glyph_to_cached`.
- Cycle 11 rebound every value-returning `push` in `sfnt_glyf`, including the
  coverage pixel loop. The binary changed, but the exact
  `fail-glyph-bitmap-pixels` result remained. Local push loss is therefore not
  sufficient to explain this boundary.
- Cycle 12 experimentally wrapped the selected-outline tuple with boolean
  status plus mutable pixel/metric outputs. It compiled 184 modules with zero
  failures but regressed to `fail-glyph-bitmap-return`. High review found that
  two array-bearing tuple returns still remained underneath the wrapper, so
  the call-site experiment was reverted before commit.
- The three-cycle cap is exhausted. Do not bootstrap and do not rerun this
  producer unchanged. In the next bounded session, add source-module boolean
  receipts around `_sfnt_rasterize_glyph_parts` and the mutable-output copy to
  distinguish an empty source bitmap from tuple-return loss. The fix must
  remove the aggregate-return chain end-to-end, preferably with a
  live-receiver raster result owner holding scalar metrics and owned pixels.

### 2026-07-27 Bungee producer cycles 13–15

- A selected-font experiment removed `Option<SfntGlyfBitmap>`, both pixel
  tuple returns, and `GlyphBitmap?` from the active path by staging through
  mutable SFNT and `FontRasterizer` owners. Source-local/source-stored boolean
  receipts precede the prior bitmap receipts.
- Cycles 13 and 14 each compiled 184 modules with zero failures and exited
  exactly at `fail-glyph-source-local-pixels`. Cycle 14 used an exact-size
  preallocated coverage buffer with indexed writes, so repeated array growth
  is not the direct cause.
- Cycle 15 added a scalar phase status to distinguish pre-raster failure from
  local pixel mismatch. It compiled 184 modules with zero failures, but the
  status reached the probe as an empty value
  (`fail-glyph-source-status-`, exit 43). This is direct evidence that the
  cross-module result receiver/scalar-field chain is itself unreliable on the
  retained compiler.
- The three-cycle cap is exhausted and no bootstrap was run. Do not push or
  treat the current live-owner experiment as a fix until high review accepts
  a safe subset. The next production design should use a module-local raw
  scalar-owned buffer or scalar handle/descriptor, copy pixels once at the
  SFFI boundary, and avoid aggregate receivers, aggregate returns, and
  receiver-field status transport across modules.

### 2026-07-27 Bungee producer cycles 16–18

- Cycle 16 added a fixed-size imported unit-return sentinel over preallocated
  caller-owned `[i64]` and `[u8]` arrays. It compiled 184 modules with zero
  failures, passed every exact sentinel check, and continued to the known
  `fail-glyph-bitmap-pixels`. Indexed mutation across the common-to-SFFI
  boundary is therefore proven on this artifact.
- Cycle 17 applied the same shape to two selected-glyph calls: measure writes
  fixed metadata slots and render fills an exact-size caller pixel plane.
  It compiled 184 modules with zero failures but stopped at
  `fail-glyph-bitmap-return`.
- Cycle 18 added boolean-only measure/render completion receipts, compiled
  184 modules with zero failures, and exits exactly at
  `fail-glyph-void-measure`; rendering is never reached.
- The three-cycle cap is exhausted and no bootstrap was run. High review must
  remove the unproven production integration before push. The next probe must
  write monotonic fixed metadata stamps after input validation, font parsing,
  cmap mapping, table validation, outline parsing, metrics, and bounds.

### 2026-07-27 Bungee producer cycles 19–21

- Cycle 19 compares an owner-local Bungee blob fingerprint with a separate
  common-module void fingerprint of the extracted blob. Both pass exact
  length/header/sample/cookie checks; the run then reaches the established
  `fail-glyph-bitmap-pixels`. Selected-blob extraction is not the active loss.
- Cycle 20 adds diagnostic-only monotonic measure stamps. Parsing, cmap, table
  bounds, metric bounds, outline parsing, and horizontal metrics all pass; the
  coarse final geometry receipt fails.
- Cycle 21 splits geometry into drawable commands, bounds availability, and
  dimensions. Every phase passes, then the run again exits at
  `fail-glyph-bitmap-pixels`. All three builds compile 185 modules with zero
  failures.
- The prior cycle-18 measure failure belongs to final metadata
  publication/validation, not font parsing or geometry. The next production
  fix must keep parsing owner-local and replace only the post-raster pixel
  publication with a raw scalar descriptor/pixel pointer or an owner-local
  void copy. Remove diagnostic double parsing from the glyph hot path before
  push unless high review explicitly accepts a bounded test-only form.

### 2026-07-27 Bungee producer cycles 22–24

- Cycle 22 implemented the canonical 17-slot two-pass SFNT metadata contract,
  caller-owned exact-size pixels, codepoint/glyph-index parity, whitespace
  completion, and the missing value-returning `_add_edge` assignment. It
  compiled 185 modules with zero failures and advanced from
  `fail-glyph-bitmap-pixels` to `fail-glyph-bitmap-return`. Later isolated
  evidence shows that result did not prove final measure publication.
- Cycle 23 moved selected codepoint and glyph-index consumption into
  FontRenderer and constructed `CachedGlyph` locally, but routed measure and
  render through FontRasterizer instance methods. It compiled 185 modules with
  zero failures and retained the exact `fail-glyph-bitmap-return` result, so
  that instance-method mutable-output channel is not accepted.
- Cycle 24 retained the selected blob on FontRenderer and invoked the common
  free two-pass functions directly. It compiled 185 modules with zero failures
  and still retained the exact `fail-glyph-bitmap-return` result. The next
  session must first isolate mutable-slice survival across an intervening call
  in a compiler-only regression probe.
- The review after cycle 24 suspected that cycles 23 and 24 shared a
  call-rich mutable-slice
  lifetime: `mut meta` and `mut pixels` remain live across aggregate-return and
  scalar helper calls before their completion writes. Cycle 16 proved only a
  leaf mutation without intervening calls. The leading root cause is therefore
  native/Cranelift slice-descriptor preservation across calls. Cycles 25–27
  below disprove that hypothesis; do not patch the compiler on this evidence.
- Final review rejected the unproven two-pass integration, FontRenderer blob
  retention, and associated protocol hardening for mainline; those edits were
  reverted. The independently definite `_add_edge` dropped-value repair was
  retained: it rebinds the value-returning `push`, compiled in all three
  cycles, and does not introduce a new transport surface.
- The mandatory three-cycle cap is exhausted. No bootstrap was run. Do not
  push the current source as a fixed implementation and do not rerun the same
  probe unchanged.

### 2026-07-27 Bungee producer cycles 25–27

- A new cross-module regression mutates preallocated `[i64]` and `[u8]`
  arrays before and after scalar and 32-byte aggregate-return calls. The
  retained pure-Simple Stage3 built and ran it successfully with both
  Cranelift and LLVM, and its focused ownership contract passes 1/1 in the
  interpreter runner. Arrays are single `SplArray*` handles in this lowering,
  not fat slice descriptors; the previous leading diagnosis is falsified.
- The same build exposed a current macOS core-C portability regression:
  `closefrom` is undeclared and a Linux-only `expected_parent` local is unused.
  The first workaround compiled, but final review rejected it: this host's
  `OPEN_MAX` is 1,048,575, so the generic loop would issue about one million
  closes per spawn and call `sysconf` after `fork`. That workaround and its
  source-only test were reverted. A fresh runtime session must implement and
  behaviorally verify an efficient Darwin strategy (for example,
  `posix_spawn` with `POSIX_SPAWN_CLOEXEC_DEFAULT`) before native builds can
  rely on current main without a dirty portability patch.
- The fresh Darwin runtime session completed that prerequisite without a
  bootstrap. Apple piped spawning now uses `posix_spawnp` with atomic process
  group creation, `POSIX_SPAWN_CLOEXEC_DEFAULT`, explicit stdin/stdout actions,
  and stderr inheritance when the parent left it open. It does no work after
  `fork`, preserves the inherited signal mask, and resets INT/TERM/PIPE
  handlers. The focused macOS runtime suite passes strict `-Werror` compilation,
  arbitrary non-CLOEXEC descriptor isolation, process-group termination and
  reaping, bounded writes, 32-slot recycling, and a generous five-second
  aggregate launch-latency guard. Linux and FreeBSD retain the existing
  fork/exec implementation.
- Cycle 25 directly consumed caller-owned selected-font metadata and pixels
  from FontRenderer while still allowing the legacy aggregate fallback. It
  compiled 192 modules with zero failures and stopped at
  `fail-glyph-bitmap-pixels`; that result was still reachable through the
  fallback and did not prove the new render path.
- Cycle 26 isolated the common two-pass API over exact Bungee `B` at 100 px.
  It compiled 11 modules with zero failures and exited `2`, before a valid
  measure status/cookie was published. Allocation and render were not reached.
- Cycle 27 removed the new helper that accepted `OtFont`, gated the direct
  path to the built-in selected face, disabled its aggregate fallback, and
  added fail-closed state/currency validation. It compiled 192 modules with
  zero failures and stopped exactly at `fail-glyph-bitmap-return`, confirming
  measure publication still fails before FontRenderer accepts a bitmap.
- The font cycle cap is exhausted and no bootstrap was run. Revert the
  unproven font integration before push. The next session must phase-stamp the
  isolated measure function once rather than redesign another transport.

### 2026-07-27 Bungee measure cycles 28–30

- Cycle 28 recovered the exact 17-slot caller-owned contract and a seven-slot
  monotonic measure trace from the prior rollout. The installed pure-Simple
  release compiler stopped before compilation with its existing
  `field access on nil receiver` (exit 132), so it produced no font evidence.
- A preserved, provenance-passing Stage3 compiler was then reused; no bootstrap
  command was run. Cycle 29 compiled the isolated Bungee `B`/100 px measure
  probe (11 modules, zero failures). Its single run published entry, input
  validation, offset-table parse, and cmap/glyph selection, then returned
  before the intra-module `rasterize_sfnt_glyf` result, scalar metadata, or
  completion cookie.
- Cycle 30 replaced only that aggregate bitmap-return seam with the recovered
  scalar-only table/outline/metrics/bounds measure pass. It compiled two
  changed modules with nine cached and zero failures, but the single run
  stopped at the same coarse boundary: parse and glyph selection pass; no
  completed scalar geometry or metadata is published.
- The three-cycle cap is exhausted. All unproven diagnostic source and the
  temporary fixture were reverted before push. The next fresh session must
  place fixed tail stamps within the scalar measure body after table lookup,
  table bounds, units/metric bounds, outline parse, horizontal metrics,
  drawable detection, bounds, and dimensions. Run one isolated Bungee measure
  probe and fix only the first missing phase. Do not bootstrap merely to repeat
  this diagnostic; reuse a current provenance-passing pure-Simple artifact.

### 2026-07-27 Bungee measure cycles 31–33

- Cycle 31 used a 15-phase caller-owned scalar trace over exact Bungee `B` at
  100 px. Tables, table bounds, units/metric headers, metric extent, outline,
  hmtx, drawable commands, and bounds all pass; the combined dimensions guard
  returns before publication.
- Cycle 32 split that dimensions guard into ordered scalar checks and published
  the computed values. The probe passes completely with raw dimensions
  approximately 61x72, rounded dimensions 62x72, and exact pixel count 4,464.
  This proves the scalar two-pass measure contract can publish valid Bungee
  geometry and completion state on the retained Stage3 diagnostic compiler.
- Cycle 33 applied the same ordered guards to the real
  `rasterize_sfnt_glyf` path and added an owner-local receipt for bitmap
  dimensions, pixel count, nonzero alpha, and completion cookie. Scalar measure
  still passes, but the real raster receipt remains entirely zero:
  `rasterize_sfnt_glyf` returns `None` after valid dimensions and before a
  bitmap can be accepted.
- The three-cycle cap is exhausted. Diagnostic source, temporary fixture, and
  the unproven production guard edit were reverted. The next fresh session must
  stamp only the post-dimension raster body: edge-list completion/count,
  pixel-plane allocation, per-row progress, final pixel count/nonzero alpha,
  `SfntGlyfBitmap` construction, and caller-side `Some` discrimination. Fix the
  first missing phase, then retain a focused native Bungee regression. No
  bootstrap was run.

### 2026-07-27 Vulkan web/GUI launch provenance hardening

- No bootstrap was run. Strict macOS Vulkan web/GUI launch now resolves the
  Homebrew ICD symlink, parses its one `ICD.library_path`, and hashes both the
  canonical JSON and canonical `libMoltenVK.dylib`.
- Receipt v3 binds the admitted compiler, winit provider, build-manifest
  runtime providers, ICD, MoltenVK image, and the exact library search path.
  The launched PID must actually map the admitted winit and MoltenVK images;
  build-only runtime providers remain manifest provenance and are not
  misreported as loaded rendering images.
- Caller dyld/driver/layer overrides are rejected in strict mode, pinned plist
  paths are XML-escaped, and web/GUI wrappers revalidate every receipt path and
  hash. Focused shell syntax, real installed MoltenVK resolution, strict
  launcher probe, GUI contract, artifact-layout, env-boundary, and rendering
  source-coupling checks passed during the bounded cycles. Final review then
  required restoring the spec terminator and retaining a focused symlink,
  relative-library, hash, and multi-ICD rejection fixture. Those exact test
  edits are present locally, but the three-cycle cap was reached before their
  final rerun; the implementation is not pushed as verified. In a fresh
  session, run only
  `test/01_unit/scripts/macos_gui_run_strict_contract_spec.spl`, then the two
  Vulkan web/GUI contract specs once. The web contract previously executed 11
  scenarios but had four HTML-fixture failures on the deployed runner; it is
  not a live Vulkan PASS.
- Hosted-WM audit found that the existing fullscreen gate still serializes an
  untyped CPU mirror and drives FIFO actions. Reuse its semantic/fullscreen and
  checksum logic, but do not claim host-WM Vulkan completion until a typed
  device-readback receipt, PID-owned macOS window capture, and native OS input
  sequence replace those authorities.
- Continue without bootstrap unless a later goal criterion cannot be reached
  with an already-built, provenance-admitted pure-Simple artifact.

### 2026-07-27 Bungee caller-owned raster cycle 34

- No bootstrap was run. A durable focused native probe now locks exact Bungee
  `B` at 100 px to 62x72, 4,464 pixels, nonzero alpha, and a completion cookie.
  The unchanged aggregate/Option path reproduces `fail-raster` with a strict
  zero-stub Cranelift build.
- A first caller-owned measure/render implementation removed the
  `Option<SfntGlyfBitmap>`, tuple, and returned-pixel-array channels. Its strict
  native build compiled two modules with zero failures and zero stubs, but the
  run stopped at `fail-measure`: metadata written by the nested private
  `_sfnt_measure_glyph_into` helper did not survive through the public
  `sfnt_measure_codepoint_into` caller.
- The three-cycle cap is reached. Do not rerun this shape. In a fresh session,
  inline the measure publication directly in the public owner function (one
  mutable-array boundary), keep the exact preallocated render buffer, and run
  the focused probe once. If measure passes but render fails, replace the
  returned `_outline_edges`/recursive `_quad_edges` arrays with owner-local
  indexed edge storage; do not redesign the font pipeline or bootstrap.
- The Vulkan provider/ICD hardening remains local and unpushed: its launcher,
  ICD fixture, and GUI contracts pass, while the web contract reports 11
  passing and four opaque pre-existing HTML-fixture failures after its own
  three-cycle cap. It must not be merged until that contract is isolated in a
  fresh session.

### 2026-07-27 Bungee caller-owned raster cycles 35–37

- No bootstrap was run. Inlining all measure logic into the public owner
  function still stopped at `fail-measure`.
- The existing fixed-array/unit-return canary then passed across the exact
  module boundary. A monotonic trace in the real measure body reached parsed
  font, cmap, table bounds, outline, hmtx, and outline bounds, then stopped in
  the dimension checks.
- Replacing the combined dimension predicate with ordered guards compiled
  strictly with two modules changed, nine cached, zero failures, and zero
  stubs, but still stopped at the same coarse dimension trace slot. The final
  binary is `/private/tmp/simple-sfnt-glyf-bungee-native-ordered-guards`.
- The three-cycle cap is reached. In the next fresh session, stamp separately
  after `raw_w`, `raw_h`, `width`, `height`, maximum-width, maximum-height, and
  pixel-count guards while publishing raw/rounded values into unused metadata
  slots. Run the focused probe once and fix only the first failing comparison.
  Do not repeat the current coarse trace, do not touch the render body yet,
  and do not bootstrap.

### 2026-07-27 Bungee caller-owned raster cycles 38–40

- No bootstrap was run. Expanding the caller-owned metadata buffer exposed the
  native fixed-array layout requirement: the strict focused Bungee probe now
  passes exact `B` at 100 px with width 62, height 72, 4,464 pixels, nonzero
  alpha, and both completion cookies. It compiled two modules with nine cached,
  zero failures, and zero generated stubs.
- The selected-font path is now wired locally into `FontRenderer`: it retains
  the validated font bytes, measures and renders directly into caller-owned
  arrays, and constructs `CachedGlyph` in the consuming module. The legacy
  dylib rasterizer path remains unchanged.
- The broader Engine2D probe compiled the edited Simple closure, then failed
  only at link because `core-c-bootstrap` lacks the required GPU symbols. The
  final bounded attempt selected `host-gpu`, but the preserved Stage 3 runtime
  capsule does not contain its canonical hosted runtime rlib. No probe run was
  possible and the three-cycle cap is reached.
- Do not push the font implementation yet. In a fresh session, use an existing
  provenance-acceptable `host-gpu` runtime artifact if one is found; do not
  bootstrap merely to manufacture it. Require the broader Bungee/Engine2D
  producer receipts before returning to Vulkan device-readback evidence.
- Independent review also requires four source corrections before that run:
  preserve selected-asset physical/root resolution instead of raw local-path
  reads; clear measure/render cookies before every possible failure; preserve
  the legacy positive advance fallback; and trim `sfnt_glyf.spl` below 800
  lines. Add stale-cookie, whitespace, asset-root, and renderer cache coverage.

### 2026-07-27 reviewed font PASS and Vulkan availability blocker

- No compiler bootstrap was run. MoltenVK 1.4.1 and Vulkan loader/tools 1.4.350.1
  are already installed and `vulkaninfo` enumerates the Apple M4 through
  `DRIVER_ID_MOLTENVK`; installation is not the blocker.
- The reviewed caller-owned SFNT probe passes a strict zero-stub native build:
  exact Bungee `B` at 100 px is 62x72 with 4,464 pixels and nonzero alpha;
  stale measure/render cookies clear, and space remains a valid advance-only
  glyph. `sfnt_glyf.spl` is 798 lines.
- A new focused `FontRenderer` native probe also passes through the active
  scalar staging path: positive quads and atlas alpha, positive cold
  rasterization, and a warm cache hit with zero rerasterization.
- With an already-retained diagnostic hosted-GPU projection, the complete
  `engine2d_font_state_native_probe.spl` links and passes 24 pt at 300 DPI,
  selected Bungee identity, quads, atlas alpha, and cold/warm cache receipts.
  This is behavioral evidence only because that runtime projection lacks the
  canonical trusted-build provenance required for release evidence.
- The real macOS Vulkan live harness then compiled successfully, but its
  bounded launch selected `cpu` and wrote
  `Vulkan shared session initialization failed: availability`. The three live
  cycles are consumed. Next, build a provenance-bound host-GPU runtime with
  Vulkan enabled (an app/runtime build, not a compiler bootstrap), extend the
  trusted manifest with anchored ICD/MoltenVK hashes and live loaded-image
  binding, then rerun capture and ordered focus/pointer/key evidence. Metal and
  QEMU remain gated behind host Vulkan PASS.
- Final review prevents merging the font patch yet: the renderer probe must
  force `try_load_selected_bytes` rather than allowing an installed font dylib,
  and must require every direct raster/reconstruction receipt unconditionally
  so vector/bitmap fallback cannot produce a false PASS. Add asset-root and
  zero-advance renderer coverage. The deployed interpreter is also stale
  against the current unit surface (`unwrap on None` in the existing SFNT spec;
  removed `font_ffi` export in the existing FFI spec), so those runs are not
  PASS. Keep the implementation local until a fresh bounded session repairs
  the probe and produces honest native evidence.

### 2026-07-27 honest FontRenderer proof and final unit-spec blocker

- No bootstrap was run. The strengthened native renderer probe now forces
  selected Bungee bytes, requires every direct raster/adapter/reconstruction
  receipt unconditionally, proves asset-root rejection and positive loading,
  positive staged quads/atlas alpha, cold/warm cache behavior, and U+0300
  normalization from raw 42x22/advance-0 to advance 43. It passes a strict
  zero-stub native build.
- The zero-extent outline regression was corrected without reopening the
  divide-by-zero path: raw dimensions reject only negative values, while the
  ordered rounded width/height guards remain positive before division. The
  deployed pure-Simple interpreter now passes `sfnt_glyf_spec.spl` 4/4.
- `font_ffi_spec.spl` is the last font merge blocker. Its removed
  `font_ffi` import was corrected to `font_sffi`, and two stale interpolated
  candidate literals were escaped. The third bounded run reaches 12/14 but
  still parses two import-source assertion strings as interpolation
  (`sfnt_cmap_glyph_id` and the matching SFNT glyf import). Escape those
  literal braces and rerun once in a fresh session before pushing the font
  implementation.
- The canonical non-bootstrap Vulkan app builder remains unable to start
  because its required current pure-Simple Stage 3 compiler/provenance pair is
  absent. The deployed release compiler is too old for trusted host-GPU
  provider admission. A compiler deployment/bootstrap is now technically
  essential for authoritative Vulkan evidence unless another active lane
  supplies that exact admitted pair; do not substitute the Rust seed.

### 2026-07-27 generic glyph selector and shaped-ascent checkpoint

- The local font implementation now exposes one generic caller-owned
  measure/render contract for both Unicode codepoints and producer-shaped
  glyph indices. Selector kind and value are bound into the metadata receipt,
  so render cannot consume a measurement made for a different selector.
- The low-level strict native selector probe passed codepoint/index parity
  before the later ascent-receipt extension was added. That PASS does not
  attest the current ascent-bearing metadata shape.
- The native `FontRenderer` path no longer crashes. It advanced into shaped
  batch construction, then failed because the selected pure-SFNT face reported
  an ascent of zero, so no shaped batch was admitted.
- The generic measure receipt now publishes scaled `hhea` ascent, and the
  selected-face shaped path consumes that receipt when its provider line
  metric is unavailable. This ascent fix is applied locally but remains
  unverified because the mandatory three-cycle cap is exhausted.
- Nothing from this checkpoint has been pushed, and no bootstrap was run.
  Keep the font/ascent result explicitly unproved until a fresh bounded
  session runs the selector and renderer native evidence once.
- The Vulkan release-path builder is delegated to a separate lane. Do not
  duplicate or absorb that builder work while continuing the font evidence
  lane.

### 2026-07-27 font push and release-builder admission cap

- The completed font lane is pushed on `main` as commit `bbb98e957a`.
  This supersedes the earlier local/unpushed font checkpoint; it does not
  establish Vulkan live evidence.
- The isolated release-path builder/admission lane remains uncommitted and
  unpushed. Its mechanical hardening is present locally: host binding, an
  exact seed classifier, private compiler and provider snapshots, a
  backend-local cache, an admission transcript, and an executable self-test.
- Release provenance still does not attest the exact Stage 3 producer command
  that created the release binary. The hardened builder therefore cannot yet
  admit that binary as authoritative release evidence.
- Two downstream static specifications remain red. Cleanup of the private
  compiler/provider snapshots is also not bounded, so the lane is not ready
  for merge or release use.
- The builder lane has reached its mandatory three-cycle cap. No bootstrap and
  no Vulkan live run were performed in that lane. Leave its changes local and
  resume only in a fresh bounded session that first closes producer-command
  provenance, the two static failures, and bounded snapshot cleanup.

### 2026-07-27 current-origin Stage 3 and ES self-test checkpoint

- One technically essential, bounded LLVM bootstrap at Git revision
  `d51ed3ec8b` completed successfully. Stage 2 and Stage 3 sanity passed, and
  the canonical provenance facade admitted Stage 3 SHA-256
  `e04c2ec7bbea06bea2d1aa43334216f27ad87813e8439d6bac826ffaaf54e76f`
  with adjacent v3 provenance.
- The standalone winit and Vulkan-enabled runtime providers built and staged
  successfully. They remain local build artifacts and do not by themselves
  establish trusted Vulkan execution.
- The EndpointSecurity collector self-test exposed an interactive overwrite
  prompt while replacing its frozen tamper fixture. The fix makes the fixture
  temporarily writable and updates the policy's builder digest. The committed
  non-interactive self-test passed; the fix is pushed as `a2fe118b69`.
- The pushed fix advances Git HEAD, so the otherwise intact Stage 3 pair is
  now correctly rejected by exact-HEAD provenance admission. Do not synthesize
  or edit its manifest. In a fresh bounded session, produce one Stage 3 pair
  from the then-current `origin/main` before retrying the Vulkan builder.
- Full CLI GUI provenance also remains fail-closed while the tracked
  EndpointSecurity policy is `status=unavailable` with unassigned signing and
  team identities. Do not treat the collector self-test as live
  EndpointSecurity authorization or as GUI execution-history evidence.

### 2026-07-27 standalone Vulkan v4 and native-lowering checkpoint

- Standalone Vulkan 2D trust is pushed as `19d51754cc`. Manifest v4 binds the
  executable actually launched, canonical Stage 3, source snapshot, providers,
  transcript, and output. It no longer authenticates an unused full CLI.
  Web/GUI retain their separate full-CLI plus EndpointSecurity admission.
- MoltenVK evidence now pins and hashes the canonical Homebrew ICD and
  `libMoltenVK.dylib`, rejects caller loader/provider/DYLD substitution, and
  uses bounded process-group cleanup. Metal launch metadata remains isolated
  from Vulkan settings.
- An exact-`19d51754cc` LLVM Stage 3 completed and passed canonical provenance
  admission (compiler SHA-256
  `36c3bdfb0173b3ddf3b673174c2c69e640fdeb6b707c4245f1e84f862b793b1a`).
  The first trusted Vulkan build reached current source and failed at a
  multiline expression in `draw_ir_adv.spl`, not at Vulkan admission.
- Focused native cycles fixed the two missing expression parentheses, changed
  the Draw IR import to its native-resolvable `std.common` path, and made the
  conditional prepared font batch explicitly `FontRenderBatch`. Each repair
  advanced native lowering.
- The cycle cap is exhausted. The next exact failure is
  `_engine2d_draw_ir_adv_composition_with_images`: native lowering treats
  `DrawIrTargetFontEvidence.batch_identity` as uninferred. Start the next
  bounded cycle at that typed return/field boundary. Do not rerun bootstrap or
  repeat the already-closed parser/import/font-batch probes first.

### 2026-07-27 Draw IR font-evidence optional checkpoint

- The guarded optional font receipt is now concretely rebound as
  `DrawIrTargetFontEvidence` before its scalar receipt fields are copied into
  the Draw IR result. This preserves Draw IR's semantic/scalar boundary:
  transient `FontRenderBatch`, atlas, and cache material remain owned by the
  renderer/backend.
- The focused native contract follows the existing guarded-rebind workaround
  and rejects `.?`, whose freestanding lowering is tracked separately.
- A diagnostic native build of the complete macOS Vulkan 2D live harness
  compiled 216 modules and linked successfully with zero failures. This closes
  the previously recorded `batch_identity` inference failure.
- The diagnostic used the retained pre-HEAD Stage 3 only to validate lowering;
  it is not authoritative execution evidence. Next, create one exact-current-
  HEAD Stage 3 pair, pass canonical admission, and run the trusted v4 Vulkan
  evidence builder. Do not claim live Vulkan, font, or 300-DPI PASS yet.

### 2026-07-27 exact-HEAD bootstrap disk checkpoint

- The clean rendering lane was synchronized to `origin/main` revision
  `4a12f533c9`. The v4 native-builder contract self-test passed at that
  revision, and the required MoltenVK/runtime providers remain present.
- One essential, jobs=1 LLVM full-bootstrap attempt rebuilt the Rust seed and
  native-all archive, then stopped before Stage 2 while copying
  `libsimple_native_all.a`: macOS reported `No space left on device`.
  This is a storage-capacity failure, not a Simple source/lowering failure.
- No second bootstrap was attempted. The first-attempt logs remain under
  `build/wm-to-i64-bootstrap/logs/aarch64-apple-darwin/`, and the reusable
  Cargo target was preserved.
- A later single bounded attempt at `f4689e6955` started with 5.0 GiB free.
  Seed and native-all completed, but runtime-nolto stopped while creating Cargo
  metadata with the same `No space left on device` cause. Compiler backfill and
  Stage 2 did not start; no source/compiler failure was observed.
- The current attempt allocated 2.44 GiB in its isolated authority. A concurrent
  root-repository bootstrap grew by about 3.35 GiB during the same interval,
  explaining why the prior 5 GiB floor was insufficient. That other agent's
  authority was preserved. Safe removal of an empty merged jj workspace and
  inactive regenerable caches raised free space to 7.7 GiB.
- Recheck for at least 7 GiB free and no concurrent bootstrap immediately
  before the next single bounded attempt. Preserve the first-attempt logs,
  canonical SFFI providers, and other agents' bootstrap/GUI authorities.
- A subsequent full attempt at `7b54ad6a79` completed the Rust seed,
  native-all, runtime, compiler backfill, and stamped tuple. Stage 2 compiled
  and passed bootstrap-compiler sanity. Stage 3 compiled but its final link
  stopped with `errno=28`; no source/compiler error was reported.
- The stamped tuple passes the canonical seed verifier, so another full
  bootstrap is neither necessary nor allowed for this lane. Remove no tuple
  files. The next bounded attempt must be incremental:
  `--pure-simple --backend=llvm --mode=dynload --jobs=1 --no-mcp`.
- The incomplete Stage 3 and now-unreferenced isolated Rust authority were
  removed after their processes exited; Stage 2, logs, providers, and the
  verified tuple remain. Start the incremental retry only with at least 2 GiB
  free and no concurrent bootstrap/native-build writer.
- The incremental retry at `792af24d9f` reused the verified tuple with Cargo
  disabled. Stage 2 and Stage 3 compiled and passed sanity, canonical v3
  provenance was written, and the v4 Vulkan native builder admitted and built
  its trusted executable.
- The first trusted live run verified the MoltenVK device/driver but stopped at
  ProcessingIR stage 4. A diagnostic receipt exposed
  `vulkan-shader-compile-failed`: the ProcessingIR path imported the I/O Vulkan
  facade, whose SPIR-V wrapper still passed a Simple array through the
  interpreter ABI during native execution.
- The I/O owner now selects the interpreter array ABI only in the interpreter
  and otherwise calls `rt_vulkan_compile_spirv_raw` with pointer and byte
  length, matching the established Engine2D owner. A cache-preserving native
  mini-build recompiled two modules and reused 214; the diagnostic then passed
  ProcessingIR and advanced to the intentionally unconfigured font stage.
- The failure receipt now retains ProcessingIR reason, completion, count,
  checksums, handle, and device identity in one atomic write. Commit this fix,
  run one incremental exact-HEAD Stage 2/3 provenance refresh, rebuild the
  trusted executable, and repeat the live Vulkan evidence run.
- macOS preflight reports both Accessibility UI scripting and Screen Recording
  access enabled. The trusted live run must still prove actual ordered input
  and exact-window capture; these permission probes only remove likely external
  launch blockers.
- Canonical Stage 3 and its v3 provenance are still absent. Consequently the
  trusted v4 Vulkan executable and live rendering/capture/event/font/300-DPI
  evidence remain pending; do not run or attest them from partial bootstrap
  material.

### 2026-07-27 Vulkan loader-alias checkpoint

- The native ProcessingIR raw-SPIR-V ABI and atomic diagnostic receipt shipped
  in `cbfc9c44e1`. An incremental `--pure-simple` refresh produced exact-HEAD
  Stage 2/Stage 3 artifacts, passed Stage 3 sanity and provenance admission,
  and the trusted v4 Vulkan builder passed.
- The next trusted live run retained the precise ProcessingIR failure as
  `vulkan-init-failed`. A bounded direct diagnostic proved the canonical
  `VK_ICD_FILENAMES` succeeds, while adding empty `VK_DRIVER_FILES` and
  `VK_ADD_DRIVER_FILES` reproduces the failure. Vulkan loader aliases must be
  absent, not serialized or assigned with empty values: an empty authoritative
  `VK_DRIVER_FILES` overrides the pinned ICD.
- The 2D launchd plist and the later Vulkan web/GUI launch commands now retain
  the canonical ICD while omitting empty loader, layer, and DYLD aliases.
  Their caller guards use set-presence checks, so even an exported empty alias
  is rejected before launch. Contract coverage preserves that boundary with
  empty-value probes and asserts the empty launch assignments remain absent.
- After this fix is committed and pushed, perform only an incremental
  `--pure-simple` exact-HEAD refresh, rebuild through the trusted builder, and
  run the third and final Vulkan 2D live cycle. If it does not pass, retain the
  exact receipt and stop this session rather than starting a fourth cycle.

### 2026-07-27 final Vulkan 2D cycle checkpoint

- The loader-alias repair was reviewed, rebased over current `origin/main`, and
  pushed as `a15386a9b3`. The exact pushed revision completed the incremental
  `--pure-simple` refresh without Cargo/full bootstrap: Stage 2 SHA-256 is
  `7c1741d1436b69ece2f4187b5c3ca2402bfaf794e00cb829b95b7581d1a8e1b4`
  and Stage 3 SHA-256 is
  `eaabd9743415e12d7de32d18a18eb2d4e415833792b96abfd7e37f03c6ad26a5`.
  Stage 3 sanity/provenance and trusted-build manifest admission passed.
- The third and final live cycle verified the Apple M4 MoltenVK device/driver
  and advanced beyond ProcessingIR to Stage 5, then stopped with
  `runtime-font-validation-failed`. No fourth live attempt is permitted in this
  session.
- Read-only diagnosis found the pinned Bungee asset is tracked at
  `assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf` with the expected
  118,996-byte size and SHA-256
  `c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f`,
  but that path was not materialized in the isolated sparse worktree used by
  the live run. The harness sets `SIMPLE_ASSET_ROOT` to that sparse root, so
  `engine.load_font` receives a missing physical path and the Stage 5 guard
  fails before rendering/capture/events.
- Next session, materialize the tracked Bungee asset directory in the isolated
  authority (or add an equivalent fail-fast prepared-host asset preflight),
  verify the exact file hash there, rebuild only if source changes, and start a
  fresh bounded Vulkan 2D live cycle. Do not claim vector-font/300-DPI or later
  web/GUI/WM lanes complete from this failed receipt.

## Ownership and Stop Conditions

| Lane | Owner | Merge rule |
|---|---|---|
| Host Vulkan web/GUI/font provider | Primary rendering agent | Merge only after live device/capture/event PASS. |
| Host/QEMU 2D Vulkan/Metal/SIMD comparison | Existing local agent | Review committed evidence; do not absorb its dirty worktree. |
| Host WM/compiler deployment | Primary rendering agent | Avoid bootstrap unless essential; host PASS precedes QEMU WM. |
| Final verification | Highest-capability primary reviewer | Review all sidecar findings and issue final PASS/FAIL. |

- Verify each acceptance criterion at most once per session.
- Stop after three fix/verify cycles for one feature and record the exact
  failure.
- Do not accept CPU mirrors, upload-only receipts, synthetic handles, static
  screenshots, or source checks as GPU proof.
- Do not claim the goal complete until every required lane has authoritative
  live PASS evidence.
