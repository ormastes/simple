# macOS Vulkan/Metal and SimpleOS QEMU Rendering Completion

Updated: 2026-07-25

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

## Ownership and Stop Conditions

| Lane | Owner | Merge rule |
|---|---|---|
| Host Vulkan web/GUI/font provider | Primary rendering agent | Merge only after live device/capture/event PASS. |
| Host/QEMU 2D Vulkan/Metal/SIMD comparison | Existing local agent | Review committed evidence; do not absorb its dirty worktree. |
| Host WM/compiler bootstrap | Primary rendering agent | Do not race another bootstrap writer; host PASS precedes QEMU WM. |
| Final verification | Highest-capability primary reviewer | Review all sidecar findings and issue final PASS/FAIL. |

- Verify each acceptance criterion at most once per session.
- Stop after three fix/verify cycles for one feature and record the exact
  failure.
- Do not accept CPU mirrors, upload-only receipts, synthetic handles, static
  screenshots, or source checks as GPU proof.
- Do not claim the goal complete until every required lane has authoritative
  live PASS evidence.
