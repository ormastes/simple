# Agent Tasks: WM Glass Theme on Host and SimpleOS

## Shared Contract

Authority and interfaces are fixed: `ResolvedThemePackage`, derived
`ThemeRenderSnapshot`, existing `SimpleTheme` adapter, `WmChromeColors`,
`SharedWmScene`, `DrawIrComposition`, `Engine2D`, and canonical x86_64
`gui_entry_desktop.spl`. No lane may invent a registry or renderer.

Manual steps and fail-fast text are fixed by the system-test plan. Missing
helpers use `fail("wm glass theme evidence not implemented")` or `assert(false)`.

## Implementation Lanes

1. Package/snapshot lane: typed parsing, SHA-256 manifest/material identity,
   `theme-sync compile-to-spl` generation, and generated-source diff review
   (`theme-sync diff` is SDN-only).
2. WM/bootstrap lane: full projection, hosted startup and canonical SimpleOS
   generated-snapshot installation.
3. Web/Draw IR lane: package CSS wiring, computed-style/accessor repair,
   Engine2D glass lowering and focused regressions.
4. Evidence lane: extend canonical host, GUI/Web parity and QEMU wrappers;
   produce correlated semantic/capability/pixel/performance artifacts.
5. Spec/manual lane: executable SPipe scenarios, docgen, capture links and
   traceability review.

The three read-only design sidecars completed architecture, system-test and
GUI/evidence audits. Further lower-model sidecars may own only bounded lanes
above after checking worktree ownership.

## Ownership

- Merge owner: primary Codex agent in `/root`.
- Broad exclusions/done marks: primary only.
- Generated-manual reviewer: primary normal/highest-capability pass.
- Final production-readiness reviewer: primary highest available model after
  all sidecars finish and changes are merged.

## Merge Order

Package/snapshot -> WM/bootstrap -> Web/Draw IR -> evidence -> spec/manual.
Each lane supplies focused passing tests once; the merge owner resolves shared
types and verifies no concurrent unrelated work was absorbed.

## Continuation State — 2026-07-24

Authoritative integration worktree:
`/Users/ormastes/simple/build/worktrees/wm-glass-theme`, created from
`origin/main` at `3721a30541`. The shared root contains unrelated and
overlapping dirty work and remains read-only for this lane.

### Completed and retained

- Theme authority is `aetheric_dark`; package resolution, immutable
  `ThemeRenderSnapshot`, material/source hashes, generated bare-metal snapshot,
  package CSS, RGBA, ordered shadows, backdrop semantics, and named
  solid-material fallback are implemented.
- Canonical x86_64 SimpleOS evidence uses
  `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`,
  `engine2d_wm_frame_executor.spl`, OVMF, QMP input, and independent
  `pmemsave`; legacy `wm_entry.spl` is not evidence.
- The CSS-scan guest fault was reduced to Rust HIR result provenance:
  `text.split()` omitted `[text]`, while `trim`, `trim_start`, and `trim_end`
  omitted `text`. The owner fix and regression
  `inferred_text_predicate_does_not_reuse_unrelated_custom_owner` are present
  in current `main`.
- Retained pre-fix QEMU artifacts and exact diagnosis are recorded in
  `doc/09_report/wm_glass_theme_qemu_postfix2_2026-07-24.md` and
  `doc/08_tracking/bug/simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`.

### Active findings

| Lane | Current state | First unresolved boundary |
|---|---|---|
| Host production WM | SOURCE FIXED; recapture blocked by Wave 0 | fresh hosted startup now installs the registry-default Stitch package through the package-owned snapshot projection (and preserves an explicit prior selection through the native-safe presence/plain-return pair), but no current Wave 0 capsule is admitted; the path must be rebuilt from an admitted capsule before one fresh host capture |
| Host events | SOURCE FIXED; REVIEW ACCEPTED; product proof pending | canonical address/title and page pointer/key/text routes plus UTF-8 click selection and blink scheduling exist; live focus/caret pixels, frame, and post-state receipts remain open |
| Simple Web glass | SEMANTICS IMPLEMENTED; SINGLE-LINE OVERLAY SOURCE FIXED; TEXTAREA SERIES REJECTED; LIVE PROOF PENDING | CPU and Draw IR share transformed/aligned/clipped theme-derived single-line input text plus selection/caret overlays. Three textarea cycles repaired functional behavior statically but remain unintegrated because Draw IR imported the CPU pixel owner and a feature helper declared direct `rt_*` text externs; see `doc/08_tracking/bug/simple_web_textarea_overlay_review_hard_stop_2026-07-27.md` |
| SimpleOS x86_64 QEMU | STATIC PREFLIGHT PASS; BRR2 SOURCE SERIES REJECTED; FRESH BOOT PENDING | legacy render/event command delegates to canonical `gui_entry_desktop.spl`; frozen admission remains blocked, and a fresh BRR2 lane must resolve exact public parser reasons plus the legacy-six-event versus SimpleOS-four-stage requirement/design mismatch before one OVMF capture |
| SimpleOS ARM64 QEMU | SOURCE INPUT PREFLIGHT IMPLEMENTED; BRR2 SOURCE SERIES REJECTED; LIVE PROOF PENDING | generated Aetheric startup and capability-discovered VirtIO-MMIO input wiring exist, but BRR2 cannot yet be admitted as truthful lifecycle evidence; the self-hosted ARM payload and QMP key/pointer/frame/RAMFB evidence remain unavailable |
| Aggregate SSpec | FAIL-FAST BY DESIGN | `require_wm_glass_theme_evidence()` remains a real failure until host and required QEMU rows produce current-source evidence |
| Simple GUI theme handoff | SOURCE FIXED; product proof pending | resolved snapshot now reaches canonical widget Draw IR; 2 bootstrap-driver scenarios pass diagnostically |
| Simple Web theme authority | INITIAL HOSTED HANDOFF SOURCE FIXED; default Web CSS pixel route SOURCE FIXED; REVIEW ACCEPTED; RUNTIME UNVERIFIED | The default `ui.browser.backend.render_frame` pure-Simple route sends request HTML/CSS through canonical layout -> Draw IR -> Engine2D. The hosted production registry uses copied canonical install wire and the ordered `create_with_theme -> theme_ready -> begin_init(themed_html)` state machine. `simple_web_window_renderer` privately decodes the wire and owns exact snapshot CSS/identity projection; no `ThemePackageInstallProjection` crosses a hosted/compositor module boundary. The themed worker rejects HTML before acknowledgement and rejects raw/mismatched init HTML after acknowledgement. Theme readiness matches revision, theme ID, source-manifest hash, and material hash. Cross-site renderer replacement creates a fresh themed generation, performs the exact theme handshake, initializes canonical empty themed HTML without publishing that bootstrap frame, and only then resumes the saved navigation permit. Final Sol review accepted the source/test contract. Live runtime/capture evidence remains open because no exact-current provenance-admitted pure-Simple CLI exists. |
| WM glass material projection | SOURCE FIXED; REVIEW ACCEPTED; RUNTIME UNVERIFIED | CPU preserves parent sampling/500/930 opacity; opaque Metal uses session-owned identity and exact per-request receipts; sub-opaque Metal fails before dispatch until a GPU-only delta path exists |
| Runtime theme switching | PROTOCOL/CACHE + K1 + CANONICAL WIRE SOURCE ACCEPTED; K2/CATALOG/PACKAGE/SOURCE-CAPTURE SERIES STOPPED; fail-fast system contract | `ThemeChangedV1`, BrowserBackend cache identity, K1 copied-payload queues, and canonical `theme-package-install-wire-v1` text are landed. K2 exhausted three cycles on cross-architecture registration/entry stability gaps; generated catalog exhausted three cycles on stale active/frame authority; package transactions remain unintegrated; source-capture design exhausted three cycles on the missing cache-owning wrapper and contradictory strict-versus-legacy missing-core semantics. The proposed parent-owned `HostedThemeRuntime` handoff is specified but not source implemented. ThemeService/consumer wiring remains unsafe; see the linked K2, catalog, package, and source-capture blocker docs |

### Hosted runtime handoff source resolution and runtime blocker — 2026-07-30

The listed initial-production handoff constraints were resolved and accepted in
the reviewed source series. They remain invariants for later runtime-refresh
work; they are not evidence of live execution:

- No `ThemePackageInstallProjection` or `ThemeRenderSnapshot` aggregate may
  cross a hosted/compositor native boundary.  The package-wire owner explicitly
  forbids it until its ABI probe is accepted.  Capture one copied
  `(revision, wire_text)` pair and derive needed scalar fields inside its
  owning module.
- The exact snapshot must be resolved from the captured source/registry bytes,
  not re-resolved through `theme_package_render_snapshot`, active-theme globals,
  or alias resolution.  The HTML projection emits the accepted ID verbatim.
- The production primary browser as well as registry windows must use
  `create_with_theme -> theme_ready -> begin_init(themed_html)`.  A raw
  `render("init", browser_initial_html)` is forbidden after the theme gate.
- `theme_ready` validates generation, request, revision, theme ID, source
  manifest hash and material hash.  Mismatch, stale, duplicate, or out-of-order
  acknowledgement sends no init/frame and tears the candidate down.
- Transport admission accounts for the `HTI1` envelope.  A codec-valid 1 MiB
  wire cannot silently overflow the renderer's same-sized payload bound; use
  one explicit greatest-constructible transport limit or a checked bounded
  framing allowance.
- Theme-bound site swap preserves ordinary navigation: restart with the exact
  accepted wire and canonical empty themed HTML, finish the handshake, then
  resume the pending navigation.  It must not fail normal cross-origin swaps as
  `theme-restart-replay-unavailable`.

Focused source evidence now covers projection CSS/attributes and
global-mutation independence; registry and direct-entry ordering;
malformed/oversize and exact identity protocol rejection; worker
no-init-before-theme; primary-browser coverage; and restart/replay
generation/identity coverage. Runtime refresh remains explicitly unavailable.

Current host execution blocker: the canonical candidate pair
`build/bootstrap/full/aarch64-apple-darwin/simple` plus adjacent
`simple.provenance.env` is absent from current `origin/main`. The only located
Stage 4 binary is older, dirty, and lacks its adjacent manifest; deployed
`bin/simple` likewise has no adjacent manifest. Do not use either for tests,
captures, or QEMU admission. A prepared-host owner must first produce and
admit an exact-current non-symlink pair with
`stage4_verify_candidate_provenance`, then run the focused hosted tests once.

### Hosted theme runtime prerequisite — design handoff (2026-07-27)

Shared interface names are fixed for implementation: `HostedThemeRuntime`,
`ThemePackageTransactionStore`, `theme_package_install_wire_v1`,
`HostedWmSession`, `init_host_wm_with_runtime`, `HostedBrowserReplayPayload`,
`theme_init(generation, revision, wire_text)`, `theme_ready`, and
`theme_apply(generation, expected_predecessor_revision, revision, wire_text)`.
The parent hosted process owns one real-mutex store whose sole payload is
`(revision, wire_text)`; it never enters shared `HostWmHandle`/core and is
never constructed per handle. Browser workers are wire consumers only.
`theme_package_install_wire_v1` is immutable `text`, contains no revision, and
is bounded through codec-owned public byte-length/checker APIs against exported
`THEME_PACKAGE_INSTALL_WIRE_V1_MAX_UTF8_BYTES`. Implementations must not
duplicate that literal or add feature-local/direct `rt_*` conversion calls.

| Lane | Scope | Owner/review |
|---|---|---|
| Runtime/store | `create_initial(source_reader, registry_path, requested_id)`, once-captured default/source bytes, initial revision `1`, exact mutex tuple, consecutive changed revisions, explicit unchanged no-op | Implementation sidecar; merge owner `/root` |
| Hosted caller migration | Add hosted wrapper/session; migrate `ui.browser`, `ui.electron`, `ui.tauri`, `ui.tui`, and `ui.tui_web`; explicitly exclude non-rendering `wm_daemon` | Implementation sidecar; merge owner `/root` |
| Worker/frame protocol | Exact init/apply envelopes and ack, explicit browser/WmContentFrame theme fields, parent-owned replay payload, restart/revision fence | Implementation sidecar; independent highest-capability review |
| Consumers | Migrate WM/GUI/Web off sequential globals to one store projection before parent admission and post-commit `ThemeChangedV1` delivery | Implementation sidecar; independent highest-capability review |
| Tests/manual | Focused envelope/bounds/frame/restart/admission checks and generated-manual quality | `N/A` until source contracts exist; final reviewer is independent highest-capability reviewer |

Merge only after the detailed contract in
`doc/04_architecture/wm_glass_theme_host_simpleos.md#hosted-runtime-theme-ownership-proposed-prerequisite`,
`doc/05_design/wm_glass_theme_host_simpleos.md#persistent-hosted-runtime-and-explicit-worker-handoff-proposed-prerequisite`,
and the planned checks in
`doc/03_plan/sys_test/wm_glass_theme_host_simpleos.md#hosted-persistent-theme-runtime-prerequisite-planned`
are satisfied. No lane may retry the rejected package transaction shape,
introduce a global store, or call the worker a file/package owner.

### Historical parallel ownership — completed

1. Sidecar A: theme/CSS/WebIR/Draw-IR and Git-history audit, read-only.
2. Sidecar B: hosted production route and event/capture diagnosis, read-only;
   completed the split-theme finding above.
3. Sidecar C: x86_64/ARM64 canonical QEMU route, media/input/capture audit,
   read-only; completed and proved the ARM64 theme-install/input gaps.
4. Implementation sidecars: Web package CSS authority, WM material projection,
   and Simple GUI widget theme handoff, with non-overlapping source ownership.
5. `/root`: merge owner, host bootstrap regression/fix, compiler preflight,
   documentation, final high-capability review, sync and push.

### Runtime-proof parallel assignments — 2026-07-26

The historical lanes above are completed ownership records, not active proof
claims. The remaining critical work is **TODO 580 (P1)**. **TODO 583 (P3)**
keeps Electron as a postponed optional wrapper and cannot gate the pure-Simple
WM/GUI/Web/Engine2D proof.

All rows use package-owned `ThemeRenderSnapshot`/scalar projections,
`SharedWmScene`, `DrawIrComposition`, `Engine2D`, the production
HTML/WebIR-to-DrawIR owner, and `widget_tree_to_draw_ir`. The five manual
steps are fixed: `Load the Stitch glass theme`; `Render the hosted WM
through the canonical scene`; `Apply glass CSS and widget computed styles`;
`Boot the canonical SimpleOS desktop in QEMU`; `Capture and compare semantic
and framebuffer evidence`.

**Compiler Wave 0 is not currently admitted at `3ed2200828`.** The forbidden Rust seed
hash is `f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc`.
Historical-only pure hash
`277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767` cannot
import the current graph. The reviewed runtime capsule
`02775039b26c80ad5858976ad0761ab331cd6454bee202b6dfb3a25310a19d85` at source
`4e1ddd3afe` is absent and is neither current nor admitted. Its replacement
core-C runtime capsule is independently ACCEPTED at source
`088da06413217edec9454cd0c24de417a8cd5e65`, runtime tree
`3dd0db9de03e225a0e16164e0a52a40cc4774902`, archive
`c4f39c1a74e1979d2680153476199b0d70b626fabb0b01d22cedc4505ca46e74`, and
manifest `5773db91727ce05bde7c100a64ef77206e4b166c1efc36534e7196d2fadf0003`.
This accepts the runtime only, not a compiler. A tracked focused bridge and
live probe now invoke the current `CompilerDriver`, while the fixed bootstrap
API uses the exact three-opt-in predicate and defaults to disabled. The pure
predicate spec and the four-scenario fail-closed admission-preparation contract
pass, and independent high-capability source review ACCEPTS the preparation.
Its manual is
`doc/06_spec/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.md`.
The final bridge micro-cycle remains unspent because no reviewed admission
runner exists and no exact native route has been approved or executed.
The runtime tree remains unchanged at `3ed2200828`, so the accepted runtime
archive is reusable; the compiler and source admission must bind to the newer
revision.

| Wave/lane | Exclusive owner and boundary | Required independent review and admission evidence |
|---|---|---|
| **Wave 0 — compiler capsule / CompileMode transport** | `/root/compiler_capsule_owner` owns the tracked bridge entry, opt-in-sensitive bootstrap option plumbing, compiler admission checker, and accepted runtime-capsule handoff from `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`. It must set `SIMPLE_NO_STUB_FALLBACK=1`; it may not change WM, GUI, Web, Engine2D, or device code. Any source change creates a fresh compiler admission requirement, while unchanged runtime tree/archive identities remain reusable. | Runtime provenance is ACCEPTED in `doc/09_report/wm_wave0_core_c_runtime_capsule_2026-07-26.md`. An independent highest-capability reviewer must still approve an eligible `compile --native` route or classifier-clean pure positional builder, then admit exact source/compiler/runtime/provider hashes and `nm` gates. Required unspent micro-cycle gates: `scripts/check/check-phase2-low-memory-source-reclaim.shs`, `test/03_system/check/phase2_low_memory_source_reclaim_gate_contract_spec.spl`, and `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs` as necessary-only; positive 3 opt-ins/reclaim/`first-free=1`/`alias=0`, negative no-optin false/no-marker, `test/03_system/compiler/native_cli_mode_transport_regression_spec.spl` output `73`, and `test/03_system/compiler/native_cross_module_class_field_layout_regression_spec.spl` output `84`. This excludes the seed and historical hashes above. Follow `doc/08_tracking/bug/bootstrap_low_memory_positional_bridge_circularity_2026-07-26.md` and `doc/08_tracking/bug/native_engine2d_readback_cross_module_field_layout_2026-07-26.md`. |
| **Wave A — theme semantics and parity** | `/root/theme_semantics_owner` owns canonical selected-snapshot propagation and focused GUI/Web semantics. `src/app/ui.browser/backend.spl` is permitted only as the canonical selected-snapshot semantic owner; it must not receive GPU, renderer, provider, readback, or backend implementation edits. | Independent high-capability review verifies the selected package CSS and widget snapshot reach `DrawIrComposition`, and runs/reviews `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` with real cascade/layout plus independent framebuffer evidence. |
| **Wave A — CPU-SIMD host oracle/events** | `/root/cpu_simd_owner` owns CPU-SIMD evidence/checker/report files only; shared Engine2D changes require merge-owner assignment. | Independent high-capability review requires exact scalar/SIMD pixels, focus/pointer/key/text ordered receipts, timing, RSS, and revision-bound artifacts. |
| **Wave B — Vulkan / Metal** | Prepared-host owners separately own only their provider/checker/manifest/report rows; no cross-backend edits. | Each device row has its own independent high-capability review: immutable device/provider/library identity, selected backend, submit/complete, device-origin readback, CPU-oracle parity, ordered events, timing and RSS. |
| **Wave B — x86_64 QEMU** | `/root/x86_qemu_owner` owns only canonical x86 checker, frozen manifest, serial/QMP/`pmemsave` captures and report. | Independent high-capability review requires the admitted Wave 0 capsule, fresh canonical boot, independent capture, themed crop/checksum, ordered input and SIMD receipts. |
| **Wave C — ARM64 QEMU** | `/root/arm_qemu_owner` owns only ARM desktop/QMP checker, frozen manifest, RAMFB/QMP captures and report. | Independent high-capability review requires the same accepted Wave 0 compiler capsule, a self-hosted payload, fresh boot, themed capture/checksum, VirtIO ordering and NEON receipt. |
| **Aggregate/manual** | `/root/wm_evidence_aggregate` owns only aggregate checkers, executable SSpec, manuals, state/plan/report links. | Independent highest-capability final review accepts only revision-bound rows, no placeholder pass, all five manual steps, and retained evidence links. |

Wave order: Wave 0 first; then Wave A lanes may run in parallel; after their
accepted capsule/oracle, Vulkan, Metal, and x86 QEMU may run in parallel; ARM
and aggregation start only from accepted prerequisite rows. An unavailable
host/device records its first missing rung and exact handoff, leaves the row
open, and does not block independent lanes. Owners never self-admit; every
device and QEMU row requires the independent high-capability review above.

### Next execution order

#### Scope decision — 2026-07-26

The critical product lane is the pure-Simple rendering chain:

```text
WM -> canonical GUI widget/scene semantics
   -> Web semantic/layout owner
   -> DrawIrComposition
   -> Engine2D CPU-SIMD / Vulkan / Metal
   -> device-origin capture + ordered input/event receipt
```

Electron is only an optional presentation/evidence wrapper around that chain.
Its live Aetheric render/event/capture run is noncritical and postponed under
TODO 583. The pinned resolver and Aetheric identity/admission hardening are
integrated, but no Electron admission, launch, screenshot, event receipt, or
PASS is required before the critical pure line proceeds.

The pure line stays P1 and open under TODO 580. Execution is postponed only
until a prepared host has the matching device/runtime and an admitted
source-matched pure-Simple compiler; postponement is not completion:

1. Restore the source-matched pure-Simple compiler/runtime/provider capsule.
   Reject Rust seed, fallback, dirty-source, or mutable-provider inputs.
2. Establish the CPU-SIMD exact-pixel oracle and real event sequence on native
   x86_64, then retain the equivalent x86 QEMU and ARM64 QEMU SIMD receipts.
3. Run Vulkan on a prepared Vulkan host and Metal on macOS. Each row must prove
   backend selection, submission/completion, device-origin readback, exact
   parity with the CPU oracle, stable device identity, timing, and RSS.
4. Drive the same Aetheric scene and focus/pointer/key/text sequence through
   WM, GUI, and Web owners; compare dimensions, ARGB, material/font witnesses,
   state transitions, and ordered event receipts across backends.
5. Admit a row only after independent high review; then update the aggregate
   SSpec/manual. A missing backend or host remains explicitly open.

### CPU-composited material sub-lane — SOURCE PREPARED / UNVERIFIED

The shared-owner material slice is limited to the existing styled-RECT Draw IR
path: `window_scene_draw_ir.spl`, `draw_ir_adv.spl`, and the new
`draw_ir_glass_material.spl` helper. `DrawIrCommand.color` remains opaque
`solid_fallback_rgba` for native-safe transport, while existing
`background-color` carries the translucent package request. The helper realizes
a bounded CPU backdrop sample/blur/saturation/alpha-composite path while
retaining existing borders; requested blur `30px` is realized as blur `4px`
with realized blur/saturation/reduction witnesses, `i64` arithmetic, and a
67,108,864-pixel output/working cap.
The subsequent W1-W4 slice extends this existing material owner through the
canonical Simple Web cascade, Draw IR, post-execution provenance, and WM
validator. It does not modify GUI, backend-native Vulkan/Metal, capture, event,
or QEMU owners.

Merge owner must obtain independent high-capability source review. The third
cycle had an opaque-material test failure; its reviewed correction has no
post-fix run because the session cap is reached. The mode-aware Web patch is
source prepared: exact opt-in preserves the material while ordinary or
unsupported modes keep the named fallback. A fresh-session PASS is required
before source acceptance. This slice is only a prerequisite for a later scalar/SIMD
oracle; it cannot
self-admit CPU-SIMD, native Vulkan/Metal, host/QEMU framebuffer, device
readback, input-event, timing, or RSS evidence.

### Web CSS material repair — documentation-first execution plan

| Phase | Status | Owner and file range | Exit condition |
|---|---|---|---|
| W1 semantic retention | Source prepared | Web semantic owner: `simple_web_html_layout_renderer_declarations.spl` and `_core.spl` | Cascaded translucent base, backdrop, radius, and ordered layers survive; named solid fallback is retained separately |
| W2 Draw IR policy | Source prepared | Web Draw IR owner: `_paint_layout.spl` plus focused specs | `DrawIrCommand.color` is opaque fallback; style carries requested and realized CPU material values; missing/incomplete policy fails closed |
| W3 layered CPU material | Source prepared | Engine2D merge owner: `draw_ir_glass_material.spl` and `draw_ir_adv.spl` | Backdrop -> translucent base -> alpha-gradient -> border order has exact pixel oracles and bounded work |
| W4 provenance | Source prepared | Web artifact and shared WM owners: `simple_web_html_layout_renderer.spl`, `simple_web_layout_engine2d_fast.spl`, `simple_web_window_renderer.spl`, `window_scene.spl` | CPU-composited and solid fallback kinds/hashes are distinct and validated end to end |
| W5 evidence | Open | Evidence owner, then independent highest-capability reviewer | CSS/computed-style/Draw IR/pixel receipts pass; no backend/device claim is inferred |

On 2026-07-27 the current-host adapter audit found that W1-W4 existed below
the producer, but `simple_web_content_render_request_with_theme` had removed the
exact mode from every WM content wrapper. That omission selected the legacy
opaque reducer before the package-owned `.widget-panel` surface could be
admitted. The adapter now restores the exact mode and gives the wrapper a
stable probe id; the generated Aetheric CSS remains the sole owner of the
translucent base, gradient, and `blur(30px) saturate(170%)`. The focused
`wm_aetheric_web_material_spec.spl` follows the production request through
computed Style and Draw IR. Two interpreter attempts reached the 120-second
resource timeout before any assertion (`0 passed, 1 failed`), so W5 remains
open and this checkpoint must not be described as a runtime PASS. A
highest-capability read-only review accepted the strengthened command-level
Draw IR assertions with no remaining P0/P1 source issue.

### Current-macOS Metal material lane

| Phase | Status | Owner and file range | Exit condition |
|---|---|---|---|
| M1 narrow operation contract | Source prepared | Draw IR target and glass execution result owners | Non-Metal targets return unavailable; final readback cannot manufacture a device-material receipt |
| M2 ordered Metal dispatch | Source prepared | `metal_session.spl`, `backend_metal_msl.spl`, `backend_metal.spl` | Optional snapshot/material pipelines compile; snapshot and material run in ordered encoders; completion alone admits `metal-device-glass-v1` |
| M3 Web/WM provenance | Source prepared | Draw IR result, Web material provenance, WM frame validator | Witness/count/target/readback/handle/identity all match; CPU/device kinds cannot be swapped |
| M4 native proof | Open | macOS evidence owner and highest-capability reviewer | Current-source Metal init, device dispatch, device readback, exact pixels/capture, events, timing, and RSS pass |

The embedded MSL source compiles with the installed macOS Metal compiler
(`xcrun -sdk macosx metal`) on 2026-07-27. Simple source checking is not
admissible on this checkout: the deployed architecture binary identifies
itself as the forbidden Rust bootstrap seed, and no bootstrap was started.
M1-M3 therefore remain SOURCE PREPARED / RUNTIME UNVERIFIED until independent
review and an admitted pure-Simple runtime execute the focused specs.

The subsequent one-file mode removal at `28a5b56b59` contradicted the retained
production adapter and full-package Draw IR specs. Source/history review
confirmed that `6b18dcd874` already provides the required `var()` resolution
and exact typed normalization for Aetheric's one linear highlight over its
translucent base. The mode is restored at source, and the production package
spec now also requires Engine2D software execution plus a matching material
receipt. A source-matched pure-Simple run is still required for M4.

The current-host launcher audit separates binary selection from execution
ownership. A deployed self-hosted CLI normally delegates `.spl` execution to
its bootstrap seed sibling. `_cli_driver_binary()` now recognizes the exact
`SIMPLE_NO_BOOTSTRAP_DELEGATE=1` opt-in and keeps execution in-process; absent
the flag, bootstrap/ordinary CLI behavior is unchanged. Launcher and evidence
wrapper integration remains assigned to the active sibling owner and must
require launcher PID == window-owner PID plus source/runtime manifest binding.

Lower-capability sidecars may own W1, W2, and test fixture preparation only
after the merge owner freezes the exact style keys:
`wm-material-request`, `background-color`,
`backdrop-filter-capability`, `backdrop-filter-realized`,
`backdrop-filter-realized-blur-radius-px`,
`backdrop-filter-realized-saturation-milli`, and
`backdrop-filter-reduction-reason`. W3/W4 integration and all done marks require
highest-capability review. No lane may edit the legacy CPU executor into a
second material renderer.

- External compiler/GPU owner: prepared-host operator under TODO 580 and
  `doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`.
- Backend capture contract:
  `doc/03_plan/agent_tasks/engine2d_four_backend_capture.md`,
  `doc/03_plan/sys_test/engine2d_four_backend_capture.md`,
  `doc/04_architecture/engine2d_four_backend_capture.md`, and
  `doc/05_design/engine2d_four_backend_capture.md`.
- WM/GUI/Web contracts:
  `doc/04_architecture/wm_glass_theme_host_simpleos.md`,
  `doc/05_design/wm_glass_theme_host_simpleos.md`, and
  `doc/03_plan/sys_test/wm_glass_theme_host_simpleos.md`.
- Current blocker/evidence reports:
  `doc/09_report/cpu_simd_engine2d_evidence_2026-07-26.md`,
  `doc/09_report/wm_current_vulkan_live_2026-07-26.md`,
  `doc/09_report/macos_vulkan_provider_micro_probe_2026-07-26.md`,
  `doc/09_report/wm_current_metal_live_probe_2026-07-26.md`, and
  `doc/09_report/macos_metal_msl_library_micro_diagnostic_2026-07-26.md`.
- x86 resume command:
  `BUILD_DIR=build/simpleos_wm_fullscreen_evidence SIMPLE_BIN=<admitted-simple> sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
- ARM resume commands:
  `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`, then
  `sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs`.
- Prerequisites: clean revision, classifier-clean pure-Simple compiler,
  runtime/provider hashes, target QEMU plus KVM/HVF/WHPX where native timing is
  claimed, and a frozen build manifest.
- Retained artifacts: compiler admission, commands, manifests, serial/QMP
  logs, framebuffer/device captures and checksums, events, font/DPI/SIMD
  receipts, timing, and RSS.
- Merge owner: `/root`; final reviewer: an independent normal/highest-capability
  reviewer.

2026-07-26 current checkpoint: source/interpreter regression is complete for
theme-package loading (11/11), Web CSS authority (5/5), and retained native
linker policy (15/15). The canonical archive owner repair is integrated, but
native/live rows remain open. The pure WM/GUI/Web/Engine2D line is the critical
priority and resumes on prepared hosts; Electron is noncritical and postponed.
No current native Aetheric producer or Electron proof exists, and neither x86
nor ARM has an admitted compiler/frozen manifest for a canonical QEMU launch.
The external seed-driven x86 job is not admissible evidence. Current details
and remaining gates are recorded in
`.spipe/wm-glass-theme-host-simpleos/state.md`,
`doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`, and
`doc/09_report/aetheric_host_web_gui_readiness_2026-07-26.md`.

2026-07-25 checkpoint: the 16x16 hosted capture is **DIAGNOSTIC ONLY**.
x86 SSE2/static and ARM VirtIO/C preflights pass, but neither launched QEMU.
The historical order below is retained for handoff; postponed rows now execute
only under the external-host ownership above.

1. Focused current-source Rust HIR regression: COMPLETE. The corrected
   name-filtered run passed the intended test (`1 passed; 3346 filtered out`);
   the earlier `--exact` run was rejected because it filtered the test out.
2. Add red-before/green-after bootstrap regressions and:
   - install the resolved host package snapshot before backend/compositor
     creation through a hosted owner helper;
   - install the generated Aetheric snapshot before compositor construction
     through one freestanding-safe helper shared by x86_64 and ARM64 entries.
3. Build one exact-current pure-Simple bootstrap artifact and prove the CSS
   collision object routes inferred text to `_rt_string_starts_with` while the
   custom receiver still routes to `CustomPrefixOwner.starts_with`.
4. Run the focused host wrapper once:

   ```sh
   SIMPLE_BIN="$PWD/<exact-current-pure-simple>" \
     SIMPLE_BIN_SOURCE=wm-glass-theme-current \
     BUILD_DIR="$PWD/build/wm-glass-theme-host-current" \
     REPORT_PATH="$PWD/doc/09_report/wm_glass_theme_host_current_2026-07-24.md" \
     sh scripts/check/check-wm-production-fullscreen-evidence.shs
   ```

5. Only after the object preflight passes, run the x86_64 QEMU wrapper once:

   ```sh
   SIMPLE_BIN="$PWD/<exact-current-pure-simple>" \
     SIMPLE_BIN_SOURCE=wm-glass-theme-current \
     BUILD_DIR="$PWD/build/wm-glass-theme-qemu-x86-current" \
     REPORT_PATH="$PWD/doc/09_report/wm_glass_theme_qemu_x86_current_2026-07-24.md" \
     sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
   ```

   The non-launching x86 ownership/SSE2 preflight must pass first:

   ```sh
   sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs
   ```

6. Build/run the ARM64 canonical desktop after theme wiring:

   ```sh
   SIMPLE_BINARY="$PWD/<exact-current-pure-simple>" \
     SIMPLE_LIB=src SIMPLE_OS_BUILD_TIMEOUT_MS=900000 \
     "$PWD/<exact-current-pure-simple>" os test \
       --scenario=arm64-desktop-engine2d --log=off
   ```

### ARM64 desktop media ownership (2026-07-24)

- Desktop scenarios own `build/os/fat32-arm64-desktop.img`, produced by the
  explicit `desktop-fonts` disk profile.
- The desktop image contains only `/SYS/FONTS`: the 16 pinned production faces
  and their 37 pinned license/metadata/notices companions.
- `arm64-virtio-fat32-smf` continues to own `build/os/fat32-arm64.img` and must
  fail closed when the target ARM64 Simple payload is missing or invalid.
- Non-QEMU acceptance: build the desktop image once, inspect all 53 font bundle
  files plus absence of `/SYS/APPS` and `/SIMPLE.ELF`, then run the focused
  disk/font contract specs.
- ARM VirtIO transport rejects both `FAILED` and `DEVICE_NEEDS_RESET` status
  after `FEATURES_OK` and `DRIVER_OK`. The canonical
  `Arm64VirtioInputBackend` now owns the raw queue, buffers cross-kind events,
  retains key edges, and assigns one sequence to each pointer `SYN_REPORT`
  frame. Typed optional-struct trait dispatch is pinned by a two-vtable native
  fixture (`49 0 73 0`). The live event-ready marker remains fail-closed until
  QMP/RAMFB evidence passes. The source preflight pins every retained
  `REL_X`/`REL_Y` summary and `BTN_LEFT`/`BTN_RIGHT`/`BTN_MIDDLE` edge before
  its `SYN_REPORT` receipt with the same `input_seq` interpolation.

   The ARM input owner is source-wired and keeps UART fallback outside
   production evidence. After the host-first gate, require QMP pointer
   movement/button down/up plus keyboard press/release. Pointer records in one
   `SYN_REPORT` transaction share one guest sequence; every key edge and
   pointer frame must correlate device, truthful poll, WM state, later frame,
   and distinct RAMFB capture evidence.
7. Replace the aggregate fail-fast helper only when it reads and validates
   production artifacts; then regenerate and review the manual.

### Admission rules

- A Rust seed, Stage 2/3 compiler used as a product runner, compatibility WM
  entry, source marker, screenshot without framebuffer provenance, synthetic
  event receipt, CPU mirror labeled as device readback, stale capture, or
  selector-free CSS rewrite cannot pass.
- Do not run QEMU before the focused compiler/object preflight is green.
- Each acceptance criterion is verified once per current source state, with at
  most three fix/verify cycles.

## Integration checkpoint — 2026-07-24 21:15 KST

Authoritative merge worktree is now
`build/worktrees/wm-integration-current`. The earlier continuation path above
is historical.

- Host: the fresh full bootstrap proved provider selection and reached process
  launch. Cycles 2 and 3 then failed before the first readiness receipt with
  `field access on nil receiver`; the cycle cap is reached and no host
  pixels/events are admitted in this session.
- Web/GUI root cause: Aetheric family defaults styled `widget-*` primitives but
  omitted their production WM aliases. `.wm-window`, `.wm-titlebar`, and
  `.wm-title` now inherit the package-owned border/radius/blur/font/weight
  tokens. Git history traces the incomplete defaults to the 2026-07-04 theme
  import, while later panel CSS added only color/shadow aliases.
- Web evidence: the static modern-preview fixture is removed from this lane.
  Production `simple_web_content_render_request_with_theme` now owns document
  generation; Simple CPU-SIMD and Electron outputs bind HTML, observation,
  backend/readback, dimensions, pixels, screenshot, binary, and source hashes.
  A live Electron adapter exposes the exact DOM over the canonical
  `simple ui snapshot/surface/find/act/history` protocol. Native producer
  generation passes with the current manifest/material hashes; full admission
  remains pending because the exact-current Stage 4 CLI build was killed
  during the 546 KiB Web source parse and no deployed `simple ui` driver was
  produced.
- x86_64: canonical F11 press/release and fullscreen delegation remain
  source-correct. Missing retained artifacts now fail the integration spec
  instead of passing through absence assertions. Live QEMU remains host-gated.
- ARM64: deterministic desktop media and failed/reset-needed VirtIO checks are
  integrated. The typed canonical VirtIO adapter is wired into
  `Compositor.with_backends`; live QEMU remains host-gated.
- ARM64 review: repeated REL_X/REL_Y aggregation, per-frame reset, all three
  button edges, shared input sequence, and raw-before-SYN receipt order are
  pinned. High-capability review accepts the implementation. Focused specs
  were invoked once but the deployed runner failed before loading them on
  missing `rt_process_run_bounded`; live QMP/RAMFB evidence remains the
  production blocker.
- Web compiler blocker: native scalar `.to_i64()` can bind imported
  `LogLevel.to_i64`. Three bounded compiler fix/review cycles were rejected on
  custom/trait dispatch, inferred-text parse semantics, and direct-native
  float conversion. The candidate series is not integrated. Resume from
  `doc/08_tracking/bug/native_primitive_to_i64_ufcs_collision_2026-07-24.md`;
  do not spend the final producer cycle before its native semantic fixture
  passes.

## Review checkpoint — browser frame and aggregate returns

- Commit `f43a30fc30` is present in `main`, but its production-frame claim is
  **rejected pending correction**. It replays the Simple pixel artifact into a
  canvas and compares an Electron raw bitmap to the same bytes, so it proves
  replay rather than the production browser presentation path. The raw bitmap
  comparison also assumes platform-specific BGRA ordering. Its event, payload,
  latency, and CSS-animation checks remain useful, but its legacy opaque color
  assertions are not glass-theme visual acceptance.
- The correction must retain the real DOM font proof, exercise the canonical
  browser presentation adapter on a separate surface, canonicalize captured
  pixels through a portable format, bind executed probe and adapter source
  hashes, and reject a same-size pixel mismatch. A highest-capability review
  must accept the correction before the frame-binding row is admitted.
- The first correction candidate (`dadc731bda`) is also rejected and not
  integrated. Its producer and validator used different RGBA channel weights,
  its changed-pixel test changed only checksum metadata, its receipt could pair
  self-consistent forged HTML with the current adapter hash, and its
  `production_simple_frame_bound` name overstated a dimensions/nonempty-pixel
  check. The final correction must deterministically regenerate HTML from a
  hashed adapter-request preimage and name structural capture evidence
  honestly; it must not claim equality with the independent Simple ARGB
  artifact.
- The final Web correction (`cc95569c4f` plus `79b8969831`) is rejected and
  not integrated. It fixed the checksum, real-byte tamper test, request
  preimage, and structural naming, but did not require byte-exact canonical
  request serialization, omitted part of the adapter serialization contract,
  left receipt-selected artifacts without regular-file/canonical-directory
  guards, and interpolated receipt strings into renderer JavaScript without
  JSON quoting. The implementation-cycle cap is reached.
- Main therefore rolls back `f43a30fc30`'s rejected pixel-replay equality claim
  and the later downstream assertions that treated it as accepted evidence.
  The earlier live DOM font frame, event, timing, animation, receipt, and
  independent Simple composition checks remain. Portable adapter-frame binding
  stays fail-closed and must resume in a fresh scoped session from the final
  review findings rather than from either rejected candidate.
- Glass acceptance comes from the package-loaded Aetheric producer, not the
  legacy event fixture. Require the inactive `.wm-window` computed surface to
  retain `rgba(31, 31, 33, 0.8)`, a linear gradient,
  `blur(30px) saturate(170%)`, the `rgba(139, 144, 160, 0.2)` border, `18px`
  radius, and the black/translucent-white shadow layers. Focus must change the
  border to `rgba(193, 198, 215, 0.3)` and retain black/accent shadow layers.
  The titlebar requires `rgba(14, 14, 16, 0.72)` with the same blur, border,
  and radius; the title requires `rgb(228, 226, 228)`, Manrope, and weight
  `650`. Aetheric `.widget-button` uses an accent-backed translucent gradient
  and `12px` radius; traffic-light RGB literals are not Aetheric evidence.
- The first aggregate-return registry candidate (`d6f68cb9406b`) is rejected
  and not integrated. Its bare-name/global `MirType` registry missed the actual
  flat entry-closure path, confused `Named` classes with enums, aliases, and
  custom primitives, retained callee-local `SymbolId` values across modules,
  collided same-named functions, and never reset between builds.
- The active aggregate correction must reset once per top-level build,
  preregister every flat and non-flat module before entry lowering, key by the
  canonical emitted qualified function identity, and resolve a stable declared
  type descriptor through the caller symbol table and normal MIR type
  lowering. Admission requires a native flat entry-closure fixture with aliased
  imports, two same-named factories returning different aggregate types,
  projected fields, a forwarded return, and a method, plus same-process A→B
  reset evidence.
- Aggregate cycle 2 (`4e0c6123cc`) is rejected and not integrated. Although it
  fixed the flat preregistration order, top-level reset, and stale callee
  `SymbolId`, it discarded generic type arguments, left method identities
  collision-prone, normalized descriptor owners asymmetrically, simulated
  aliases/custom primitives, bypassed other top-level lowering paths, and used
  registry-unit simulations instead of real flat MIR/native/reset evidence.
  Cycle 3 is the final compiler implementation cycle for this session.
- Aggregate cycle 3 (`d59ef76462`) is rejected and not integrated. Direct
  lowering still re-registered and emitted non-method functions under bare
  names, static-method identity diverged, alias expansion depended on importer
  symbols and declaration order, later lowering paths wrote after the claimed
  single prepass, and skip-MIR could retain stale registry state. Its unit spec
  still simulated registry state; the full fixture was not invoked by a test
  or used to compare real flat call/definition ABI signatures.
- The isolated Cranelift construction itself completed (`3 compiled, 0
  failed`) before the stop arrived, producing a 29 MB candidate CLI and an
  unrun fixture in `/tmp/simple-cycle2-owner-cycle2/build/cycle3/`. These
  artifacts are diagnostic only: architecture review rejected their source,
  the candidate `test` invocation reported `unknown command 'test'`, and
  nothing was run, admitted, deployed, or retried. The aggregate compiler
  implementation-cycle cap is reached; resume only in a fresh scoped session
  from the cycle-3 review findings.
- A separate root-worktree full-CLI build is active and is not authoritative
  for this lane because its source state is unrelated and potentially dirty.
  Do not deploy over live MCP. Start the isolated exact-current CLI build only
  after the accepted compiler candidate is integrated and the unrelated build
  releases the native-build resources.
- The later exact-current isolated bootstrap at `719f610e3c` built its own
  Rust seed/runtime and passed Stage 2 and Stage 3 sanity, but Stage 4 corrupted
  lexer/token state while parsing the ordinary `elif` chain in
  `src/lib/nogc_async_mut/cli/log_modes.spl`. No full CLI was produced and the
  build must not be repeated in this session. Continue from
  `doc/08_tracking/bug/stage4_selfhost_log_modes_lexer_state_corruption_2026-07-24.md`;
  the deployed stale runner remains unchanged.

## 2026-07-26 No-Bootstrap Evidence Audit

- W1-W4 is remotely saved at checkpoint branch
  `codex/wm-glass-theme-host-simpleos-20260726`; source review is accepted,
  runtime verification remains open.
- The generic `bin/release/simple` wrapper fails its deployed-runtime identity
  probe. The architecture-specific Mach-O binary also emits the forbidden
  Rust-seed warning when it executes current source. Neither is admissible.
- x86_64 and AArch64 QEMU plus firmware are installed. Static x86 WM/QMP/SSE2
  preflight passes, but live x86 evidence lacks an admitted current
  kernel/disk and `grub-mkstandalone`.
- ARM live evidence lacks the admitted kernel, FAT disk, manifest, and frozen
  source receipt. Building those is intentionally postponed because it
  requires the long attested build and crosses the user's no-bootstrap limit.
- Existing 16x16 hosted captures, stale native WM binaries, generic
  SIMD/Metal evidence, and generic Vulkan event captures are diagnostic only:
  none binds the current Aetheric shorthand, Draw IR witness, backend receipt,
  device readback, and native event sequence into one proof.
- Resume W5 on a host with an admitted deployed pure-Simple runtime and current
  guest artifacts. Do not substitute the Rust seed or stale diagnostic images.

## 2026-07-27 Environment Routing

Current macOS work remains active as `MAC-WM-GLASS-LOCAL-001`. Windows, Linux,
x86 QEMU, and ARM QEMU execution are postponed to their required hosts through
four explicit P0 feature requests:

`doc/08_tracking/feature/wm_glass_cross_host_evidence_requests_2026-07-27.md`.

The fail-closed external-host handoff, including its exact prepared-host
commands and receipt requirements, is recorded in:

`doc/08_tracking/feature/wm_glass_cross_host_evidence_requests_2026-07-27.md`.

External rows remain required and must not be counted as exclusions or PASS.

The 2026-07-27 Metal device-glass source checkpoint has completed independent
highest-capability review with no P0/P1 findings. The reviewer required exact
straight-alpha parity for translucent destinations and sampled live-device
comparison with the scalar CPU oracle. Runtime admission remains open because
the available local executable identifies as the forbidden Rust bootstrap
seed; no bootstrap was started.

## 2026-07-27 Current Implementation and Runtime Handoff

Current macOS implementation work is active; this does not mean macOS runtime
evidence is available. The authoritative Aetheric Stitch glass source contract
is restored, and the renderer material/Engine2D software-receipt path is
tested. The Metal device sample/translucent CPU-oracle checkpoint exists,
including straight-alpha parity for translucent destinations. Commit
`b7b4c241dc` adds opt-in `SIMPLE_NO_BOOTSTRAP_DELEGATE=1`, allowing the
admitted launcher path to avoid delegating source execution to a bootstrap
driver.

Live macOS GUI evidence remains **RUNTIME UNVERIFIED** until a trusted,
source-matched self-hosted runtime is admitted and demonstrates matching
launcher/window-owner identity with the required native receipts. No
seed/bootstrap execution may satisfy that gate; old orphan
`SimpleGui -> simple_seed` processes are inadmissible diagnostic residue.

The manifest-v3 source boundary separates the canonical full CLI GUI driver
from Stage 3 and keeps admitted hashes authoritative. The Endpoint Security
candidate now collects exec/fork/exit lineage with sequence-gap and finalization
checks, runs the driver from an immutable private snapshot in a process group,
and uses a non-circular unavailable/prepared/admitted policy. Independent
highest-capability static review found no remaining P0/P1 source issue in the
bounded pathname-TOCTOU repair. A fresh clean-revision verification then passed
the Swift `-lbsm` compile/link/self-test, builder self-test, focused
boundary/full-CLI/GPU contracts, both direct-env modes, and the explicit
`--exec-verified` unavailable-policy branch with exit 125 and
`policy-not-admitted`. Independent highest-capability review accepted the
source verification. The clean direct-env results are scope guards, not
non-vacuous implementation coverage. Policy remains `status=unavailable`; no
source verification result is live admission or GUI evidence.

The canonical SimpleOS desktop entries for x86_64, ARM64, and RV64 call
`install_generated_simpleos_wm_theme()` before compositor and first-frame
construction. Their live framebuffer/input evidence remains assigned to the
prepared-host rows; source ordering is not a QEMU PASS.

Linux/Windows, x86/ARM QEMU, and native-board runs remain postponed to prepared
hosts and fail closed. They are still required, never PASS by postponement;
retain and use the exact commands and path references in the existing
cross-host request and handoff contract above.

The superseded manifest-v2 gate bound the widget/Web inputs but admitted its
Stage-3 compiler as the strict GUI driver. Manifest v3 replaces that mismatch
with a separately provenance-bound canonical full CLI GUI driver, normalized
history verifier, and fail-closed tracked trust-root gate. The collector
candidate and immutable-snapshot lifecycle now exist, and the fresh
source-verification session plus independent review passed. Promotion is still
deliberately separate: first provision the approved signing identity and
Endpoint Security entitlement and review a `prepared` policy that pins source,
toolchain, argv, and environment while output/manifest hashes remain
unavailable. Then build and review the collector candidate; only its exact
output and manifest hashes may enter a separate `admitted` policy. The
canonical full-CLI driver is produced and admitted only after collector trust.

## 2026-07-27 Metal Receipt and GUI Driver Follow-up

The Metal device-material receipt is now GPU-only. Normal mirror mode rejects
the device-only operation before dispatch, leaves its CPU mirror unchanged,
and must take the explicit CPU fallback path. A successful device receipt no
longer invokes the CPU glass oracle behind the provenance boundary.

Receipt `801caf` is therefore retained solely as a GPU-only Metal
device-operation checkpoint. It is not a native widget/web capture, event
receipt, GUI admission, or product PASS, and it cannot promote any other row.

GUI-driver admission source is repaired, and the Endpoint Security collector is
now a source-verified fail-closed candidate. Live artifact production and
capture still cannot begin because the policy stays unavailable. The security
owner must provision the approved signing team and Endpoint Security
entitlement and obtain independent review of a source/toolchain-pinned
`prepared` policy whose output hashes remain unavailable. Next it must build
and review the reproducible collector candidate, separately admit its exact
output/manifest hashes, and only then produce and admit the exact canonical
full-CLI driver before live evidence. No admissible current pure-Simple GUI
runtime exists; the native harness and every seed/delegating driver remain
inadmissible.

## 2026-07-27 Hosted Event and QEMU Contract Review

The committed hosted browser route now keeps address/title commands on the
canonical compositor owner and page pointer, key, text, and active-animation
commands on `HostedBrowserRendererProcess`. A scoped source contract binds
those branches, semantic targets, external-frame re-submission, and private-
route exclusions. Independent highest-capability review accepted that static
contract. It does not close live AC-7 focus, pointer, move/maximize, key/text,
timing, animation-frame, or post-state evidence.

The later input rendering repair removes a hardcoded placeholder gray and uses
one `InputTextPaintPlan` for both CPU pixels and Draw IR, preserving computed
transform, RTL, alignment, vertical placement, Aetheric/theme foreground, and
the intersection of input content and ancestor clips. Engine2D scopes and
restores that clip while retaining the canonical `draw_text`/font-batch route.
Address-bar Backspace validates the whole UTF-8 draft, deletes exactly one
valid trailing scalar, and leaves malformed byte sequences unchanged. Exact
behavioral source specs cover valid Korean/`é`, malformed/truncated input,
theme/layout/clip parity, clipped pixels, and clip restoration. Independent
highest-capability source review accepted the repair. The admitted runtime was
unavailable, so no live browser, caret/selection, framebuffer, timing, or RSS
PASS is inferred.

The follow-up single-line input overlay keeps stable author-id/body-relative
layout keys across serialization, maps validated UTF-8 source boundaries
through password masking, transform expansion, RTL, alignment, and horizontal
reveal, and emits clipped selection/text/caret order through both Engine2D
executors. Readonly controls remain selectable but immutable; disabled controls
cannot focus or emit hit/overlay geometry. Prevented pointer defaults preserve
selection, chrome focus clears page selection/blink, and the worker schedules
500 ms caret edges only while appropriate. Exact behavioral specs cover
anonymous reparse identity, multibyte click placement, computed selection
color, center/right hit alignment, preventDefault, chrome blur, invalid UTF-8,
blink visibility/cancellation, and view retention/reset. Independent
highest-capability static review accepted commit `63205f9e8f`. No admitted
runtime was available, so this is not an executed browser PASS; textarea
caret/selection and all live pixel/event/timing/RSS evidence remain open.

Independent highest-capability QEMU review rejected a source-complete claim.
The entries install the generated theme before the first frame, and ARM already
has strong frozen-source/NEON/QMP/VirtIO/RAMFB checks, but remaining P1 gates
are recorded in
`doc/08_tracking/bug/wm_glass_qemu_evidence_contract_p1_2026-07-27.md`.

A subsequent isolated frozen-admission lane exhausted its three-cycle cap and
was not integrated. Its final behavior gate stopped before launch because the
attempted unlinked fake-QEMU snapshot execution through macOS `/dev/fd/7` was
denied. No fourth attempt, live QEMU, bootstrap, integration, or push ran.
The x86 route also correctly identified that mutable vvfat cannot satisfy the
required final-byte contract. Resume only with a supervised, provenance-bound
host C `posix_spawn`/fdset helper and a builder-owned raw immutable ESP image;
Darwin exposes no usable `fexecve`. Rejected commit `6108a099f5`, uncommitted
final-cycle work, and the later incomplete helper candidate `e98275fca0` are
not source evidence. The helper candidate exhausted its own three-cycle cap
without process supervision, QEMU closure admission, wrapper wiring,
raw-profile isolation, or executable fake-QEMU behavior tests. No QEMU guest,
bootstrap, integration, or push ran. A future helper may claim honest same-UID
race resistance only; malicious same-UID admission remains unavailable without
a privileged OS-immutable store. It must validate environment and exclusively
reserve the receipt before spawn, kill-and-wait every post-spawn failure, and
bind its exact no-follow source snapshot, actual compiler/SDK/argv/sanitized
environment, verified signatures/dependency closure, and concurrency-safe
output/receipt publication.
In particular, x86 must publish and consume frozen admission with no external-
ELF bypass, prove SSE2/scalar parity and ordered damage/frame receipts, while
ARM direct-`-kernel` firmware is N/A; it must bind theme/material/backend/
fallback identity and finalize
events only after the correlated frame. Both rows still require timing/RSS.
Active sibling changes in those files remain separately owned and must be
re-reviewed only after their owner commits them.

## 2026-07-27 Source-only Delta Audit

Three later commits improve prerequisites but do not admit a host or QEMU
runtime:

- `e0daceb361e88583be711dc97584e469b518e505` preserves negative filesystem WM
  coordinates through the app-process contract. It is a narrow source repair,
  not native input-backend, capture, or live event evidence.
- `bd7f63edb8597d6b5ae51a873f3f91a7fc634bfe` reserves the complete x86_64
  desktop heap before page-table allocation. It fixes the triple-fault path
  where the enlarged heap overlapped active PMM page tables. It changes no ARM
  source and does not alter frozen admission, BRR2, K2, event ordering,
  timing/RSS, or theme-before-first-frame requirements.
- `67024e9c0a51722812f295cfd7170364f2f031d2` improves Stage 4 HIR import
  resolution, and `a7ac45b72f5d894d416482bf4d2f31e0d7378bbf` restores a missing
  runtime-contract source input, but neither produces an admitted
  source-matched compiler/runtime artifact. Receiver/module-key failures and
  the generated `_dispatch_function` code-generation split remain.

No safe incremental QEMU run follows from these changes. Retained x86
ELF/admission sets predate the heap fix and lack its marker; rebuilding only a
kernel and combining it with their disk/manifest would violate frozen
admission. ARM is unaffected. Resume x86 with one fresh, source-matched admitted
OVMF capture that proves the reserved heap covers the entire heap, the VMM root
lies outside it, and PMM/VMM startup survives. Until then host runtime, x86
QEMU, and ARM QEMU rows remain postponed rather than passed.

## 2026-07-30 scoped continuation

The first current-host increment repairs two source regressions without a
bootstrap: restore the native-safe `ThemeMaterialSnapshot` wire serializer and
populate `ThemePackage.semantic` from the installed package CSS. Exact
Aetheric semantic-color tests discriminate CSS extraction, and an independent
highest-capability review accepted the corrected patch. Focused static gates
are required before integration; runtime and live-capture rows remain
unverified while the external source-matched incremental build is unresolved.

The remaining host work is divided into bounded follow-ups:

1. Admit CPU, software, CPU-SIMD, and Vulkan presentation targets to honest
   CPU-composited glass, while keeping Metal as the only device-glass path and
   AUTO/generic GPU on solid fallback.
2. Preserve ordered Web shadow layers and per-corner radius through typed
   lowering, with negative-control tests.
3. Resume QEMU only after the `Result<(), E>` parser/capsule blocker is fixed
   and a current admitted artifact exists. x86 currently ends in
   `guest-render-fault`; ARM has no current admitted ELF/FAT/capture.

Merge owner remains `/root`; each bounded implementation receives independent
highest-capability review before push.

### CPU-composited glass result

Follow-up 1 is source-complete and accepted: concrete CPU, software, CPU-SIMD,
and Vulkan presentation targets request the bounded Engine2D CPU compositor.
Metal alone requests device glass; AUTO/generic GPU stay on opaque solid
fallback. A deliberately translucent fallback fixture proves that raw command
pixels remain opaque while the CPU material's computed background remains
translucent. Producer metadata records a requested target only; the Engine2D
execution result owns actual realization.

Runtime/capture evidence remains open because no current source-matched runtime
is admitted. Follow-up 2 (typed ordered Web shadows and per-corner radius) is
next; follow-up 3 (QEMU) remains postponed behind the capsule blocker.

### Web box-effects hard stop

Follow-up 2 reached the three-review-cycle cap and is not committed or pushed.
All architecture/module/typed-schema/corner/work-cap findings were corrected,
but the final review found one P1 in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_box_effects.spl`:
`_e2d_box_legacy_shadow` must enforce offset `-65536..65536` and blur
`0..65536` before its call-safety check. A fresh scoped session must add tests
for accepted `65536` and no-op offset `+/-65537`/blur `65537`, then perform one
independent review. QEMU remains separately postponed.

### Web box-effects fresh follow-up

The fresh bounded follow-up is accepted. Legacy shadows now apply the exact
inclusive offset `-65536..65536` and blur `0..65536` contract before geometry
validation or narrowing. Direct render tests prove both boundaries remain
admitted and that offset `+/-65537` or blur `65537` cannot paint even when
their geometry would otherwise land onscreen.

This source increment is eligible for scoped static integration. Runtime and
capture evidence remain unverified. The QEMU lane stays assigned separately
and must not reuse an externally owned or stale live VM/artifact.

### Hosted event-to-present receipt repair

The 2026-07-30 current-history audit found an independent host production
blocker: consolidation commit `f119f8b712` removed
`host_wm_input_record_presented`, its receipt fields, and its behavior test,
while `src/os/hosted/hosted_entry.spl` retained the import and live call after
every accepted frame presentation. The hosted WM therefore could not build to
the native event/capture boundary, and no semantic event could close with a
truthful presentation receipt.

The scoped repair restores accepted semantic-event to host-presentation
correlation, including completion time, input-to-present latency, cumulative
present count, and skipped-frame count. Failed, invalid, stale, or regressive
updates must preserve the last accepted receipt. The focused unit owner is
`test/01_unit/os/desktop/hosted_wm_evidence_spec.spl`.

This is source repair only. Static review cannot promote host pixels, native
events, timing, RSS, browser rendering, or either QEMU row. Host execution
still requires one admitted exact-current pure-Simple CLI; QEMU remains owned
by its delegated plan and is not executed by the merge owner.

### Current CLI admission attempt — 2026-07-30

The isolated current-main normal deploy correctly refused to run because the
Rust seed and runtime archive were absent. This made one
`bootstrap-from-scratch.sh --full-bootstrap --deploy` essential rather than an
optional broad check. The first Stage 3 run exposed the missing seed-only
`std.alloc.sffi` import in `compiler.hir.hir_types`; the accepted repair now
declares the already-linked `rt_dict_contains` runtime symbol directly and its
focused source regression rejects only the removed import form. A second full
bootstrap reached **Stage 2 PASS**, then Stage 3 exited 139 while compiling the
self-hosted CLI. The bounded log ends in HIR-expression lowering and supplies
no source-level diagnostic. No third retry was run. The bootstrap correctly
refused seed fallback, so no CLI manifest, runtime test, host capture, or QEMU
artifact was admitted. Continue from the Stage 3 native SIGSEGV diagnosis;
do not reuse the generated Stage 2 binary as verification evidence.

### GUI root material projection

The 2026-07-30 GUI audit found that the correct selected snapshot reached
`UISession`, but the widget producer discarded its material and emitted only
flat rectangles. The scoped source repair makes
`common.ui.theme_draw_ir_material` the common WM/GUI material-style owner,
adds one opaque initializer and one eligible root material request, and removes
the hardcoded hosted GUI frame seed. Nested controls deliberately remain plain
semantic rectangles; no private GUI raster path or nested backdrop sample was
introduced. Focused source contracts cover the root-only request, initializer,
primitive roots, fallback/backend metadata, and neutral renderer seed.

Independent Sol review accepted the final source diff. Runtime pixels, native
host events, device receipts, and QEMU parity remain unverified until an
admitted exact-current pure-Simple CLI is available.
