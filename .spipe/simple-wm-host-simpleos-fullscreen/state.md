# Feature: simple-wm-host-simpleos-fullscreen

## Raw Request
$sp_dev harden simple wm, full screen and windows mode on host. simple os full screen mode. let it use simple gui of internal windows rendering and object rendering for taskbar and top title bar. make it pure simple lane. simple gui, simple web, simple 2d rendering backed. fix any fake. resarch local codes first. impl with smaller model with detail guide and reviews.

## Task Type
feature

## Refined Goal
Harden the production Simple WM so host windowed and fullscreen modes and the SimpleOS fullscreen desktop render the same interactive internal windows, taskbar, and top title bar through the pure-Simple shared GUI, Simple Web, and Simple 2D rendering stack without demo-only or fabricated evidence paths.

## Acceptance Criteria
- AC-1: A production host launcher enters windowed mode, toggles to native fullscreen, returns to the prior window geometry, and preserves compositor window, focus, and taskbar state across both transitions.
- AC-2: A live SimpleOS QEMU boot owns the full framebuffer and renders the shared WM desktop at the detected display size, with fullscreen internal-window maximize/restore behavior proven from real input/state transitions and framebuffer captures.
- AC-3: Host and SimpleOS frames contain multiple real compositor-managed internal windows plus an interactive taskbar and top title bar, including visible title text and window controls, rendered from shared production scene/object models rather than fixture-only markers.
- AC-4: Window content and chrome route through the documented pure-Simple Simple GUI, Simple Web, and Simple 2D backend boundaries; production entrypoints do not substitute Rust-seed execution, host HTML screenshots, fixed QEMU responses, or hardcoded pixel evidence for target rendering.
- AC-5: Pointer and keyboard interactions cover focus, drag, minimize, taskbar restore, maximize/fullscreen, and fullscreen exit without losing window geometry or z-order; focused automated tests exercise the shared state transitions.
- AC-6: Capture evidence validates nonblank rendered pixels, bounded title/taskbar geometry, readable title glyphs, distinct window surfaces, and changed/restored frames for host windowed/fullscreen and SimpleOS fullscreen lanes, failing closed when runtime or capture dependencies are absent.
- AC-7: Focused checks and SPipe scenarios prove production entrypoint wiring and backend provenance, contain no placeholder passes or fake implementations, and generate operator-readable mirrored manuals under `doc/06_spec`.
- AC-8: Final review checks architecture/detail design, requirement traceability, performance of startup and representative frame/interaction paths, environment/process facade compliance, and freshness of matching `doc/07_guide`, `doc/06_spec`, feature/layer expert, SPipe skill/agent, and evidence-wrapper documentation.

## Scope Exclusions
Physical-board display evidence and unrelated SimpleOS driver completion are excluded; SimpleOS runtime proof is QEMU framebuffer evidence unless a board lane is explicitly selected later.

## Cooperative Review
- Lower-model sidecar lanes: local production-path inventory; fake/fixture/evidence audit; focused implementation tasks after architecture assigns disjoint files.
- Merge owner: primary Codex agent (`/root`).
- Final reviewer: primary normal/highest-capability Codex agent after sidecar output and focused verification.
- Shared interfaces: `HostDisplayMode`, `HostDisplayTransitionPhase`, `HostSurfaceGeometry`, `HostSurfaceState`, `WmSceneRevision`, `WmContentFrame`, `WmRenderMetrics`, `SharedWmRenderInput`, existing `SharedWmScene`, and the existing backend-first `shared_wm_scene_render_to_backend` compatibility API.
- Manual flow helpers: `step("Launch the production WM in a host window")`, `step("Toggle the host surface to fullscreen and restore it")`, `step("Boot SimpleOS into its framebuffer desktop")`, `step("Interact with internal windows and taskbar chrome")`, and `step("Validate captured pixels and backend provenance")`.
- Setup/checker helpers: reuse or refine the canonical host launch/capture and SimpleOS QEMU fullscreen evidence wrappers identified by research; no duplicate wrapper may be introduced without design justification.
- Fail-fast placeholders: every unimplemented scenario/helper must use `assert(false)` or `fail(...)`; no `pass_todo`, constant-success assertion, fixed marker response, or synthetic capture is acceptable.
- Generated-manual review owner: primary Codex agent.

## Research Summary
### Existing Code
- `src/lib/common/ui/window_scene.spl` and `window_scene_draw_ir.spl` provide the shared internal-window/taskbar model and backend-neutral object renderer.
- `src/os/compositor/host_compositor_entry.spl` is the production host WM but has no host display-mode/fullscreen state.
- `src/os/desktop/shell.spl` and `shell_baremetal.spl` bypass shared objects with an explicitly fake direct overlay.
- Existing host and SimpleOS fullscreen lanes are demos with incomplete provenance and interaction evidence.

### Reusable Modules
- `SharedWmScene`, `TaskbarModel`, `shared_wm_scene_render_to_backend`, `HostCompositor`, `simple_web_window_renderer`, and the Winit facade.

### Domain Notes
- Host fullscreen must be reversible platform surface state, separate from internal-window maximize; resize/scale events determine the actual render viewport.

### Open Questions
- NONE; user selected Feature A and NFR Target 1.

## Requirements
- REQ-1 (AC-1): Production host WM owns reversible windowed/borderless-fullscreen state and preserves internal compositor state — area: `src/os/compositor/`, `src/os/hosted/`.
- REQ-2 (AC-2): SimpleOS full-desktop mode uses detected framebuffer state and input-driven internal maximize/restore — area: `src/os/desktop/`, `examples/09_embedded/simple_os/`.
- REQ-3 (AC-3/4): Shared scene objects render real titlebar/taskbar/window content through Simple GUI, Web, and 2D boundaries — area: `src/lib/common/ui/`, `src/os/compositor/`.
- REQ-4 (AC-5): Host and QEMU inputs prove focus, drag, minimize/restore, maximize, and fullscreen exit with exact state restoration — area: compositor tests and system specs.
- REQ-5 (AC-6/7): Evidence is dynamic, semantic, provenance-recorded, and fail-closed with no placeholder/source-only passes — area: `scripts/check/`, `test/03_system/`.
- REQ-6 (AC-8): Startup/frame/interaction performance and documentation freshness are release gates — area: plans, guides, reports, and verification.

<!-- sdn-diagram:wm-fullscreen-dependencies -->
```sdn
feature "production WM modes" {
  depends_on "SharedWmScene"
  depends_on "Simple Web artifacts"
  depends_on "Simple 2D backend"
  adapts_to "host Winit surface"
  adapts_to "SimpleOS framebuffer"
}
```

## Architecture

### Module Plan
Host surface state is added to `host_compositor_entry.spl` and translated by `hosted_entry.spl`; host `HostCompositor` and SimpleOS `DesktopShell`/`WmService` remain their sole mutable authorities; revisioned `SharedWmScene` projections render shared chrome/taskbar with common-owned Simple Web content artifacts; SimpleOS replaces its fake baremetal overlay.

### Dependency Map
Host and SimpleOS adapters depend on common-owned scene/content/metrics contracts. The existing common executor's dependency on `CompositorBackend` is preserved but not expanded; Web adapters produce common-owned frames, preventing a new common-to-os cycle.

### Decisions
- Separate host display fullscreen from internal-window maximize.
- Model asynchronous fullscreen request/acknowledgement/failure/timeout with nonce rejection and rollback.
- Delete substitute demo/fake scene ownership from production paths.
- Correlate input, state, capture, backend, and executable provenance.

### Public API
`HostDisplayMode`, `HostDisplayTransitionPhase`, `HostSurfaceGeometry`, `HostSurfaceState`, `WmSceneRevision`, `WmContentFrame`, `WmRenderMetrics`, `SharedWmRenderInput`, the preserved backend-first renderer API, and distinct `shared_wm_scene_render_context_to_backend`.

### Requirement Coverage
REQ-1 host adapter; REQ-2 SimpleOS adapter; REQ-3/4 shared renderer; REQ-5/7 evidence; REQ-6 inputs; REQ-8 specs/manuals.

<!-- sdn-diagram:wm-state-architecture -->
```sdn
"Host surface" -> "HostCompositor" -> "SharedWmScene"
"SimpleOS framebuffer" -> "DesktopShell" -> "SharedWmScene"
"SharedWmScene" -> "Draw IR chrome + Web content" -> "Simple 2D backend"
```

## Phase
arch-done

## Implementation Progress
- Host state contract: `HostDisplayMode`, asynchronous transition phases, saved geometry, nonce validation, resize/scale acknowledgement, timeout/failure rollback; 3 focused scenarios passed.
- Production hosted adapter: F11 native borderless toggle, resize/scale/move acknowledgement, x/y/w/h restoration, compositor resize, timeout rollback, and close cancellation; focused facade/contract checks passed.
- Common render contract: authoritative numeric revisions, typed Simple Web content frames, shared DPI metrics, rich executor, fail-closed frame validation, and exactly one bounded model-backed taskbar; common executor reached 10/10 focused scenarios.
- Host renderer: production fallback uses content-only Simple Web frames with stable content revisions and authoritative running/tray/clock taskbar objects; no fabricated pinned-process items.
- SimpleOS shell: production baremetal loop renders the live compositor projection, authoritative taskbar model, and validated Simple Web content frames; failed launches no longer create overlay-only windows.
- SPipe contracts/manuals: host fullscreen (7 scenarios, 0 stubs), SimpleOS fullscreen (6, 0), and performance (10, 0) are generated; render-provenance spec exists but its manual still needs generation.
- Host internal maximize now preserves an explicit pre-maximize rectangle, reserves the shared top/taskbar bands, and restores exactly; production evidence rejects unsupported maximize.
- Production SimpleOS F11 now enters through `Compositor` PS/2 input, is consumed once by `DesktopShell`, mutates the focused live surface, renders through Engine2D, and emits sequence-correlated IRQ/state/frame markers.
- The QEMU wrapper now boots `gui_entry_desktop.spl`, derives scanout address/stride from guest evidence, accepts any real focused window ID, and requires maximize/restore to target the same window.
- Open: live host capture, successful production QEMU capture, NFR measurements, pure-Simple native-build convergence/provenance, compatibility API cleanup outside production entrypoints, and final verification.

## Log
- dev: Created state file with 8 acceptance criteria (type: feature).
- research: Merged three sidecar audits, documented 6 mapped requirements, and wrote feature/NFR options.
- requirements: User selected Feature A + NFR Target 1; final requirement files replace option documents.
- arch: Designed shared-scene host/SimpleOS architecture, UI/detail design, test plan, and five implementation lanes.
- design-review: Resolved renderer API collision, dependency direction, mutable authority, async transition, scanout, DPI, revision, performance-method, and executable-spec blockers from two independent reviews.
- impl: Landed and primary-reviewed common render contracts plus host transition state and production F11 adapter slices; focused checks pass but local tool reports Rust bootstrap-seed provenance.
- impl: Added Winit position restoration, content-only Web frames with stable revisions, single authoritative taskbar object rendering, and replaced the production SimpleOS fake overlay loop with live compositor projection.
- specs: Added fail-fast host, SimpleOS, render-provenance, and performance SPipe scenarios; generated host/SimpleOS/performance manuals with zero target stubs.
- impl: Replaced the QEMU wrapper's legacy demo entry with the production desktop, added exact SimpleOS internal maximize/restore state, and corrected stale tests that inspected only `gui_entry_engine2d.spl`.
- verify: Scoped source checks and shell syntax passed. A single pure-Simple production native-build using `bin/release/aarch64-apple-darwin-macho/simple` made no observable progress for four minutes and was terminated under the runaway guard; no QEMU boot or capture occurred.
- verify: The verified stage3 pure-Simple compiler then built the production kernel successfully (`587 compiled`, 35.8 MB ELF, 95s); its cached rebuild compiled 6 modules and reused 581.
- qemu: Three bounded cycles failed closed before rendering because stdvga mode readback returned `device_id=0 width=0 height=0`. Real port-I/O symbols and PCI `1234:1111` presence were confirmed. The owner now uses QEMU's documented aligned `0x1d0` word data port; live confirmation is deferred by the three-cycle cap.
- qemu: A further bounded audit proved both generic Simple and direct runtime port probes return zero and enabling PCI command decode does not change it. The temporary direct probe was removed. The production owner now discovers PCI BAR2 and stages QEMU's PCI-native flat Bochs MMIO registers at `BAR2+0x500`, with hardware readback and BAR0 scanout ownership; live confirmation is deferred by the turn's three-cycle cap.
- host: Pure stage3 exposed a reserved-identifier mismatch (`on`) and then linked an invalid artifact after skipping 12 modules and generating 107 stubs. The identifier is fixed, the evidence wrapper now deletes/rejects incomplete native builds, and optional backend pattern bindings were replaced with shared backend readback plus explicit raw-buffer ownership. Live rebuild is deferred by the host lane's three-cycle cap.
- qemu: PCI diagnostics proved stdvga discovery and decode are valid (`device=1`, BAR0 `0xfd000000`, BAR2 `0xfebf0000`). Disassembly then proved entry-module scalar `val`s were weak zero-return functions, so PMM bounds and requested BGA mode were zero. Entry hardware values are now local immediates and the compiler defect is recorded. The next run reached PMM and exposed ignored `--cpu x86-64-v1`: Cranelift emitted BMI2 `shlx`, faulting baseline `qemu64`; the evidence target now explicitly declares `qemu64,+bmi2` pending compiler repair.
- host: Entry-owned lowering failures are cleared. Cranelift compiles 367 modules with zero file failures, but 32 unresolved stubs remain. The wrapper rejects them. The next build is staged with entry-only closure, typed constant casts, and the canonical native runtime archive path; live confirmation is deferred by the host cap.
- qemu: `qemu64,+bmi2` still faulted on `shlx`; QEMU `max` allows PMM/VMM to complete and reaches PCI/MMIO. BAR2 readback currently faults and returns stable undefined values because `vmm_init` builds but does not activate its 4GB identity map. `vmm_activate()` is now explicit in the production entry. BGA hardware conversions use typed casts; live confirmation is deferred by the three-cycle cap.
- host: The runtime archive increased unresolved stubs and was removed. An isolated host cache reduced the stable unresolved set to 23. `HostWmHandle` no longer imports SimpleOS `WmService`; it owns only `HostWmLoopState`. Evidence file I/O now calls the direct runtime facade rather than pulling generic VFS/path/glob modules. The next isolated build will measure the reduced closure.
- qemu: The stable undefined BAR2 values were traced to the documented freestanding MMIO test-mode hazard: `_mmio_test_mode` is not reliably initialized false, and the production entry omitted `mmio_disable_test_mode()`. It now disables test mode before PMM/device access and activates the VMM CR3 before BAR access. No fourth QEMU run was issued.
- host: A fresh isolated cache produced the smallest honest set so far: 260 compiled, zero failed, 23 unresolved stubs. Generic evidence I/O dependencies were then removed; the next turn will rebuild once to measure the direct-runtime closure.
- qemu: Live execution after disabling test mode exposed a second stage3 ABI defect: passing `PhysMemManager` by value corrupted `bitmap_addr` to `-122`. PMM bitmap operations now cross helper boundaries with scalar addresses. The attempted confirmation reused a stale kernel because the wrapper watched only the entry timestamp; dependency-wide freshness is now mandatory before evidence.
- host: `HostWmLoopState` plus an isolated cache removed SimpleOS service ownership, but the honest gate still reports 23 unresolved runtime/source stubs. Direct evidence I/O is staged for the next isolated rebuild; no stubbed artifact is retained.
- host: The direct-runtime evidence I/O rebuild completed with 260 modules, zero failed files, and the same 23 unresolved symbols. The fail-closed wrapper deleted the 13.9 MB linked candidate and recorded `production-native-build-incomplete`; no launch or capture was attempted.
- qemu: A fresh isolated build proved scalar bitmap helpers alone were insufficient because stage3 also corrupts module-global `PhysMemManager` aggregate state. PMM operational state now uses scalar globals and exposes aggregate snapshots only at the public boundary. Focused source checks pass, but the local `bin/simple` identifies itself as the Rust bootstrap seed, so the result is syntax evidence only. Live QEMU confirmation remains deferred by the three-cycle cap.
- qemu: Entry-only discovery now avoids unrelated `src/lib` parse failures while `SIMPLE_LIB=src` resolves the true transitive closure. A real `mmio_disable_test_mode()` owner replaced the prior weak no-op and was confirmed as a strong ELF symbol. The next live fault moved into VMM's first table allocation: its unused `PhysMemManager` by-value parameter still corrupted the stage3 call frame. Production now uses scalar-only `vmm_init_from_global_pmm(0)`; source checks pass and live confirmation is deferred by the three-cycle cap.
- host: Compositor method numbers now live in `common.window_protocol.compositor_methods`, removing the production compositor's userlib protocol dependency. A clean stage3 measurement compiled 271 modules with zero failures but retained the exact same 23 unresolved stubs, proving the compiler emits unreachable directory/module code beyond that import edge. The candidate was deleted and the entry-closure compiler defect is tracked separately.
- qemu: Three bounded cycles isolated two further stage3 boundaries. `PageFrame?` was tagged `Some` while its enum payload was zero, so PMM raw allocation/free now operate directly on scalar physical addresses and VMM consumes them without optional structs; the repeated-fault log fell from 578 KB to 804 bytes. The remaining two traps are Limine HHDM/RSDP optional parsing in generic early init, but this target is direct multiboot/QEMU with scalar bounds. Production now calls `arch_x86_64_direct_boot_init()`, retaining fault, per-CPU, CPUID topology, and syscall setup without fake Limine state. Source checks pass; live confirmation is deferred by the cap.
- qemu: Direct architecture bootstrap is now live-confirmed with no Limine traps. Direct serial phases prove hardware MMIO selection, optimized scalar PMM, and scalar VMM construction all return; the guest stops only when activating the new CR3. VMM operational PML4/HHDM authority now uses scalar globals across hub/copy/address-space paths. ELF inspection proves PTE constants are correctly initialized. Scalar PML4[0]/PDPT[0]/PD[0] probes are staged for the next bounded run; no fourth run was issued.
- qemu: Page-table probes proved a valid chain (`root=0x14004000`, `pml4e0=0x14005007`, `pdpte0=0x14006007`, `pde0=0x83`). The legacy `RuntimeValue` CR3 helper decoded the raw root by shifting right three; explicit raw CR3 primitives fix that ABI mismatch. Live execution now reaches dynamic scanout, framebuffer Engine2D, input, compositor, and shell initialization. The evidence target omitted its required FAT32/NVMe app media and then faulted in `SharedFat32Driver.stat`; target and wrapper now attach the canonical x86_64 fixture. `FramebufferDriver.from_scanout_raw` removes another corrupted struct-by-value boundary. The fault-storm guard caps serial evidence at 1 MiB. Live confirmation is deferred by the three-cycle cap.
- qemu: With canonical NVMe media attached, live boot proves device grant, direct sector transfer, and FAT32 geometry (`bps=512`, `spc=8`, `reserved=32`, `fats=1`, `fat_size=129`, `root=2`) plus scratch DMA allocation. The direct mount now returns bool, avoiding a corrupted `Result<bool,text>` payload. The next fault is the fixed `VERSION.TXT` path entering legacy tagged C string decoding. A numeric FAT 8.3 root/SYS version probe now performs the same real directory and file reads without text equality/case helpers; source checks pass and live confirmation is deferred by the cap.
- qemu: The numeric version probe is linked, but its first directory read still enters the runtime panic/string decoder before producing a marker. The remaining operational scratch buffer was a module-global `SharedDmaBuffer` aggregate. FAT boot scratch address, physical address, and length are now scalar-owned; validity checks, directory scans, and raw byte copies use those scalars, and only the NVMe submission receives a freshly constructed local descriptor. Source checks pass; live confirmation is deferred by the three-cycle cap.
- qemu: Three bounded runs live-confirmed scalar FAT traversal through `/VERSION.TXT`, `/SYS/APPS/BROWSMF.SMF`, and `/SYS/APPS/HELLOSMF.SMF`; Browser Demo starts at cluster 33 and Hello World at cluster 32. Shell and Editor payloads are absent from the canonical fixture, so readiness correctly failed closed before process launch. The staged production set is now Browser Demo, Hello World, and Clang (`CLANGSMF.SMF`), all backed by canonical registry entries and compositor-owned process surfaces. Engine2D, mouse bounds, compositor dimensions, and framebuffer evidence now consume trusted scanout scalars instead of corrupted `FramebufferDriver` aggregate fields. Source checks pass; live confirmation is deferred because the QEMU three-cycle cap is exhausted.
- qemu: Three further bounded cycles live-confirmed Browser Demo cluster 33, Hello World cluster 32, Clang cluster 79, required payload caching, valid 1024x768 scalar framebuffer state, and clean explicit compositor construction. The former `Compositor.new(fb, keyboard, mouse)` call had no linked owner and entered a generated panic stub; production now uses `Compositor.with_backends` with the persistent Engine2D backend and a real PS/2 `InputBackend`. The next live fault was a hosted manifest scan from `DesktopShell.init()`. Production now stages `init_baremetal()`, which initializes WmService and the canonical launcher without re-entering hosted VFS, and successful baremetal launches immediately materialize process-owned surfaces. Source checks pass; the next boot is deferred by the three-cycle cap.
- qemu: Three bounded cycles live-confirmed `init_baremetal()` removes the hosted manifest fault and reaches direct Browser Demo spawn. Calling the C export as a Simple `extern` returned tagged `-14`; production now imports the native Simple syscall bridge and uses scalar app-ID dispatch. That exposed the next aggregate boundary: `resolve_executable_bytes()` enters `AppEntry` alias traversal, faults, and requests a corrupted 175 MB allocation. A dedicated numeric boot-app byte cache now lives in the kernel app registry, is populated only from the real FAT reads for IDs 1/3/12, and feeds syscall 13 before aggregate alias lookup. This retains the installed scheduler returned by process creation and creates no synthetic PID. Source checks pass; live confirmation is deferred by the three-cycle cap.
