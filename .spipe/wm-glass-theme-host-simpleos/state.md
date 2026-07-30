# Feature: WM Glass Theme on Host and SimpleOS

## Raw Request
`$sp_dev check wm on host and simple os on qemu. and fix unwired and unimpled and bug. specially simple gui and simpwl wm does not apply theme properly which created from stitch in glass theme like mac fill. research current files and git history check theme apply plan if web renderer does not apply css properly fix the bugs in root cause. do things in pherallel and use smalll model agents with detail guide and higher model review.`

## Task Type
bug

## Refined Goal
Make the canonical hosted and SimpleOS/QEMU window-manager paths apply the Stitch-derived macOS-like glass theme faithfully through Simple GUI and Simple Web, fixing missing wiring, unimplemented behavior, and CSS/rendering defects at their owning layers with retained semantic and framebuffer evidence.

## Acceptance Criteria
- AC-1: The selected Stitch-derived glass theme has one authoritative theme identity and produces explicit semantic values for desktop fill, window fill, title bar, border, radius, shadow, translucency/alpha, text, and active/inactive state.
- AC-2: The production hosted WM renders that theme through `SharedWmScene -> DrawIrComposition -> Engine2D`; structured Draw IR evidence and a nonblank framebuffer prove the requested computed styles reached the submitted composition without a compatibility renderer or unrelated synthetic frame.
- AC-3: The canonical SimpleOS desktop entry (`gui_entry_desktop.spl`) uses the same theme identity and canonical frame route; a fresh QEMU boot provides retained serial provenance plus an independent `pmemsave` framebuffer crop showing the themed desktop and window chrome.
- AC-4: Simple GUI widgets and WM chrome preserve the theme's background/fill, alpha, radius, border, shadow, typography, and active/inactive state instead of silently falling back to hard-coded defaults.
- AC-5: Simple Web's production HTML/WebIR-to-DrawIR path applies the CSS properties needed by the glass theme; focused semantic/layout assertions and independently rendered pixels fail on omitted or incorrectly parsed/cascaded properties.
- AC-6: Every discovered unwired or unimplemented theme path is either implemented at its canonical owner and covered by a focused regression, or remains explicitly failed/blocked with a concrete bug record; no placeholder pass, synthetic handle, private parallel renderer, fixture bypass, or raw runtime shortcut is accepted.
- AC-7: Host interaction evidence proves focus, pointer down/up, move/maximize, keyboard/text input, positive `performance.now()` delta, at least two animation frames, CSS animation application, and a post-action semantic state change with `blur_or_tolerance=false`.
- AC-8: Host and QEMU evidence record exact binary/source revision, viewport, backend and fallback state, framebuffer/readback provenance, checksum, artifact paths, and the first unavailable GPU-proof rung; screenshots alone are insufficient.
- AC-9: Relevant research, requirements, architecture, detail design, system-test plan/spec/manual, agent-task plan, operator guide, and tracking records are current and trace every AC to implementation and evidence.
- AC-10: Focused specs, host checks, QEMU checks, generated-manual quality review, direct-runtime guards, generated-spec layout guard, and final high-capability review pass once without stubs, dummy assertions, or stale evidence.

## Scope Exclusions
No new drawing IR, private widget renderer, font atlas/cache, Engine3D shortcut, platform-specific theme fork, or broad unrelated compiler/runtime repair. Compiler/runtime bugs discovered as prerequisites remain in scope only through the smallest owner-level reproducer and fix or a concrete blocking bug record.

## Cooperative Review
- Bounded sidecar lanes: (1) current-code/docs/history and theme-plan archaeology, (2) hosted WM/Simple GUI/Web renderer and CSS gap audit, (3) SimpleOS canonical entry/QEMU evidence audit. Model selection is delegated to the available agent runtime; these lanes are intentionally narrow enough for lower-capability execution.
- Merge owner: primary Codex agent in `/root`.
- Final reviewer: primary normal/highest-capability Codex agent; sidecars cannot accept done marks, exclusions, generated-manual quality, or release-blocking evidence.
- Shared interfaces: `SharedWmScene`, `DrawIrComposition`, `Engine2D`, the existing authoritative theme model discovered by research, and the existing production HTML/WebIR-to-DrawIR and `widget_tree_to_draw_ir` owners. No sidecar may invent replacement interfaces.
- Manual steps: `Load the Stitch glass theme`; `Render the hosted WM through the canonical scene`; `Apply glass CSS and widget computed styles`; `Boot the canonical SimpleOS desktop in QEMU`; `Capture and compare semantic and framebuffer evidence`.
- Setup/checker helpers: reuse or extend the canonical hosted WM/theme checker, `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`, and the canonical SimpleOS QEMU framebuffer wrapper identified by research; provisional new helpers must be named `check-wm-glass-theme-host-evidence.shs` and `check-wm-glass-theme-simpleos-qemu-evidence.shs` only if no owner exists.
- Fail-fast placeholders: any temporarily introduced checker/spec helper must call `fail("wm glass theme evidence not implemented")` or `assert(false)` until real semantic and framebuffer assertions replace it.
- Generated-manual review owner: primary Codex agent after sidecar findings are merged.

## Runtime Boundary Decision
- runtime_need: none established during goal refinement.
- facade_checked: pending research of existing UI, renderer, QEMU, file, process, and environment facades.
- chosen_path: `reuse-facade`.
- rejected_shortcuts: raw `rt_*` aliases, fixture-only theme branches, backend field pokes, compatibility WM renderers claimed as canonical, synthetic GPU/readback evidence, and hard-coded browser pixels.

## Research Summary

- Current theme authority: `config/themes/theme.sdn` selects `aetheric_dark`.
- Conflicting history: commit `2248995c72` introduced hard-coded light Aqua WM
  defaults without promoting them to the package registry.
- Hosted root causes: the production theme-to-WM adapter is unwired; Simple Web
  emits hard-coded CSS; RGBA, shadow, gradient, and backdrop-blur semantics are
  lost or incomplete before Draw IR.
- SimpleOS authority: canonical evidence must use x86_64
  `gui_entry_desktop.spl` and `engine2d_wm_frame_executor.spl`, not legacy
  `wm_entry.spl`.
- Existing QEMU framebuffer evidence is nonblank and interactive but lacks a
  resolved theme fingerprint and structured glass witnesses.
- User selected Feature A and NFR A: registered `aetheric_dark` is the single
  authority; host/SimpleOS require exact semantic parity with
  capability-declared pixel evidence.

## Phase
implementation-source-prepared-web-cpu-material-verification-blocked

## Log
- dev: Created state file with 10 acceptance criteria (type: bug); defined bounded cooperative lanes, canonical interface constraints, evidence steps, and fail-fast policy.
- research: Consolidated three parallel read-only audits; wrote local/domain
  research and selectable feature/NFR options. No implementation choice was
  inferred because repository policy requires user selection.
- requirements: User selected Feature A + NFR A. Promoted the selections to
  final requirement documents and deleted all option artifacts.
- design: Three bounded read-only reviews converged on explicit package-to-
  snapshot bootstrap projection, existing canonical render owners, and
  capability-declared semantic/pixel evidence. Added architecture, GUI/TUI,
  detail design, system-test plan, agent tasks, and fail-fast executable spec.
- implementation: Added a content-addressed renderer-neutral theme snapshot,
  exact generated bare-metal snapshot, host and SimpleOS first-frame WM
  installation, package-owned Simple Web CSS/cache identity, RGBA parsing,
  multi-shadow/backdrop semantic preservation, and named solid-material raster
  fallback. Focused source checks and generator execution passed.
- verification: Canonical hosted capture stopped before rendering on the
  existing self-hosted `HostedCaptureFramebuffer.put_pixel` lowering defect;
  recorded `hosted_wm_capture_put_pixel_lowering_2026-07-19.md`. Canonical QEMU
  verification was not started because another repository lane owns a live
  QEMU process. Fail-fast system evidence remains intentionally unresolved.
- qemu-actual: Launched the canonical x86_64 `gui_entry_desktop.spl` wrapper
  in isolated `build/wm_glass_theme_qemu_actual`. Cycle 1 exposed hosted
  `theme_package` execution in bare metal and faulted before the first frame.
  Fixed the boundary by embedding composed CSS in the generated snapshot and
  using the installed snapshot before any hosted package fallback. Cycle 2
  reached production readiness and identified the expected Aetheric taskbar
  clock-oracle change. Cycle 3 PASS retained independent QMP pmemsave pixels,
  matching guest/host font-region SHA-256, nonblank 4K frames, correlated F11
  maximize/restore, 20,043,014 changed bytes, and exact restored checksum.
- visual-review: Inspection of retained PASS images found the Simple Web
  Engine2D heuristic still matched WM class names inside CSS and overpainted
  content with legacy `#2050A0/#182230`. Removed that heuristic for WM content,
  routed it through real selector/layout rendering, and mapped content fill and
  text to package variables. Source checks pass. Per the mandatory three-cycle
  cap, this post-review pixel correction must be re-captured in a fresh session;
  the retained PASS report predates only this final content-color correction.
- continuation-2026-07-24: A fresh cache proved the July 20 striped framebuffer
  predates the current renderer source. Directly routing the full Aetheric CSS
  into the bare-metal selector/layout path remains unsafe. Added explicit
  `solid-material` background/foreground metadata from the installed
  `ThemeRenderSnapshot`; Simple Engine2D now strips package selector CSS only
  for that declared fallback and renders the original body through the real
  layout/text painter. Browser engines still consume the full Stitch CSS.
- continuation-2026-07-24-tooling: Resolved concurrent rebase markers in the
  canonical wrapper and `gui_entry_desktop.spl` to the retained Aetheric
  taskbar hash `addf76...`. The deployed CLI is stale on
  `rt_process_spawn_guarded`; today's pure-Simple Stage-3 compiler
  (`6175ea...`) successfully built the patched kernel.
- continuation-2026-07-24-qemu: The old Stage-3 compiler entered SimpleOS but
  faulted in `sfnt.find_table` before a frame. Two launches of the fresh
  Stage-3 kernel then failed identically in OVMF/GRUB with #GP
  `RIP=FFF1000000000000` before `[BOOT32]`. Recorded
  `simpleos_wm_uefi_pre_kernel_gp_fresh_stage3_2026-07-24.md`; no current-source
  framebuffer exists. Stopped at the mandatory third cycle.
- continuation-2026-07-24-host: The patched x86_64 entry closure compiled
  `658` files with `0` failures using pure-Simple Stage 3. The focused hosted
  spec reached the test daemon but timed out after its one permitted run.
  Working and staged direct-env/runtime guards pass, `git diff --check` passes,
  no conflict markers remain, and `doc/06_spec` contains zero executable
  `*_spec.spl` files. Runtime host assertions and current-source QEMU pixels
  remain unproven.
- continuation-2026-07-24-review: Highest-capability review rejected the
  selector-free fallback document because it discarded canonical package CSS
  and affected hosted Engine2D. Removed that rewrite. Renderer-neutral
  fallback metadata remains on the WM root while the original full document
  flows through the canonical CSS/layout owner.
- continuation-2026-07-24-ovmf: Added the EFI GOP/video modules and text
  payload already proven by the canonical readiness wrapper. Three fresh
  launches now reach font registration, shell/app startup, compositor
  software fallback, FAT32, and a 3840x2160 ARGB scanout; the former
  pre-kernel GP is resolved.
- continuation-2026-07-24-span-blocker: All three launches stop on the first
  CSS scan. RIP is in `ByteSpan.starts_with` (previously `equals`) with return
  address in `_css_scan_rules_simple`. A direct comparison experiment moved
  but did not fix the fault and was reverted. Recorded
  `simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`; the QEMU
  cycle cap is exhausted and pixel evidence remains blocked.
- sync-2026-07-24: Fetched GitHub and confirmed `main@origin` matches local
  `main` at `058f1338` (parser parity fix). The 85-file dirty tree contains
  WM/theme, unrelated `llm_caret`, shared, and external lanes, while another
  agent owns a live full-bootstrap process; no mixed or unverified working-copy
  commit was pushed.
- sync-continuation-2026-07-24: Fetched GitHub with the `$sync` workflow;
  `main@origin` and the working parent match at `52d0c716f0d1`, and the tracked
  file-count guard remained `105960 -> 105960`. Mixed WM and unrelated
  concurrent-session changes remain uncommitted and were not pushed.
- inferred-text-provenance-2026-07-24: Built exact pure-Simple bootstrap
  compilers from the synchronized tree. QEMU cycle 2 used compiler
  `bc99e6c6...`, built a 658-file kernel with zero failures, reached the
  3840x2160 production scanout, then faulted in `ByteSpan.starts_with` from
  `_css_scan_rules_simple`. Strengthening the fixture from explicit
  `opener: text` to inferred `opener` reproduced a direct custom-owner
  relocation. Three compiler/probe iterations did not clear that relocation;
  the final RED object and exact resume command are recorded in
  `simpleos_wm_freestanding_bytespan_css_scan_fault_2026-07-24.md`. Per the
  hard cap, QEMU cycle 3 and the hosted runtime gate were not run.
- continuation-bootstrap-wiring-2026-07-24: Resumed in the isolated
  `build/worktrees/wm-glass-theme` worktree from `origin/main` at
  `3721a30541`. Read-only sidecars confirmed the host production entry bypassed
  the package snapshot installer and ARM64 never installed the generated
  Aetheric snapshot. Added one hosted owner helper and one freestanding-safe
  SimpleOS owner helper; the host now installs the resolved snapshot before
  backend/compositor construction and uses its desktop fill, while x86_64 and
  ARM64 install the same generated snapshot before compositor construction.
  A focused three-scenario source contract passes diagnostically, but the
  deployed CLI delegates to the Rust seed and is not admissible production
  evidence. Host event receipts, current-source host pixels, x86_64 QEMU
  pixels, and ARM64 framebuffer/input evidence remain active gaps.
- continuation-compiler-check-2026-07-24: The first current-source Cargo
  command used `--exact` and filtered out the intended inferred-text
  regression, so it was rejected as evidence. The corrected name-filtered run
  passed the intended test exactly once: `1 passed; 3346 filtered out`.
- continuation-history-audit-2026-07-24: Read-only history/source review found
  three first-loss owners beyond bootstrap: Simple GUI discards `app.theme`
  before fixed-palette widget Draw IR; Simple Web selects legacy generated
  glass CSS instead of package-resolved CSS; and WM chrome flattens the render
  snapshot to colors before fixed-geometry Draw IR. Runtime theme switching
  also loads tokens without installing/notifying a snapshot. Separate
  non-overlapping implementation sidecars now own the first three boundaries.
- continuation-static-gates-2026-07-24: Working/staged direct-env/runtime
  guards, `git diff --check`, and the `doc/06_spec` executable-layout guard
  pass. The available Stage-3 artifact identifies as a pure-Simple bootstrap
  compiler but has no `check` command; no product runtime claim is admitted
  from it.
- continuation-parallel-fixes-2026-07-24: Three non-overlapping sidecars
  removed the legacy Web CSS authority, passed resolved theme snapshots into
  canonical widget Draw IR, and retained renderer-neutral WM glass identity
  and effect requests in WM Draw IR. Web passed 3 scenarios and widget Draw IR
  passed 2 scenarios using the Rust bootstrap driver; both are diagnostic,
  not product admission. The focused broad window-scene spec timed out at
  120 seconds with no assertion result and is recorded in
  `window_scene_draw_ir_spec_timeout_2026-07-24.md`. No retry was made.
- continuation-input-and-switching-2026-07-24: Host production evidence now
  records distinct real winit/FIFO key-down, key-up, pointer-move,
  pointer-button-down, and pointer-button-up receipts while retaining the
  canonical compositor calls. Six focused scenarios pass diagnostically; the
  product entry check is still blocked on `rt_process_spawn_guarded`. No
  canonical title-command/body-input API exists, so none was fabricated.
  ARM64 QMP input remains blocked before rendering by missing VirtIO-MMIO
  device discovery/eventq/backend/device attachment; a two-scenario system
  contract remains fail-fast. Runtime theme switching remains blocked by a
  missing notification transport ABI; its contract was placed under system
  tests, not the unit suite.
- continuation-exact-bootstrap-and-host-2026-07-24: Rebased to current
  `origin/main` and built exact-current pure-Simple Stage 2/3 with cargo
  disabled and `SIMPLE_NO_STUB_FALLBACK=1`; both sanity gates passed and
  Stage 3 SHA-256 is `6c64561a...`. The three host cycles all stopped before
  launch: first on two missing bridge-build scripts, then twice because the
  native-project linker ignored the wrapper's external runtime providers.
  Added the missing builders, stable provider install names, wrapper
  `SIMPLE_LINK_OBJECTS` wiring, and the matching native-project linker
  implementation. High-capability review rejected the first bridge patch for
  shipping, portability, install-name, proof, injection, and manual gaps. All
  six were corrected; focused Rust regressions now pass (`3 passed; 3348
  filtered`) with a real provider link/run and stub-suppression proof.
  Host cycle cap is exhausted; current-source pixels/events remain unproven.
- continuation-arm64-input-source-preflight-2026-07-24: ARM64 source now
  attaches capability-discovered VirtIO-MMIO keyboard/pointer devices, owns
  modern eventq 0 with strict reset/status/QueueReady/DMA-layout validation,
  observes device-owned used records with acquire ordering, and republishes
  recycled descriptors with release ordering. The desktop reuses shared evdev
  translation, assigns one guest sequence per pointer SYN transaction, and
  emits truthful poll/state/frame markers for pointer frames and both keyboard
  edges. Silent ToggleTheme handling was replaced by an explicit blocker.
  The focused C contract and cross-target C syntax preflight pass; no QEMU ran.
  A full diagnostic build still stops before entry compilation because the
  self-hosted `aarch64-unknown-simpleos/simple` FAT32 payload is absent, so
  live input/pixel evidence remains FAIL-FAST rather than inferred from source.
- integration-checkpoint-2026-07-24: Pushed reviewed Aetheric CSS/WM aliases,
  production Web/UI-access evidence plumbing, fail-closed x86 evidence, typed
  ARM VirtIO input ownership, same-frame pointer receipts, and tightened ARM
  aggregation/reset/order contracts through `9113a77defbd`. High review
  accepts the ARM implementation. Focused ARM specs remain pre-execution
  blocked by the deployed runner's missing `rt_process_run_bounded` extern.
  No QEMU was launched because the host gate remains failed and its
  three-cycle cap is exhausted.
- native-to-i64-review-2026-07-24: The Web renderer link failure is a compiler
  collision between scalar `.to_i64()` and imported `LogLevel.to_i64`.
  Three bounded fix/review cycles repaired receiver reuse but failed
  high-capability review on resolved custom/trait dispatch, inferred-text
  parse-to-Option resolution, and direct-native float conversion. The rejected
  series was not integrated; the semantic fixture and exact resume gate are
  recorded in
  `doc/08_tracking/bug/native_primitive_to_i64_ufcs_collision_2026-07-24.md`.
  The final Web producer cycle remains unspent.
- continuation-2026-07-25-admission: Package CSS authority now requires the
  installed snapshot fingerprint to match the resolved package, and Web plus
  Electron root attributes distinguish omission (preserve) from explicit
  empty (clear). Focused Web (5/5), Electron bridge, theme bootstrap (5/5),
  and hosted-wrapper (3/3) contracts pass. The retained 16x16 Aetheric host
  capture is diagnostic-only: its launcher emitted the Rust seed warning, the
  manifest hash is empty, render time is zero, readback is local raster, and
  event/performance evidence is absent. The evidence wrapper now fails closed
  for those conditions. x86 SSE2/static and ARM VirtIO/C preflights pass
  without launching QEMU. AC-1 is source-complete and AC-6 is fail-closed;
  AC-2/3/4/5/7/8/10 remain open, while AC-9 awaits final manual refresh.
  Exact-current host and QEMU evidence remain blocked by the recorded native
  primitive `.to_i64()`/imported `LogLevel.to_i64` collision.
- continuation-2026-07-25-to-i64-fixture: Added the required semantic native
  fixture for imported/custom/primitive/text `to_i64` ownership. An isolated
  bootstrap produced two verified pure-Simple Stage 3 compilers; optional
  Stage 4 was killed by signal 9. Both candidate fixture binaries linked
  without unresolved `LogLevel.to_i64`, but returned code 4 because the
  side-effecting `u8` result did not convert to 255. The candidate MIR guards
  were rejected and removed. The three-cycle cap is exhausted; exact-current
  host and QEMU launches remain blocked, with the retained cache and next
  inspection point recorded in the bug tracker.
- continuation-2026-07-25-to-i64-native-trace: Retained Mach-O disassembly
  proves `ReceiverProbe.next_u8` returns `0xff` and is immediately followed by
  a call to imported `LogLevel.to_i64`; rc=4 is dispatch failure, not numeric
  extension. Three pure-Simple Stage-3 candidates covering declared result
  propagation, pre-UFCS Infer guarding, bootstrap embedded-symbol lookup, and
  unresolved integer recovery all emitted the identical bad call. All
  compiler candidates were rejected and removed at the hard cycle cap. The
  semantic fixture and exact next native-entry HIR/MIR instrumentation point
  remain recorded; production host/QEMU evidence is still blocked.
- continuation-2026-07-25-theme-root-fixes: Integrated the reviewed typed WM
  material/gradient projection and fixed four remaining owner boundaries:
  UI-session submissions honor the tree-selected snapshot identity; Web
  custom properties filter `:root[attr]` against the actual root, preserve
  selector specificity and source-last precedence, reject descendant leakage,
  and support `i`/`s` attribute flags; Web Draw IR emits a typed first shadow
  layer with retained raw CSS; Engine2D consumes its blur radius and admits
  the supported WM glass style keys on a fresh device. Focused regressions
  cover root variants and typed shadow serialization. `git diff --check`
  passes. Runtime verification is still open: the deployed nominal release
  binary identifies itself as a Rust bootstrap seed, the isolated full
  bootstrap hit disk exhaustion, and current Stage4 rejects the shared
  compiler backfill as stale. The three-attempt build cap is exhausted, so
  no host/QEMU live claim is made from these source changes.
- continuation-2026-07-25-stage3-evidence-routing: The export-use global
  binding fix cleared fresh bootstrap stages 2 and 3; full Stage 4 now reaches
  the full-CLI parse and is killed at roughly 4.68 million heap-registry
  entries, so it is recorded as a resource/OOM blocker rather than an
  export-use regression. The verified Stage 3 compiler built the focused host
  generator and CPU-SIMD renderer after isolating native caches per entry and
  wiring the existing WM runtime providers, but the UI-access CLI then exposed
  an unwired SQLite provider set. The three host cycles are exhausted and no
  host screenshot/event PASS is claimed. The x86_64 WM kernel independently
  compiled 662 files with zero failures and produced a preserved
  ELF32/little-endian/EM_386 Multiboot1 image. Its wrapper admission had both
  the wrong ELF64 expectation and a positional-argument clobber that made the
  machine check read a file named after the class byte; both source defects
  are corrected, but the cycle cap prevents a further QEMU launch in this
  session. ARM64 remains blocked because the canonical producer requires the
  absent full CLI `os build` dispatcher; Stage 3 cannot substitute for that
  provenance path. Live x86/ARM captures and comparison therefore remain open.
- continuation-2026-07-25-fat32-x86-host-arm: Valid FAT32 image construction
  and fsck/manifest integrity are now on `main`. The x86 QEMU lane boots GRUB,
  the current kernel, NVMe, and a real 3840x2160 ARGB scanout; after the
  DrawIR optional workaround it reaches `engine2d_rendered`, but correctly
  fails closed because the material fallback identity is lost (`none` with an
  empty hash). No x86 capture or input receipt is claimed. The reviewed host
  native-provider binding and compiler zero-argument receiver preservation
  fixes are pushed through `62b498050e`. A refreshed host CPU-SIMD run now
  reaches `engine-cleared` before a distinct nil-receiver fault, so screenshot
  and Electron event evidence remain open. Vulkan compiles but its earlier
  live run faulted in the font-atlas path; Metal compiles but fails closed to
  CPU because no backend-specific probe is available. Standalone NEON reports
  exact primitives but 18/192 composite mismatches. The focused ARM CLI source
  route passed high review, but its exact Stage4 capsule was killed with
  exit 137 before producing an executable, so ARM QEMU was not launched.
  Parallel agents own the x86 provenance and host nil-receiver diagnoses.
- continuation-2026-07-25-bounded-runtime-results: The reviewed scalar x86
  material predicate correction is pushed through `fd935c8d9a`; it snapshots
  wide aggregates, avoids nil `trim/lower` dispatch for the exact WM contract,
  remains fail-closed, and emits one rejection receipt per render invocation.
  Its final behavioral execution was not repeated after the three-cycle cap.
  The preceding canonical x86 run built 663 files and booted a current admitted
  kernel, but still rejected content provenance before capture or input
  injection; no x86 screenshot, SIMD receipt, or event claim is made. A minimal
  host CPU-SIMD probe renders/presents/reads back successfully and then faults
  at the nullable zero-argument
  `vulkan_font_performance_evidence()` getter; three scoped fixes did not
  converge, so no speculative host patch was retained. The ARM compatibility
  import fix is pushed as `a750d8413e`, but the final exact focused build then
  reached a second retained-Stage3 grammar blocker at the tuple-pattern loop in
  `cuda_backend.spl:562`. ARM cycle 3/3 produced no artifact, therefore QEMU
  was not launched. The backend capture comparison remains fail-closed:
  Vulkan and Metal compile, standalone NEON has 18/192 composite mismatches,
  and no backend currently has comparable live capture plus event evidence.
- continuation-2026-07-26-toolchain-promotion: High review rejected the host
  `fn`-getter-to-`me` workaround and its rectangle-only probe because it hid
  the immutable receiver ABI bug and expected an impossible nonempty font
  target; neither change was integrated. The strengthened material-provenance
  probe and exact refutable-binding grammar fixture are pushed, but x86 QEMU
  did not launch because both retained Stage3 compilers reject the legitimate
  `val Some(x) = value else: break` surface. The guarded ARM exact-capsule
  source/cache route is pushed as `0f4c846a08`; source review accepts it, while
  execution remains open. The owner-level pure parser fix for existing
  unparenthesized tuple bindings is pushed as `1c03e23f0d`.
  A no-Rust synthetic bridge at historical `19b32d6aec` plus the tuple parser
  and receiver fixes built 675 modules with zero failures:
  `build/worktrees/grammar-bridge-19b-synthetic/build/grammar-bridge-19b/bootstrap/aarch64-apple-darwin/simple`,
  SHA-256 `ce3440cc2fe6fcd1f5a58d9372624565c1d167a3c0dc3bd24853ee906823b45c`.
  Its native receiver regression passes. The bridge's pure positional route
  also parses/code-generates the refutable binding, proving the earlier
  `Else` failure came from the historical `--entry` delegation to the stale
  Rust parser, not the pure parser. Positional linking still fails on missing
  `___simple_runtime_init`, `___simple_runtime_shutdown`, and `spl_init_args`,
  so the bridge is not admitted for the current-main hop. The manual-discovered
  full CLI SHA `8a0c22df...` is rejected: it predates focused OS routing,
  loses linker stderr, and crashes with corrupted HIR state. Next resume must
  repair/admit the pure positional runtime-link/one-binary route, then rebuild
  current main with fresh caches before any host or QEMU evidence run.
- continuation-2026-07-26-pure-runtime-capsule-and-receiver-gate: The
  synthetic bridge's positional Cranelift route is now admitted through a
  reproducible current-source C-runtime capsule rather than the stale
  bootstrap runtime archive. At source `4e1ddd3afe`, Apple clang 17 compiled
  the canonical 15 hosted runtime sources; the source-list fingerprint is
  `16e6153aefabbaa93fbe32e071308543a7e64ea884677874b3448ee783acf5ab`
  and the reviewed composite archive SHA-256 is
  `02775039b26c80ad5858976ad0761ab331cd6454bee202b6dfb3a25310a19d85`.
  A refutable `val ... else` fixture linked and ran with exit 0 through the
  pure positional path. Two current-main compiler promotion attempts were
  then killed with exit 137 before producing an artifact. The second attempt
  used one worker and requested low-memory mode, but trace inspection proved
  that the historical positional bootstrap driver ignores that CLI flag when
  constructing `CompileOptions`; it died near 1.6 million heap-registry
  entries. The final permitted promotion attempt is deferred until a
  pure-built bootstrap-only bridge variant explicitly enables
  `options.low_memory`.

  The immutable receiver investigation found no further production change is
  justified beyond the already-pushed `fd21c765f2`: its three receiver-vector
  paths preserve the implicit receiver without changing `fn` mutability.
  High review rejected an initial false-positive fixture, then accepted the
  corrected cross-module zero- and one-explicit-argument receiver regression.
  That test is pushed as `7554bc6ff1`. Host and QEMU live evidence remain
  open until the current compiler promotion succeeds; no screenshot, input,
  Vulkan, Metal, or SIMD parity claim is added by this checkpoint.
- continuation-2026-07-26-current-host-live-failures: The canonical staged
  self-hosted compiler at the repository release path rebuilt both current
  macOS backend harnesses and refreshed their trusted manifests. Real window
  launches still fail before readiness. Vulkan's stripped artifact exits 132
  on a nil receiver, while an unstripped current diagnostic artifact reaches a
  fail-closed receipt:
  `Vulkan shared session initialization failed: availability`. MoltenVK,
  the loader, and provider symbols are present, so a focused availability /
  device-count receipt is required before another full window cycle. Metal
  falls back to CPU because the main Engine2D MSL library fails compilation.
  The shared harness now probes `MetalBackend.last_error` directly instead of
  reporting the previous uninformative
  `backend-specific-probe-unavailable`. A diagnostic attempt to preserve
  `metal_last_error()` exposed a separate native text ABI corruption
  (`<value:...>`), so that misleading detail plumbing was reverted.

  The host Vulkan and Metal three-cycle limits are exhausted for this session.
  No before/after window capture, 4K device readback, ordered input receipt, or
  cross-backend parity is claimed. CPU-SIMD and both QEMU lanes remain open;
  QEMU still depends on a pure compiler route that does not retain the entire
  phase-2 compiler closure. Current reports and root-cause notes are recorded
  under `doc/09_report/wm_current_*_2026-07-26.md` and
  `doc/08_tracking/bug/`.
- continuation-2026-07-26-phase2-source-reclamation: Pushed `51ba081458`
  after independent high review. Low-memory non-VHDL compilation now clears
  every frontend whole-source holder after Phase 2, registry-frees every
  `SourceFile.content` alias without dereferencing a previously freed alias,
  then evicts source metadata before HIR. The focused spec covers shared and
  distinct allocations plus parse/reset/reclaim/HIR ordering, and the stale
  deep-free report now limits the claim to source buffers. Both direct-env
  audits pass. The available full-CLI runner stayed CPU-bound without test
  output for more than six minutes and was stopped once under the runaway
  guard; therefore the new spec has no executable PASS and no Stage-4/RSS
  claim. The final compiler-promotion attempt remains unspent until that
  focused gate can run on a healthy admitted full CLI.
- continuation-2026-07-26-cpu-simd-oracle-and-provenance: Pushed the reviewed
  CPU-SIMD correction through `b7abf9512d`. Production C/NEON blending was
  already correct; the pure-Simple scalar fallback needed explicit packed-word
  `i64` normalization under native AOT. The evidence program now uses the
  canonical scalar helpers, covers non-opaque destinations, and derives gates
  from per-kernel hit counters plus exact mismatch totals rather than corrupted
  aggregate bool receipts. The wrapper has one committed canonical source,
  byte/SHA equality, exact command and artifact provenance, bounded logs, and
  fail-closed native mode. No fourth native run was made after the three-cycle
  cap, so the report remains `BLOCKED`; the unchanged architecture-matrix
  scenario also remains a release blocker. This is an integrated correctness
  and evidence-hardening checkpoint, not a fresh native parity PASS.
- continuation-2026-07-26-sibling-qemu-audit: A read-only sibling audit found
  one external x86 desktop native build still CPU-bound after roughly 49
  minutes, with no candidate ELF, QEMU process, cache output, or new receipt.
  It started from the changing dirty root and source files changed afterward,
  so any eventual result is diagnostic-only without frozen-source admission.
  Existing x86 reports remain stale FAIL and no ARM sibling has new evidence.
  All relevant x86/ARM sibling commits are already patch-equivalent to, or
  superseded on, `origin/main`; nothing should be cherry-picked. Live x86 and
  ARM capture/event rows therefore remain open.
- continuation-2026-07-26-vulkan-provider-micro-probe: Pushed the reviewed
  windowless provider diagnostic through `763453420e`. It binds the exact
  provider and canonical self-hosted compiler to trusted paths/hashes, resolves
  availability/init/device-count/error/shutdown symbols, gates calls in
  fail-closed order, records a reproducible command, and retains bounded
  build/probe logs with hashes. The dynamic loader exposes provider error as
  tagged `text`, while `DynLib.call0` returns `i64`, so the unsafe conversion
  was removed and `provider_error_abi=blocked` is explicit. Source contract
  2/2 and shell/audit checks pass. The exhausted native/full-live cycles were
  not rerun, so availability/device count and Vulkan rendering/events remain
  unobserved rather than inferred.
- continuation-2026-07-26-gpu-manifest-and-arm-simd-admission: Pushed GPU
  trusted-manifest admission as `ca911ba081`. Independent high review ACCEPTS
  its exact current/legacy identity-source pairs, canonical builder
  `--verify` delegation, legacy provenance recomputation, fixed
  compiler/provider paths and hashes, caller-override rejection, seed/debug
  rejection, shell safety, and static-only native-claim boundary.

  Pushed the ARM64 QMP SIMD receipt gate as `d63f205ccf` and its manual-only
  quality repair as `04bc5fa4f4`. High review ACCEPTS the functional gate:
  exactly one AArch64/NEON receipt, positive native fill hits/vector chunks,
  complete required `fill` kernel-kind execution, no fallback, bit-exact
  scalar parity, final-transcript uniqueness, and evidence/report binding.
  The first review REJECTED only the generated manual presentation; the follow-
  up restores the prominent no-live-evidence disclaimer and removes malformed
  pseudo-steps without changing the gate.

  The low-memory compiler bridge remains circular: the current compiler
  promotion needs an admitted low-memory-capable bridge, while producing that
  bridge depends on the compiler path being promoted. The tracking document
  `bootstrap_low_memory_positional_bridge_circularity_2026-07-26.md`, pushed
  through `8ac0150d38..7f9815a929`, is now ACCEPTED by high review. Binary
  `f2c216...` is seed-marked and forbidden as compiler, driver, delegate, or
  fallback. Binary `277f...` is the only eligible pure-Simple candidate, but
  it cannot import the current compiler graph.

  The corrected next action uses one of the two remaining bounded micro cycles
  in a clean linked worktree: pin only `277f...` and attempt a minimal
  historical-compatible bridge within that capsule's import/syntax surface.
  Before use, require a canonical regular path and exact hash, bounded version,
  negative seed-classifier checks, and `nm` proof of native `rt_string_free`.
  Only an admitted non-seed bridge may build the focused current-graph probe
  with `SIMPLE_NO_STUB_FALLBACK=1`; positive opt-in reclaim and negative
  no-opt-in controls must both pass. If `277f...` cannot produce that bridge,
  stop and retain the bug. Do not use `f2c...` or run full Stage4 to diagnose
  the circularity. No compiler promotion, host/QEMU launch, SIMD parity PASS,
  or native rendering/event claim is added by this checkpoint.
- continuation-2026-07-26-electron-only-current-host-scope: By user direction,
  the current host now owns only repository-pinned Electron provisioning and
  the canonical Aetheric browser render/event/capture lane under TODO 583.
  The pure-Simple bridge/runtime capsule, native Vulkan/Metal/SIMD comparison,
  x86 QEMU evidence, and ARM64 QMP framebuffer/input/NEON evidence are
  postponed to prepared external hosts through their existing open TODOs and
  external-host plan. No acceptance criterion is closed, excluded, skipped,
  or counted as PASS by this decision. External execution must retain admitted
  compiler/provider identities, frozen manifests, serial/QMP logs,
  framebuffer/device readback, checksums, events, font/DPI/SIMD receipts, and
  independent review. Missing Electron or producer prerequisites on this host
  remains a fail-closed blocker; it does not authorize implicit `npx`
  downloads, a seed compiler, fixture rendering, or synthetic evidence.
- continuation-2026-07-26-pure-line-priority: User reprioritized Electron WM as
  noncritical and postponed its live run. TODO 583 is now P3 and remains open;
  no compiler/provider admission was requested, no Electron process launched,
  and no live proof or PASS exists. Strict local Electron resolution and
  Aetheric identity admission are integrated through `7a03de1b4d`; the
  separate WM-event provenance candidate failed final review and was not
  pushed.

  The critical P1 lane is explicit under TODO 580:
  pure-Simple WM -> GUI/Web semantic owners -> DrawIrComposition -> Engine2D
  CPU-SIMD/Vulkan/Metal -> device-origin capture and ordered events -> x86/ARM
  QEMU parity. It resumes only on prepared hosts with an admitted
  source-matched pure-Simple compiler, immutable provider/runtime provenance,
  frozen manifests, exact CPU oracle parity, backend/device identity, timing,
  RSS, and independently reviewed artifacts. The authoritative plan and links
  are `doc/03_plan/agent_tasks/wm_glass_theme_host_simpleos.md` and
  `doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`.

- continuation-2026-07-26-package-owned-theme-projection: A parallel
  source/history audit found that `UISession.submit_widget_draw_ir` accepted a
  tree-selected theme but repainted a mismatch through the compatibility
  widget lowerer and process-global WM material. Browser/session/theme-service
  callers also carried `ResolvedThemePackage` or `ResolvedThemeColors`
  aggregates across the native boundary documented by the current hosted-WM
  failure.

  The source fix keeps `ResolvedThemePackage` inside `theme_package.spl` and
  exports only snapshot, fingerprint, scalar material/color, token, and
  canonical-id projections. Default-id, alias, and package caches now prevent
  registry/package rereads after warmup and preserve targeted/global
  invalidation. `UISession` reuses an installed generated snapshot only after
  a non-empty scalar identity match, through an owner-local non-optional list
  projection; mismatches load the tree's own canonical package snapshot.
  BrowserBackend and the SimpleOS browser compositor now use the same
  package-owned snapshot/scalar authority, and production callers no longer
  invoke `load_theme_package` outside its owner module.

  Focused session, package, render-snapshot, and Web authority specs were
  updated; the Web authority manual now matches all six scenarios. Static
  diff, generated-spec-layout, and direct-runtime guards pass, and independent
  Terra plus highest-capability Sol reviews ACCEPT the final boundary. The one
  bounded session-spec run timed out before assertions, while a corrected
  self-hosted source check reached unrelated pre-existing compiler frontend
  errors; therefore this checkpoint is source-fixed and reviewed, not an
  executable native/host/QEMU PASS. The concurrent rejected 59-line draft was
  not committed. Its replacement plans now freeze the exact current revision,
  admit no current Wave 0 compiler capsule, constrain BrowserBackend edits to
  semantic snapshot ownership, link the five fixed manual steps and parity
  checker, and gate every render/device/QEMU execution row on immutable
  compiler/runtime provenance. Independent highest-capability Sol review
  ACCEPTS both repaired plans. Runtime evidence remains open; this planning
  repair does not claim native, host, or QEMU execution.

- continuation-2026-07-26-host-package-activation: Current-source and history
  audits found that hosted bootstrap still bypassed the registry package on a
  fresh launch and installed the generated bare-metal Aetheric snapshot.
  `install_host_wm_theme(theme_id)` now consumes only
  `theme_package_render_snapshot(theme_id)` and installs that immutable
  projection before backend/compositor creation; the default path resolves
  `default_theme_id()`, so Stitch package CSS/material changes reach WM, GUI,
  and Web through one identity. Existing explicit selection is preserved
  through `active_wm_theme_snapshot_present()` plus the native-safe plain
  snapshot getter, never the Cranelift-broken optional aggregate return.
  Freestanding SimpleOS still uses its generated snapshot and dynamic
  ThemeService notification remains explicitly out of this checkpoint.

  The focused bootstrap contract passes 7/7 in interpreter mode, the direct
  environment/runtime guard and diff checks pass, and independent
  highest-capability Sol review ACCEPTS after rejecting and correcting the
  unsafe optional-return branch. Lint reached unrelated current compiler
  semantic failures and supplies no positive result. This is a reviewed
  hosted source fix, not native framebuffer/event or QEMU proof.

- continuation-2026-07-26-wave0-runtime-capsule: The compiler driver now emits
  ordered `phase2:source_reclaim:start` and `phase2:source_reclaim:done`
  markers inside the existing low-memory reclaim branch; focused exact-body
  contracts pass 2/2 and 3/3. This makes the required live receipt observable
  without changing reclaim behavior or claiming admission.

  The committed direct-C producer
  `scripts/check/build-core-c-bootstrap-runtime-capsule.shs` compiles the
  canonical runtime graph twice, hashes all 24 declared/transitive local
  inputs, CC/AR/NM binaries and version receipts, requires byte-identical
  deterministic archives, proves sole `rt_string_free` ownership in
  `runtime_native.o`, and runs the C tombstone/alias self-check. Independent
  review ACCEPTS the clean pushed capsule at source
  `088da06413217edec9454cd0c24de417a8cd5e65`, runtime tree
  `3dd0db9de03e225a0e16164e0a52a40cc4774902`, archive
  `c4f39c1a74e1979d2680153476199b0d70b626fabb0b01d22cedc4505ca46e74`,
  and manifest
  `5773db91727ce05bde7c100a64ef77206e4b166c1efc36534e7196d2fadf0003`.
  The remote later advanced to `3ed2200828` with the same runtime tree, so the
  runtime capsule remains reusable while compiler admission must use the newer
  source revision.

  Compiler Wave 0 remains NOT ADMITTED and its final micro-cycle remains
  unspent. A tracked focused bridge and live probe now call the current
  `CompilerDriver`, and the fixed bootstrap API enables low-memory mode only
  when all three canonical opt-ins equal `"1"`; the pure 8-case predicate spec
  and four-scenario fail-closed system contract pass. Independent
  high-capability source review ACCEPTS this preparation. The mirrored manual
  is
  `doc/06_spec/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.md`.
  No admission runner exists or has executed, and the historical pure compiler
  still cannot pass the necessary `native-build` validator or implement
  current no-stub semantics. Host/device/QEMU execution rows therefore remain
  closed until the runner and exact native route receive independent review.

- continuation-2026-07-26-cpu-composited-glass-material: **SOURCE PREPARED /
  UNVERIFIED.** The dirty shared Engine2D slice keeps canonical WM
  `DrawIrCommand.color` as opaque `solid_fallback_rgba` for native-safe
  transport; the translucent package `window_fill_rgba` remains in the
  existing `background-color` style and feeds the enabled CPU material helper.
  The helper samples the pre-surface framebuffer, applies bounded
  blur/saturation, clips a rounded surface, and alpha-composites the style
  material or two-stop gradient before existing borders. Requested blur 30 is
  explicitly realized as blur 4 with realized blur/saturation/reduction
  witnesses; `i64` arithmetic and a 67,108,864-pixel output/working cap bound
  the helper.
  It is deliberately not a new Draw IR command, private renderer, GUI/Web
  implementation, CPU-SIMD receipt, native Vulkan/Metal implementation,
  host/QEMU capture, device readback, event receipt, or timing/RSS result.

  The focused source tests define the intended WM-style request and CPU pixel
  arithmetic, but no passing receipt exists for this dirty checkpoint. The
  third verification cycle had an opaque-material test failure; post-run static
  review identified and corrected the saturation-zero luminance rounding
  mismatch, but the session retry cap prevents a post-fix run. Normal Web
  lowering still intentionally erases glass to named solid fallback, so
  GUI/Web realization remains open and needs a mode-aware provenance-preserving
  patch. Independent review and a fresh-session PASS remain required before
  integration. Existing aggregate system evidence remains fail-closed; all
  host/device/QEMU rows remain open.

- continuation-2026-07-26-web-material-w1-w4: **SOURCE PREPARED /
  UNVERIFIED.** The canonical Simple Web cascade now preserves the exact
  opt-in glass semantics, retains unsupported image syntax as a fail-closed
  raw witness, and normalizes the Aetheric
  `linear-gradient(...), rgba(...base...)` stack into one typed gradient plus
  translucent surface. Draw IR keeps the named opaque command fallback and
  carries explicit requested/realized material witnesses.

  Engine2D now receipts only successful CPU glass execution. Web provenance is
  derived after rendering and requires a complete Draw IR witness count to
  equal the Engine2D execution receipt count; incomplete execution, skipped
  commands, unsupported layers, or receipt mismatch remain `none`. The WM
  validator accepts only the exact solid/CPU reason pairs and lowercase
  SHA-256 formatting. No native-device, SIMD, host, event, or QEMU claim was
  added.

  `git diff --check` passes. The focused SSpec runner exhausted its three-cycle
  cap with only `0 passed, 1 failed` and no child diagnostic. The repository
  launcher then identified as a Rust bootstrap seed, so source checking stopped
  without bootstrap per user instruction. The harness defect is tracked in
  `doc/08_tracking/bug/sspec_runner_suppresses_child_failure_diagnostic_2026-07-26.md`.
  Fresh pure-Simple focused PASS and retained host/device/QEMU evidence remain
  required.

- continuation-2026-07-26-web-material-review-repair: Highest-capability review
  rejected the first integration and drove five owner fixes. Draw IR now uses
  the real `rect` command identity; Aetheric snapshot/Web shorthand values keep
  base `0xCC1F1F21` and raw alpha stops `0x14FFFFFF`/`0x06FFFFFF`; the updated
  material SHA-256 is
  `0ad3df8e5f6169cb83a2554fbe0823ec470070ae43a47eae701c4f9321cdda37`.
  Software and Engine2D material paths composite base then alpha gradient.
  Embedded/offscreen execution returns zero material receipts until a
  parent-backdrop-aware path exists.

  Web provenance now uses a typed producer witness built through direct
  per-field Style binds and is admitted only after exact pixel/skipped/count
  execution checks. Generic Draw IR has no such witness and remains
  fail-closed. Exact backdrop grammar and strict legacy solid witnesses prevent
  malformed exact mode from downgrading to an accepted solid receipt. Focused
  source assertions cover the complete public Aetheric shorthand route, but a
  usable pure-Simple runner PASS remains outstanding.

- continuation-2026-07-26-web-material-final-review: **ACCEPTED FOR SOURCE
  CHECKPOINT.** A final highest-capability read-only review accepted the W1-W4
  implementation after correcting the centered first-row software-gradient
  expectation to `0xFF595959`. This is source-review acceptance only; it does
  not replace the outstanding pure-Simple runner, backend, host, event, or QEMU
  evidence.

- continuation-2026-07-26-no-bootstrap-evidence-audit: **W5 POSTPONED TO AN
  ADMITTED HOST/ARTIFACT SET.** Both macOS QEMU executables and firmware are
  installed, and static x86 WM/QMP/SSE2 preflight passes. Live x86 lacks an
  admitted current kernel/disk plus `grub-mkstandalone`; ARM lacks the admitted
  kernel, FAT disk, manifest, and frozen-source receipt. Producing them requires
  the long attested build, so it was not started.

  The generic deployed-runtime wrapper fails identity. The architecture-specific
  Mach-O binary reports `Simple v1.0.0-beta` but announces the forbidden Rust
  bootstrap seed when executing current source; its hosted capture admission
  correctly failed and the generated invalid report was removed. Existing
  captures and stale binaries remain diagnostic only. The reviewed source is
  remotely preserved on `codex/wm-glass-theme-host-simpleos-20260726`; no
  backend, native event, or QEMU PASS is claimed.

- continuation-2026-07-27-cross-host-routing: **CURRENT HOST ACTIVE; EXTERNAL
  HOSTS POSTPONED.** Added P0 requests for Windows Vulkan/SIMD, Linux
  Vulkan/RenderDoc/SIMD, x86 QEMU/SSE2, and ARM QEMU/NEON rendering plus native
  event evidence. Added a fail-closed system contract and manual that keep all
  four rows required while preventing their postponement from being counted as
  PASS. The macOS Metal/NEON/current-source lane remains active.

- continuation-2026-07-27-wm-web-adapter-glass: **SOURCE REPAIRED / RUNTIME
  UNVERIFIED.** Parallel read-only audits found no host-independent SimpleOS
  theme/event wiring defect, but found the current-host Web producer had
  removed `engine2d-cpu-composited-material-v1` from every WM content wrapper.
  That forced the legacy opaque reducer even though the generated Aetheric
  `.widget-panel` CSS owns a translucent surface and admissible backdrop.
  The producer now restores the exact mode without duplicating theme values,
  retains the opaque named fallback for fail-closed admission, and exposes a
  stable computed-style probe id. The committed conflict text in the existing
  adapter spec is resolved, and a focused production-request-to-Draw-IR
  regression pins surface `3424591649`, backdrop
  `blur(30px) saturate(170%)`, one CPU material witness, and a 64-character
  digest. Both the broad adapter spec and the reduced one-case spec timed out
  under the deployed interpreter's 120-second resource limit before any
  assertion (`0 passed, 1 failed`); no bootstrap or retry follows. Independent
  highest-capability review then accepted the strengthened command-level Draw
  IR assertions with no remaining P0/P1 source issue. Native Metal/NEON and
  postponed external-host/QEMU evidence remain open.

- continuation-2026-07-27-metal-device-glass: **SOURCE PREPARED / RUNTIME
  UNVERIFIED.** Three parallel read-only audits agreed that the existing final
  `device_readback` proves only framebuffer origin: the glass operation still
  ran through `read_pixels -> cpu scalar -> draw_image`. The current source
  adds one narrow Draw IR target operation and two optional Metal pipelines.
  An ordered device snapshot encoder precedes the material encoder, avoiding
  in-place blur races while keeping transient buffers outside Draw IR. Only a
  completed dispatch yields `metal-device-glass-v1`; counts, target, positive
  framebuffer handle/device identity, and final device readback must all match
  before Web/WM accepts `metal-device-composited-material`. CPU execution and
  device execution remain distinct and fail closed on mismatch.

  The extracted embedded MSL compiled successfully with the installed macOS
  Metal compiler. The repository source check refused because the deployed
  architecture runtime identifies as the forbidden Rust bootstrap seed; no
  bootstrap was started. Focused Simple unit/integration specs were added but
  not executed. Highest-capability review found and corrected a translucent-
  destination alpha mismatch in the shared MSL blend helper, then accepted
  the final source with no P0/P1 findings. The live Metal spec now compares
  sampled device pixels against the CPU oracle over a translucent backdrop.
  The existing row SIMD ABI can use real NEON for blend rows but lacks
  operation-specific proof and does not accelerate blur/saturation, so no NEON
  glass claim was added. Vulkan and external-host/QEMU rows remain postponed.

- continuation-2026-07-27-aetheric-mode-source-reconciliation: **SOURCE
  REPAIRED / RUNTIME UNVERIFIED.** A later one-file change removed the WM
  material mode based on guest output but retained both committed production
  specs that require the mode and exact resolved Aetheric material. Parallel
  source/history review found that the stated CSS limitations had already
  been repaired in `6b18dcd874`: the Web cascade resolves package variables
  before declaration parsing and normalizes exactly one linear highlight plus
  translucent base into typed fields while preserving unsupported layers as
  rejection witnesses. The wrapper again carries the exact mode, and the
  production full-package spec now continues through Engine2D software
  execution and requires a matching CPU material receipt. The guest output is
  retained as diagnostic-only because no revision-bound current pure-Simple
  executable is available; active host GUI processes delegate to
  `simple_seed`. No runtime PASS, native capture, or QEMU claim is made.

- continuation-2026-07-27-pure-gui-no-seed-delegate: **SOURCE PREPARED /
  RUNTIME UNVERIFIED.** Parallel launcher/history audits found that selecting a
  self-hosted `SimpleGui` is insufficient: `_cli_driver_binary()` delegates
  `.spl` execution to its deployed `simple_seed` sibling. The CLI now supports
  the exact opt-in `SIMPLE_NO_BOOTSTRAP_DELEGATE=1`, which returns no external
  driver so `cli_run_file` stays in the admitted self-hosted process.
  Ordinary CLI/bootstrap behavior is unchanged when the flag is absent, and a
  focused unit spec saves/restores the environment while pinning the opt-in.
  An active sibling session owns the macOS launcher/evidence wrappers, so this
  checkpoint deliberately does not race those files. The launcher must still
  set the flag and prove equal launcher/window-owner identities before host
  pixels or events become admissible.

- current-state-2026-07-27: **MACOS IMPLEMENTATION ACTIVE / RUNTIME
  UNVERIFIED.** The authoritative Aetheric Stitch glass source contract is
  restored: the production wrapper carries the resolved material mode, and
  the renderer material plus Engine2D software-receipt path is tested. The
  Metal device sample/translucent-CPU-oracle checkpoint also exists, including
  straight-alpha handling for translucent destinations. Commit `b7b4c241dc`
  supplies the opt-in `SIMPLE_NO_BOOTSTRAP_DELEGATE=1` path so an admitted
  launcher can keep source execution in-process.

  This is not live macOS GUI evidence. It remains **RUNTIME UNVERIFIED** until
  a trusted, source-matched self-hosted runtime is admitted and proves the
  launcher/window-owner identity plus the required native receipts. No
  seed/bootstrap run is admissible for this proof, and orphan `SimpleGui ->
  simple_seed` processes are explicitly inadmissible diagnostic residue.
  Linux/Windows, x86/ARM QEMU, and native-board execution remain fail-closed
  and postponed to their prepared hosts; use the existing cross-host handoff
  commands and path references rather than treating postponed rows as PASS.

- source-checkpoint-2026-07-27: the macOS widget/web live-evidence path is now
  fail-closed on `macos-gpu-2d-live-native-manifest-v2`. The manifest binds
  the exact widget source, web source, and web HTML path/hash. Strict
  `SimpleGui` launch records bind the admitted compiler, copied executable
  hashes, launcher/window-owner PID identity, and absence of `simple_seed`
  descendants. Both wrappers consume that record, recheck identity/hash before
  input and window-ID-scoped captures, and have host-neutral contract probes.
  Shell/static and positive/negative contract probes pass; no live GUI,
  bootstrap, seed, or QEMU execution was used, so runtime status remains
  **UNVERIFIED**.

- metal-receipt-checkpoint-2026-07-27: a successful Metal device-glass
  receipt now requires `gpu_only`; normal mirror mode fails closed and uses
  the explicit CPU fallback lane. The successful device path no longer calls
  the CPU glass oracle or mutates the CPU mirror, so zero-CPU device
  provenance cannot hide CPU work. Focused source and macOS behavioral
  regressions cover the boundary. Runtime evidence remains **UNVERIFIED**.

- live-driver-admission-blocker-2026-07-27: the v2 manifest admits a Stage-3
  compiler, while the strict launcher additionally requires that same binary
  to contain the native Winit GUI marker. The current builder proves Winit
  only on its native harness output, not on the admitted compiler. No local
  exact-current pure-Simple GUI driver with matching provenance exists.
  Before live widget/web evidence, admit a separately provenance-bound
  GUI-capable full CLI driver (or explicitly build and prove the full CLI);
  never substitute the harness or seed.

- continuation-2026-07-27-v3-render-authority: **SOURCE REVIEW REJECTED /
  RUNTIME UNVERIFIED.** The manifest-v3 candidate introduces a
  canonical full-CLI producer and immutable admission copies, binds the
  complete source/build transcript, and uses PID/executable/descendant-tree
  evidence to reject seed/bootstrap delegation. The launcher keeps the
  admission-exported driver and manifest hashes authoritative across launch.
  Final review rejected its process proof: it rejects the canonical
  `build/bootstrap/full` root by substring and polling can miss same-PID exec
  or short-lived descendants. The bounded review cap is reached; no canonical
  full-CLI artifact or generated manifest-v3 exists locally.

  The hosted Web cache now receives the selected Engine2D backend instead of
  the old `auto` software default. The canonical package-aware Web CSS branch
  uses package-owned variables for fills, material, and traffic controls;
  literal palettes remain only in the explicit package-less compatibility
  branch. WM chrome carries the Aetheric material through Draw IR, samples the
  already-painted parent in z-order and preserves inactive embedding opacity.
  Final review rejected the Metal path because the inactive offscreen is not
  GPU-only, receipt target/handle/device aggregation is last-wins, and one
  capability assertion is inconsistent. That uncommitted candidate is not a
  source checkpoint. Both exact blockers are recorded under
  `doc/08_tracking/bug/`.

  x86_64, ARM64, and RV64 canonical desktop entries now install the generated
  Aetheric snapshot before compositor/first-frame construction. External
  QEMU/Windows/Linux evidence remains fail-closed under the prepared-host
  handoff. The current session did not bootstrap or substitute the Rust seed.

- continuation-2026-07-27-web-css-final-review: **SOURCE REVIEW REJECTED /
  RUNTIME UNVERIFIED.** The final bounded candidate separated canonical
  package output from the literal compatibility sheet and supplied all
  referenced Aetheric tokens. Review still rejected it because the canonical
  builder emits literal `\\n` separators and its traffic-light pseudo-elements
  lack content/geometry. The review-cycle cap is reached, so the Web source
  candidate remains uncommitted. Exact fresh-session repairs and focused
  commands are recorded in
  `doc/08_tracking/bug/web_css_package_authority_adapter_2026-07-27.md`.

- continuation-2026-07-27-web-css-repair-accepted: **SOURCE FIXED / REVIEW
  ACCEPTED / RUNTIME UNVERIFIED.** A fresh origin-based lane repaired real CSS
  newlines and traffic pseudo-elements, retained the complete production
  structural/event contract (including window state, resize/hot-corner hit
  geometry, dialogs/forms, tooltip/tree DOM, taskbar preview/context menus, and
  responsive breakpoints), and kept all canonical paint/material values in the
  Aetheric package. Focused static/token/producer contracts and independent
  highest-capability review passed. No admitted self-hosted runtime exists, so
  live Simple Web parsing, Draw IR, pixels, events, and timing remain open.

- continuation-2026-07-27-metal-per-material-repair-accepted: **SOURCE FIXED /
  REVIEW ACCEPTED / RUNTIME UNVERIFIED.** A fresh origin-based lane made the
  retained Metal session device the single identity for material execution and
  device readback, then validated one ordered receipt per independently derived
  Draw IR material request against the presented framebuffer. Behavioral
  contracts reject missing, duplicate, extra, reordered, unfulfilled, mixed,
  or tuple-mismatched receipts. CPU parent-seeded delta preserves 500/930
  opacity. Sub-opaque selected Metal now fails before dispatch rather than
  creating a mirror-backed offscreen or claiming a device frame. Independent
  highest-capability review accepted the source; admitted macOS opaque-Metal
  readback/capture evidence remains open.

- continuation-2026-07-27-macos-admission-repair-accepted: **SOURCE FIXED /
  REVIEW ACCEPTED / LIVE ENDPOINT SECURITY UNAVAILABLE (EXIT 125).** A fresh
  scoped lane fixed canonical full-CLI root classification and replaced the
  polling/self-attested process receipt with a normalized v2 history verifier
  plus a fail-closed tracked trust-root gate. It rejects gaps, malformed
  lineage, forbidden-role same-PID delegation, short-lived forbidden
  descendants, incomplete exits, root-order violations, and
  collector/policy/provenance/signing drift.
  Widget and Web launchers use the exact admitted GUI driver. Independent
  highest-capability review accepted the fail-closed source boundary. Live
  evidence remains open because the real Endpoint Security collector and
  admitted trust-root branch are not implemented, and this host has no
  approved signing team, entitlement, signed provenance-bound collector, or
  source-matched canonical full-CLI GUI artifact. The production branch
  deliberately exits 125 until the implementation is reviewed, pinned policy
  hashes/status are updated, and those capabilities are provisioned.

- continuation-2026-07-27-hosted-browser-event-routing: **SOURCE ROUTE FIXED /
  STATIC CONTRACT ACCEPTED / LIVE EVIDENCE OPEN.** The production hosted
  browser keeps address/title commands on the canonical compositor and sends
  page pointer, key, text, and active-animation commands through the retained
  `HostedBrowserRendererProcess`, followed by external-frame re-submission. A
  scoped executable-source contract strips comment-only lines, binds the
  canonical process construction, separates address/page branches, validates
  ordering and semantic targets, and rejects private/direct routes.
  Independent highest-capability review accepted that contract. AC-7 still
  requires live focus, pointer, move/maximize, key/text, timing, animation
  frames, and post-state evidence from an admitted runtime.

- continuation-2026-07-27-qemu-contract-review: **P1 GAPS / LIVE ROWS
  BLOCKED.** Independent highest-capability review confirmed theme-before-
  first-frame wiring but rejected a source-complete claim. x86 still needs
  published frozen admission with no external-ELF bypass, SSE2/scalar parity,
  strict damage/frame ordering, timing, and RSS. ARM still needs firmware and
  theme/material/backend/fallback identity plus a receipt finalized after the
  correlated WM frame. Exact repair gates are tracked in
  `doc/08_tracking/bug/wm_glass_qemu_evidence_contract_p1_2026-07-27.md`.
  Active sibling changes remain separately owned and are not absorbed.

- continuation-2026-07-27-macos-es-collector-cycle-3: **SOURCE CANDIDATE
  STATIC ACCEPT / VERIFICATION BLOCKED / LIVE EXIT 125.** The Endpoint Security
  candidate collects exec/fork/exit lineage with sequence-gap and finalization
  checks, runs the exact driver from an immutable private snapshot in a process
  group, and binds immutable builder/policy/source/entitlement/output/manifest
  inputs to a non-circular unavailable/prepared/admitted policy. Independent
  highest-capability static review found no remaining P0/P1 in the bounded
  pathname-TOCTOU repair. The third-cycle cap was reached before the final
  Swift `-lbsm` link/self-test and repaired builder self-test could be rerun;
  focused boundary/full-CLI/GPU contracts and direct-env gates also remain
  unrun after that final repair. No PASS is inferred. Policy remains
  `status=unavailable`, and a fresh verification session plus separate
  prepared/admitted promotions are required before live evidence.

- continuation-2026-07-27-macos-es-collector-source-verified: **SOURCE
  VERIFIED / LIVE ADMISSION UNAVAILABLE.** At clean revision `b70aef1dd6`, a
  fresh non-bootstrap session passed the Swift `-lbsm` compile/link/self-test,
  builder immutable-snapshot self-test, focused boundary/full-CLI/GPU
  contracts, both direct-env scope modes, and the explicit `--exec-verified`
  unavailable-policy branch with exit 125 and `policy-not-admitted`.
  Independent highest-capability review accepted source verification. The
  clean direct-env passes are vacuous scope guards and are not implementation
  coverage. Policy remains `status=unavailable`; no approved signing team,
  Endpoint Security entitlement, prepared/admitted pinned collector and
  canonical driver, or live ES/GUI evidence exists.

- continuation-2026-07-27-browser-input-draw-ir-parity: **SOURCE FIXED /
  REVIEW ACCEPTED / RUNTIME UNVERIFIED.** CPU and Draw IR input text now share
  one `InputTextPaintPlan` for transformed/RTL/aligned/vertically placed text,
  theme-derived foreground, and intersected content/ancestor clips. Engine2D
  scopes and restores the clip while retaining canonical `draw_text` and font
  batch routes. Hosted address Backspace validates the full UTF-8 draft,
  removes one trailing scalar for valid Korean/`é`, and leaves malformed or
  truncated byte sequences unchanged. Behavioral specs pin exact Draw IR
  geometry/color/clip and pixel restoration. Independent highest-capability
  source review accepted commit `b51e27442f`. The admitted runtime was
  unavailable; live caret/selection, pixels, events, timing, and RSS remain
  open.

- continuation-2026-07-27-qemu-frozen-admission-hard-stop: **THREE-CYCLE CAP /
  NOT INTEGRATED / LIVE ROWS BLOCKED.** Two isolated frozen-receipt candidates
  were independently rejected for forgeable lineage, mutable-path TOCTOU,
  unbound final boot bytes/manifests, and helper-only false-green tests. The
  final cycle moved regular inputs toward no-follow snapshots and unlinked
  inherited descriptors, but its sole final behavior gate stopped before
  launch when macOS denied execution of the unlinked fake-QEMU snapshot through
  `/dev/fd/7`. No fourth attempt, QEMU, bootstrap, integration, or push ran.
  Rejected commit `6108a099f5` and the dirty final-cycle worktree are not
  evidence. Resume requires a reviewed descriptor-exec helper plus a
  builder-owned raw immutable x86 ESP image, then the still-open SIMD parity,
  ordered input/damage/frame, backend identity, timing, and RSS gates.

- continuation-2026-07-27-qemu-host-launch-helper-hard-stop: **THREE-CYCLE
  CAP / NOT INTEGRATED.** Darwin SDK research found no `fexecve`/`execveat`, so
  a fresh lane attempted a host C `posix_spawn` launcher with fixed inherited
  media descriptors and an opt-in raw ESP profile. Independent review rejected
  cycle 1; cycle 2 fixed descriptor roles, canonical argv/environment framing,
  and catalog compatibility, but P0 supervision/provenance/wiring/profile/test
  gaps remained. The final cycle stopped without changes rather than weaken
  them. Candidate `e98275fca0` lacks pre-spawn validation/receipt reservation,
  no-orphan kill-and-wait cleanup, supervised wait/signal/post-exit receipt,
  truthful exact source/compiler/SDK/argv/environment build provenance and
  concurrency-safe publication, QEMU signature+dylib/resource closure
  admission, exact wrapper fdset wiring, an isolated BOOTX64/kernel-only raw
  producer, and executable fake-QEMU behavior tests. Its threat claim could
  cover honest same-UID race resistance only; malicious same-UID admission
  remains unavailable without a privileged OS-immutable store. No QEMU guest,
  bootstrap, integration, or push ran; the candidate is not evidence.

- continuation-2026-07-27-browser-input-caret-selection-overlay: **SOURCE
  FIXED / STATIC REVIEW ACCEPTED / RUNTIME UNVERIFIED.** Supported single-line
  inputs now preserve stable author-id/body-relative identity and validated
  UTF-8 source boundaries through password masking, transform expansion, RTL,
  alignment, horizontal reveal, click placement, selection, and 500 ms caret
  blink. CPU and Draw IR share computed-color selection/text/caret order and
  clipping through both Engine2D executors. Readonly remains selectable but
  immutable; disabled emits no focus/hit/overlay; prevented defaults preserve
  state; chrome focus clears page caret/blink. Behavioral specs cover anonymous
  serialize/reparse mutation, malformed UTF-8, computed theme color,
  center/right alignment, blink visibility/cancel, and view retention/reset.
  Independent highest-capability static review accepted commit `63205f9e8f`.
  No admitted runtime existed, so no executed PASS is inferred. Textarea
  overlays and live pixels/events/timing/RSS remain open.

- continuation-2026-07-27-theme-notification-foundation: **SOURCE FOUNDATION
  ACCEPTED / RUNTIME SWITCHING STILL BLOCKED.** Added the common-only bounded
  `ThemeChangedV1` method-4 codec, strict canonical identity/hash/revision
  validation, injected synchronous-copy/non-reentrant transport contract, and
  stable all-subscriber dedupe/status policy. BrowserBackend static-frame,
  static-shell, layout, and present caches now include canonical theme id plus
  source-manifest and material hashes. Focused specs were added, direct-env
  audits and diff checks passed, and independent highest-capability static
  review found no P0/P1. The checked-in self-hosted launcher resolves to a
  Linux binary on this macOS host, so no runtime test or live switching PASS is
  inferred. Kernel-owned payload queuing/authenticated source identity,
  transactional package refresh, ThemeService delivery, monotonic consumers,
  and the intentional fail-fast system contract remain open.

- continuation-2026-07-27-brr2-foundation-hard-stop: **THREE-CYCLE CAP /
  REJECTED / NOT INTEGRATED.** An isolated source-only lane produced commits
  `a2e949d838`, `2edbe367ed`, and `c10eff40a9` for a numeric no-allocation BRR2
  guest owner, host parser, normalized lifecycle evidence, fixtures, and
  focused specs. Review cycles repaired receipt splicing, caller-forged parsed
  state, BRR1 event-count behavior, geometry overflow, and the false promotion
  of one four-stage SimpleOS lifecycle into six native input events. Final
  high-capability review still rejected the series because the public capture
  boundary collapses exact parser failures to `invalid_brr2_receipt`, making
  its checksum/endian/correlation expectations impossible, and because the
  selected four-backend requirement/design still applies the legacy six-event
  contract to the distinct SimpleOS lifecycle. Runtime tests/docgen were
  unavailable; no QEMU, bootstrap, Rust seed, integration, or push ran. Per the
  hard cap there is no fourth cycle. Resume in a fresh lane only after resolving
  the requirement/design contract and preserving exact parser reasons through
  public capture validation.

- continuation-2026-07-27-theme-ipc-owned-k1: **SOURCE FOUNDATION ACCEPTED /
  RUNTIME SWITCHING STILL BLOCKED.** Added an owner-local bounded IPC payload
  queue without changing the repr-C header: the manager copies caller bytes
  before return, enforces 4 KiB/message plus 64 KiB/64-slot per-port limits,
  preserves FIFO and exact pop/destroy accounting, distinguishes delivered,
  unauthorized, missing, empty, metadata-only, and invalid receive states, and
  rejects capability-bearing metadata until capability transfer is owned.
  Final high-capability review accepted the cumulative K1 repair with no P0/P1.
  K1 deliberately makes no authenticated-source claim because its task id is
  still a manager parameter; K2 must bind the kernel dispatcher’s actual
  current task, perform syscall copy-in/out, and align the ABI before
  `ThemeChangedV1` transport can be wired. The only diagnostic test executable
  identified as Rust-built and is not admitted PASS. Package transactions,
  generated SimpleOS snapshot catalog, ThemeService/consumer wiring, the
  fail-fast system contract, and live host/QEMU evidence remain open.

- continuation-2026-07-27-textarea-overlay-hard-stop: **THREE-CYCLE CAP /
  REJECTED / NOT INTEGRATED.** Isolated commits `32063ae68a`, `259c3e07be`,
  and `87a73e9d0d` extended the existing input overlay owners toward raw
  multiline textarea text, UTF-8/CRLF navigation, newline-only selection,
  per-line alignment/RTL, persistent horizontal reveal, clipping, worker state,
  and sub-800-line cohesive files. Independent review accepted those functional
  repairs statically but rejected the final series because the Draw IR painter
  imported the CPU framebuffer painter instead of a neutral shared owner and
  `browser_text_control.spl` declared two direct `rt_*` text externs outside a
  runtime/provider facade. The admitted self-hosted runtime was unavailable;
  no executed spec, live pixel/event, timing, or RSS PASS exists. No fourth
  cycle, integration, or push ran. Resume only in a fresh lane following
  `doc/08_tracking/bug/simple_web_textarea_overlay_review_hard_stop_2026-07-27.md`.

- continuation-2026-07-27-theme-catalog-hard-stop: **THREE-CYCLE CAP /
  REJECTED / NOT INTEGRATED.** Catalog candidates `9f9a921689`, `d404042bc4`,
  and `7ed0ae0a1a` added registry-derived aliases/defaults, deterministic
  generation, full tuple cache/provenance identity, generated-default boot,
  and resolver-derived freestanding closure checks. Final review rejected the
  series because pre-existing non-default active snapshots could bypass
  catalog/hosted parity and external-frame registrations were not revalidated
  after an active-theme change. No fourth cycle or runtime PASS exists. Resume
  through
  `doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27.md`.

- continuation-2026-07-27-theme-package-transaction-blocker: **CANDIDATE
  REJECTED / CYCLE 2 STOPPED READ-ONLY / CYCLE 3 UNUSED.** Commit `4f84131c55`
  was rejected for multi-read prepare drift, reachable mutable maps, unlocked
  partial publication, legacy commit bypass, and false-green overflow coverage.
  A safe single-read immutable candidate is viable, but the package module has
  no race-safe once-initialized hosted mutex/CAS owner. Unsafe lazy/eager module
  locks, stub atomics, and unlocked swaps were rejected. Resume only after
  single-threaded hosted bootstrap injects one transaction store, as specified
  in
  `doc/08_tracking/bug/theme_package_transaction_sync_owner_blocker_2026-07-27.md`.

- continuation-2026-07-27-theme-ipc-k2-hard-stop: **THREE-CYCLE CAP /
  REJECTED / NOT INTEGRATED.** K2 candidates `235ef0250b`, `41eedf1bf5`, and
  `d9554f91af` attempted versioned dispatcher-bound IPC copy-in/out,
  reservation/rollback, fail-closed SMP admission, mapping-stable copyout,
  nonreusable tokens, and broad caller migration on top of landed K1. Final
  review rejected the series because x86 compatibility IDs were not registered
  or state-threaded, kernel-internal direct x86 syscalls bypassed the assumed
  interrupt mask, the ABI audit missed old-layout C paths, and RV32 six-register
  compatibility returned `ENOSYS`. No runtime, SimpleOS, QEMU, bootstrap, or
  fourth cycle exists. Resume through
  `doc/08_tracking/bug/theme_ipc_k2_review_hard_stop_2026-07-27.md`.

- continuation-2026-07-30-native-theme-package-repair: **SOURCE REPAIR /
  HIGHEST-CAPABILITY ACCEPT / RUNTIME UNVERIFIED.** Audit found that
  `14ed678bc8` had overwritten the native-safe theme material serializer from
  `892e467f74`, reopening its native `rt_to_string` failure, and that the
  installed `ThemePackage` did not project the package CSS semantic
  info/success/warning/error colors. The scoped repair restores typed native
  scalar serialization and exact lowercase booleans, projects all four
  semantic colors from the package CSS with fail-closed parsing, and adds exact
  Aetheric assertions. Review accepted the corrected patch after CSS fallbacks
  were changed so the tests discriminate real extraction. No live runtime,
  host capture, bootstrap, or QEMU claim is made: the released runtime remains
  stale while an external source-matched incremental build is unresolved.
- continuation-2026-07-30-rendering-audit: CPU/software/CPU-SIMD/Vulkan glass
  remains a separate source task. The honest design is CPU-composited material
  uploaded through those presentation paths, never Vulkan device glass; Metal
  retains the only device-glass receipt. Web lowering is connected, but ordered
  multi-shadow and per-corner-radius fidelity remain open. Current x86 QEMU
  evidence ends in `guest-render-fault`; ARM has no admitted current
  ELF/FAT/capture, and the source-matched capsule is blocked by the
  `Result<(), E>` parser gap.
- continuation-2026-07-30-cpu-composited-glass: **SOURCE CONTRACT /
  HIGHEST-CAPABILITY ACCEPT / RUNTIME UNVERIFIED.** Concrete `cpu`,
  `software`, `cpu_simd`, and `vulkan` WM targets now request the existing
  bounded Engine2D CPU compositor through
  `engine2d-cpu-composited-material-v1`; Metal alone retains device-glass
  intent, while AUTO/generic GPU remain opaque solid fallbacks. Vulkan never
  claims device glass, and producer metadata does not claim realization:
  Engine2D's execution result remains the only execution receipt. Tests cover
  all four concrete targets, AUTO/GPU negative controls, Vulkan CPU planning,
  and a translucent custom fallback that proves command/fallback pixels are
  forced opaque while computed CPU material color stays translucent. Review
  accepted on cycle 3 after the opacity edge and misleading producer-side
  realized-target key were removed. No current binary/capture/QEMU PASS is
  claimed.
- continuation-2026-07-30-web-box-effects-cycle-cap: **P1 / NOT COMMITTED /
  NOT PUSHED.** The GUI/Web/DrawIR/Engine2D ownership and extracted modules
  passed final architecture review, including zero-layer shadows, independent
  corners, signed-i32 narrowing, and the 16,777,216-pixel work cap. The third
  review cycle found one remaining escape:
  `draw_ir_box_effects.spl::_e2d_box_legacy_shadow` checks signed-i32/work but
  not the shared legacy offset `-65536..65536` and blur `0..65536` limits.
  Thus legacy `65537` can execute after the same typed value is rejected.
  Mandatory cycle cap stops this session. Fresh scoped follow-up: add the exact
  legacy range guard before `_e2d_box_shadow_call_safe`, with boundary `65536`
  admission and offset `+/-65537` plus blur `65537` no-op pixel tests. Do not
  push the Web box-effects increment until that review passes.
- continuation-2026-07-30-web-box-effects-fresh-review: **SOURCE CONTRACT /
  HIGHEST-CAPABILITY ACCEPT / RUNTIME UNVERIFIED.** The fresh scoped follow-up
  now enforces the same inclusive legacy offset `-65536..65536` and blur
  `0..65536` bounds as typed Web shadows before geometry validation or native
  narrowing. Discriminating tests admit both offset boundaries, reject
  `+/-65537` and blur `65537`, and place the unsafe cases so an escaped guard
  would visibly paint. Independent review accepted the fix. The Web/Engine2D
  increment is eligible for scoped static integration; no runtime, host
  capture, or QEMU PASS is claimed.
