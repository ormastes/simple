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
implementation-blocked-native-to-i64-and-exact-current-live-evidence

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
- continuation-2026-07-26-theme-package-native-boundary-regression: Current
  origin still projected `ResolvedThemePackage` across the known-broken native
  aggregate return ABI in hosted WM startup and Web CSS generation, allowing a
  nil-receiver trap before generated fallback/theme application. Hosted startup
  now uses only an active durable snapshot or the generated immutable Aetheric
  snapshot. Web package ownership remains dynamic but crosses the module
  boundary only as scalar CSS/fingerprint text, and installed CSS is accepted
  only on exact fingerprint equality. The owner exports both scalar projections.
  Focused host bootstrap contract passes 6/6 and Web CSS authority passes 5/5;
  independent source review accepts the boundary repair. The underlying generic
  aggregate-return compiler bug remains open and the production bypass must stay
  until its native regression passes.
- continuation-2026-07-26-bounded-metal-and-phase2-gates: Pushed reviewed
  diagnostics through `eca95ca8cf`. The Metal gate compiles the exact production
  MSL source through the typed provider API, supervises the complete process
  group/FIFO drains, and requires exact availability/init/device/compiler/
  library/cleanup semantics; it remains explicitly blocked before native run
  because the trusted Metal manifest is absent. The phase-2 source-reclamation
  gate now avoids the heavyweight compiler test closure, scopes source-order
  checks to exact bodies with false-green controls, attests the pure-Simple
  artifact, and bounds the entire process tree and streams. It remains runtime
  BLOCKED until a compatible self-hosted binary produces alias free results
  exactly `1,0`; no Stage-4 or historic 0/0 result is accepted.
- continuation-2026-07-26-frozen-qemu-source-admission: Pushed `cb0eb1d818`.
  x86 and ARM producers now require a clean linked worktree, exact revision,
  entry/compiler/build-command/output identities, and pre/post source
  fingerprints. The ignored generated source tree is included after
  deterministic normalization, while ARM QMP consumption cross-checks the
  build and frozen manifests. This prevents the prior changing-root build from
  becoming evidence. No new build or QEMU launch was performed, so x86/ARM
  pixels, SIMD receipts, and ordered input events remain open.
