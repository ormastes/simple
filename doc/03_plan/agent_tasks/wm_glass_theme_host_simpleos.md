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
   generator and drift checks.
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
| Host production WM | SOURCE FIXED; recapture blocked by cycle cap | exact-current Stage 3 passed; bootstrap/theme/bridge/provider wiring is fixed, but the compiler containing the provider-link fix must be rebuilt before one fresh host capture |
| Host events | SOURCE PARTIAL; product proof pending | real key down/up and pointer move/button-edge receipts are retained; title-command/body-input remain unsupported because HostCompositor exposes no canonical API |
| Simple Web glass | SEMANTICS IMPLEMENTED, LIVE PROOF PENDING | current-source computed-style/Draw-IR/framebuffer proof has not passed; Chromium fixture timing is not Simple Web animation evidence |
| SimpleOS x86_64 QEMU | STATIC PREFLIGHT PASS, FRESH BOOT PENDING | legacy render/event command now delegates to canonical `gui_entry_desktop.spl` evidence; host gate, exact-current rebuild, and one OVMF capture remain |
| SimpleOS ARM64 QEMU | SOURCE INPUT PREFLIGHT IMPLEMENTED; LIVE PROOF PENDING | generated Aetheric startup and capability-discovered VirtIO-MMIO keyboard/pointer eventq wiring are present; DMA ordering/status/shape contracts pass locally, but the self-hosted ARM payload and QMP key/pointer/frame/RAMFB evidence are not yet available |
| Aggregate SSpec | FAIL-FAST BY DESIGN | `require_wm_glass_theme_evidence()` remains a real failure until host and required QEMU rows produce current-source evidence |
| Simple GUI theme handoff | SOURCE FIXED; product proof pending | resolved snapshot now reaches canonical widget Draw IR; 2 bootstrap-driver scenarios pass diagnostically |
| Simple Web theme authority | SOURCE FIXED; product proof pending | package CSS is now the final authority; 3 bootstrap-driver scenarios pass diagnostically |
| WM glass material projection | SOURCE FIXED; focused spec timed out | Draw IR retains durable identity/radius/border/shadows/backdrop request and named fallback; broad focused spec timed out at 120 seconds without assertions |
| Runtime theme switching | ABI BLOCKED; fail-fast system contract | numeric subscriber ports have no `IpcOutputPort`/send adapter, message schema, source identity, or delivery-failure policy |

### Current parallel ownership

1. Sidecar A: theme/CSS/WebIR/Draw-IR and Git-history audit, read-only.
2. Sidecar B: hosted production route and event/capture diagnosis, read-only;
   completed the split-theme finding above.
3. Sidecar C: x86_64/ARM64 canonical QEMU route, media/input/capture audit,
   read-only; completed and proved the ARM64 theme-install/input gaps.
4. Implementation sidecars: Web package CSS authority, WM material projection,
   and Simple GUI widget theme handoff, with non-overlapping source ownership.
5. `/root`: merge owner, host bootstrap regression/fix, compiler preflight,
   documentation, final high-capability review, sync and push.

### Next execution order

#### Scope decision — 2026-07-26

The only active execution lane on this host is the Electron/Aetheric browser
surface. Provision the repository-pinned Electron dependency with:

```sh
npm ci --prefix tools/electron-shell
export PATH="$PWD/tools/electron-shell/node_modules/.bin:$PATH"
```

Then run the full canonical producer command documented in
`doc/09_report/aetheric_host_web_gui_readiness_2026-07-26.md`; missing inputs
must fail closed. Retain its generated HTML, ARGB files, PNG, computed-style
observation, Electron log, UI-access history, proof envelope, exact hashes, and
event-routing receipt. TODO 583 owns this current-host work.

All non-Electron native execution is postponed to prepared external hosts:
the final pure-Simple bridge/runtime capsule, Vulkan/Metal/SIMD device
comparison, x86 QEMU capture/events, and ARM64 QMP framebuffer/input/NEON
receipt. These rows remain open under their existing TODOs and acceptance
criteria; postponement is not completion or exclusion.

- External compiler/GPU owner: prepared-host operator under TODO 580 and
  `doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`.
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
native/live rows remain open: Electron is active on this host, while the
compiler/GPU/QEMU rows are externally postponed. No current native Aetheric
producer or Electron proof exists, and neither x86 nor ARM has an admitted
compiler/frozen manifest for a canonical QEMU launch. The external seed-driven
x86 job is not admissible evidence. Current details and remaining gates are recorded in
`.spipe/wm-glass-theme-host-simpleos/state.md` and
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
