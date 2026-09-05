<!-- codex-design -->
# Tiny UI/Web/WM parallel-agent plan

## Shared rules

The contract owner freezes `TinyModuleV1`, `TinyRect`, `TinyPane`, `TinyEvent`, `TinyDrawStreamV1`, `TinyRenderedSurfaceV1`, `TinyWebHostPortV1`, `Tiny2DBackendV1`, `TinyWmPortV1`, `TinyPresentPortV1`, and `TinyInputPortV1` before fan-out. `TinyRenderedSurfaceV1` is the contract-owner-approved B-10 receipt added after independent review so presentation binds the exact backend result. Other lanes consume these interfaces and request changes through a small RFC. Each lane owns separate paths and delivers code, real tests, mapping evidence, dependency delta, and size delta.

Merge owner: primary Tiny stack integrator. Final reviewer: best available normal/highest-capability model. Broad inventory/differential/size exploration may use Codex Spark, Claude Haiku, or Claude Sonnet sidecars; contract acceptance, exclusions, generated-manual quality, and done marks require the final reviewer.

The manual step/helper/checker names and fail-fast placeholder policy are frozen in `doc/03_plan/sys_test/tiny_ui_web_wm.md` before implementation sidecars start.

## Wave 0: baseline and freeze

Parallel lanes: current dependency/symbol inventory; component mapping census; ABI/profile contract; reproducible size laboratory; fresh RV32 platform probe; compositor/WM extraction inventory.

Gate G0: empty RV32 baseline recorded, contracts and capacities approved, ownership map committed, and no unresolved conflict with shared UI/WM authority.

## Wave 1: common substrate

Parallel lanes: Tiny Lib; Tiny Pane; static registry and thin SFM bridge; TinyDrawStream writer/validator; size-report integration.

Gate G1: a nested-pane host fixture emits and replays a validated stream within the `tiny-min` budget, and static/dynamic descriptors report equal capabilities.

## Wave 2: vertical libraries

Parallel lanes after G1: Tiny GUI; Tiny TUI; HTML parser; CSS/style; Web layout/hit; software Tiny 2D; Tiny WM kiosk; host present/input ports.

Gate G2: the admitted page renders under host Tiny WM with nested clipping, focus, scrolling, button, and popup; TUI differential fixtures pass; dependency audit finds no full renderer/compositor import.

## Wave 3: product and adapters

Parallel lanes after G2: browser ECS capsule; web forms/events; strict host Vulkan; DrawIR adapter; WebIR adapter; shared-WM/full-scene adapter; popup/cursor packs; differential corpus.

Gate G3: the host software browser is interactive, Vulkan succeeds with device/readback evidence or fails explicitly, and all compatibility packs remain absent from the RV32 base closure.

## Wave 4: RV32 and closure

Parallel lanes after G3: RV32 entry/resource port; headless RGB565 render; framebuffer/virtio-gpu present; physical input; measured size reduction; dynamic closure proof; generated docs/evidence.

Gate G4: fresh boot, headless frame, fullscreen present, input, optional-module, and size gates have their required evidence. Do not claim R2/R3 before those distinct gates pass.

## 2026-08-16 implementation handoff

The owned browser/WM repair removes copied-owner mutation at the direct-present boundary: `TinyBrowser` now mutates its retained WM and present ports directly, and interaction-only setup admits the kiosk root before keyboard/text routing. Focused unit, integration, and system sources cover retained root state, exact direct-present geometry, pointer capture/release, and wheel scrolling. These edits are not PASS evidence until the pure-Simple commands below run once.

Active blocked rows remain part of this plan:

- H0/H3 resume: `bin/simple test test/01_unit/lib/tiny/tiny_wm_kiosk_spec.spl test/01_unit/lib/tiny/browser_memory_ports_spec.spl test/02_integration/lib/tiny/tiny_browser_stack_it_spec.spl --mode=interpreter --no-session-daemon --timeout 90`.
- System/manual resume after focused PASS: `bin/simple test test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl --mode=interpreter --no-session-daemon --timeout 90`, followed by `bin/simple spipe-docgen test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl --output doc/06_spec --no-index` and `bin/simple sspec-maintain scan test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl`.
- H4/R4 remain fail-closed until descriptor parity, excluded-pack closure, and strict Vulkan device/readback receipts exist.
- R0-R4 remain fail-closed until fresh RV32 build/boot, RGB565, fullscreen present, physical input, and module receipts exist.
- S0 remains fail-closed until stripped ELF, PT_LOAD, section, symbol, dependency, module-delta, and reserve evidence proves the 409,600-byte limits.
- Core boundedness source work now includes saturating geometry, typed generational pane lookup, preallocated counted DrawStream storage, and preallocated software-2D execution stacks. Commit `544428e1343550cf3f589d8d3a50511d7f4b93a9` has one-pass `STATIC_PASS`; retained-allocation and executable evidence remain open under B-6.
- Product boundedness source work now uses preallocated WM/present/input storage with explicit logical counts; `cda76b5e357d2af31281f5ddf386229b7f1720fa` adds retained preallocated pixel copying plus an isolation oracle. Runtime capacity/allocation proof remains open under B-7.
- REQ-009 source work now includes an optional non-exported `TinyWmServiceCapsule` and linked/service parity spec (`b3ac80d951f8ac4c0f3fdb5d661dac5b45c690b3`). Executable parity, ABI rejection, and excluded-pack evidence remain open under B-8.
- AC-7 source work now includes compatible V2 valid-empty resource admission, retained navigation/repaint state, and separately rasterized visible popup content. Commit `b170f8bd370fbdef992873a6f29d4dd8d1cd0faa` adds built-in/ROM/VFS integration/system parity scenarios; executable product evidence remains open under B-9.
- Frozen execution/presentation remains open: carry `TinyDrawStreamV1` rather than raw words across the backend port and bind presented pixels/surface identity to the software checksum (B-10).
- Web/component semantics remain open: connect admitted attributes and bounded CSS to computed layout, implement `TinyWebHostPortV1`, suppress non-rendered document content, and implement every base component rather than metadata-only declarations (B-11).
- Event-to-frame ownership remains open: constrain GUI delivery by the WM routed target and drive edits/wheel/navigation through repaint, damage, and present with before/after evidence (B-12).
- WM/registry lifecycle remains open: stable generational surface identity, capacity/focus cleanup, separate bounds/clip, and cross-module class uniqueness require implementation and focused coverage (B-13).
- Web/GUI arena boundedness remains open: token/parser/CSS/layout/paint/GUI/resolved-pane storage must be preallocated with logical counts and reset in place, and per-event resolved-pane allocation must be removed before NFR-011 can pass (B-14).

The independent highest-capability review on 2026-08-16 returned `STATUS: FAIL`. It accepted the blocker disclosure as directionally truthful but rejected any done or internally-consistent-completion claim. The review itself is complete; its findings remain merge-owner work and must not be downgraded to runner-only `BLOCKED`.

Runner-independent gates executed once on 2026-08-16: generated-spec layout `0`; direct-env/runtime guard working and staged `PASS`; rendering-source-coupling `PASS`; staged numbered-artifact guard `PASS`; Tiny-owned static scan found no `pass_todo`, raw `rt_*`, or prohibited boolean-wrapper assertions. The working numbered-artifact guard failed on unrelated `.claude/worktrees.pre_migrate_backup/**` content and is not attributable to Tiny. Both local Simple candidates failed provenance admission, so no Tiny test, lint, duplicate-check, docgen, sspec-maintain, RV32, Vulkan, or size command ran. The Rust seed was not used.

Merge owner remains `/root`; final reviewer remains the highest-capability `/root` reviewer. The fail-closed system scenarios are deliberate completion blockers, not passing placeholders.

Checkpoint review on 2026-08-16 inspected the exact 68-path source commit `6a72812917a205eb471e4b921fd9b6cd04dca187`. It found stale popup assertions that confused absolute `resolved` geometry with effective `clip`; follow-up `eb6e0f568303d650355b2d53b25de4b69d7a9f31` now asserts `resolved = 40x40` and `clip = 20x20` in both integration and system sources. The same highest-capability reviewer returned `PASS-for-checkpoint` for that corrected criterion. This is static checkpoint evidence only: B-6 through B-9, the deliberate fail-closed scenarios, and all executable gates remain open.

The bounded source follow-ups are preserved linearly on `codex/tiny-checkpoint-01a00036-20260816` through `544428e1343550cf3f589d8d3a50511d7f4b93a9`. The counted-stream slice changed exactly ten paths with tree file count unchanged (`114396 -> 114396`) and passed its single runner-independent static gate. No runtime, lint, docgen, RV32, Vulkan, or size PASS is inferred from that result.

## Ownership boundaries

- Contract owner: common ABI/profile and generated manifest schema.
- Library owners: one owner each for `common`, `pane`, `draw`, `gui`, `tui`, `web`, and software `engine2d`.
- WM owner: `src/os/services/tiny_wm/**`; aspect owners are restricted to their aspect folder.
- Browser owner: `src/os/apps/tiny_browser/**`.
- Platform owners: RV32 present and input adapter paths only.
- Evidence owner: build/size scripts and reports, not implementation folders.
- Docs owner: generated mapping/spec manuals only after implementation evidence exists.

No lane edits another lane's dirty files, imports host adapters into target code, changes existing dynSMF defaults, or consumes the 68 KiB reserve silently.
