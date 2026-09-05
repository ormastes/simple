# Tiny UI/Web/WM developer guide

## Current capability

The B-10 through B-14 host source repair is implemented, including retained
Web/GUI arenas. Runtime conformance is still blocked, so the repository does
not advertise a completed RV32 browser, zero hidden post-init allocations, or
a verified 409,600-byte closure. Use `.spipe/tiny_ui_web_wm/state.md` for
acceptance state and `doc/03_plan/agent_tasks/tiny_ui_web_wm.md` for ownership.

## Architecture rule

Tiny is a strict profile of shared Simple UI/WM semantics. Producers resolve `TinyPane` geometry and emit `TinyDrawStreamV1`; software or optional strict Vulkan executes the stream; Tiny WM owns root/popup admission, focus/capture, damage, and present policy. Do not add an app-private font path, web-only compositor, second semantic IR authority, or optional-pack import into the base.

## Frozen interfaces

`TinyModuleV1`, `TinyRect`, `TinyPane`, `TinyEvent`, `TinyDrawStreamV1`, `TinyRenderedSurfaceV1`, `TinyWebHostPortV1`, `Tiny2DBackendV1`, `TinyWmPortV1`, `TinyPresentPortV1`, and `TinyInputPortV1` change only through the contract-owner review recorded in the SPipe state. The backend accepts the versioned envelope and presentation accepts the exact rendered-surface receipt; raw words or a damage-only present call are not equivalent.

## Development order

1. Prove bounded common, pane, ABI, draw validation, and software pixels.
2. Add GUI/Web semantics and one host nested-pane fixture.
3. Integrate linked Tiny WM and the browser capsule.
4. Generate and review the Modern SSpec manual.
5. Run distinct RV32 build, headless, fullscreen, input, module, and size gates.

Never treat QEMU boot as display/input evidence, a screenshot as interaction evidence, LTO flags as size evidence, or software fallback as Vulkan success.

## Focused verification

Use the repository-managed pure-Simple Stage-4 binary when available and record its resolved path/version. Run each unchanged green criterion once. Focused unit/integration/system specs precede lint, duplicate-check, source checks, direct-runtime guards, generated-manual review, RV32 evidence, and final verification. The Rust bootstrap seed is diagnostic only.

Until such a binary has a current admission receipt, record `TEST_BLOCKED` for
focused tests, docgen, and `sspec-maintain`; static source-contract guards may
pass but must not be promoted to runtime PASS.

## Retained arena contract

`TinyBrowser.create` preallocates token, parse-node/stack/suppression, CSS
declaration, layout-node/pane/style/visibility, paint-record, and GUI
node/resolved-pane stores. Product rendering and event dispatch reset logical
counts and overwrite slots; they do not replace these owners. Consumers must
iterate `token_count`, `node_count`, `declaration_count`, `style_count`,
`pane_count`, and `record_count`, never the backing array length.

`TinyBrowser.arena_receipt()` reports twelve constructor-owned backing stores,
aggregate reuse, and current logical extents. A stable count plus increasing
reuse is the source-level B-14 oracle. It is not evidence of hidden runtime
allocator behavior; capture that separately with the admitted runtime. Legacy
standalone helpers remain compatibility APIs and allocate their own temporary
arena by design.

## Active implementation boundaries

The current source snapshot has B-10 through B-14 structural repairs but is
runtime-unverified. Do not treat module names or in-band counters as executable
proof that the frozen contracts are connected:

- backend execution must consume a validated `TinyDrawStreamV1` envelope, not only raw words;
- presentation must bind the rendered surface/pixels and checksum, not only a damage list;
- built-in/ROM/VFS loading must implement `TinyWebHostPortV1`; metadata validation is not resource delivery;
- CSS/attributes and every base component need production layout/draw/event consumers;
- WM-routed identity must constrain GUI dispatch, and edits/scroll/navigation must repaint, damage, and present;
- surface handles, focus/routing lifecycle, and registry class IDs must remain unique across removal and module boundaries.

The canonical open findings and resume conditions are B-6 through B-14 in the Tiny integration blocker record. B-14 source is complete; only qualified compilation, focused behavior, and allocator-instrumented loop evidence can close it.

The linked browser must mutate retained `self.wm` and `self.present` owners directly. The copied-owner path is the current hypothesis for the integrated root/direct-present mismatch even though the isolated WM scenario appeared correct; keep blocker B-1 open until the pure-Simple integration spec passes. Interaction-only fixtures admit the root before WM-gated keyboard or text dispatch. Wheel events first route through Tiny WM hit/capture policy, then update the bounded browser scroll state.

Current fail-closed rows are H4/R4 descriptor and strict-Vulkan evidence, RV32 R0-R4, and size S0. Their exact resume commands and evidence lists are in `doc/03_plan/agent_tasks/tiny_ui_web_wm.md`; the system spec intentionally fails those rows until real artifacts replace them. A generated manual carrying the stale-handoff notice is not final manual evidence.

## Key references

- Requirements: `doc/02_requirements/{feature,nfr}/tiny_ui_web_wm.md`
- Architecture: `doc/04_architecture/tiny_ui_web_wm.md`
- Design: `doc/05_design/tiny_ui_web_wm.md`
- Test plan: `doc/03_plan/sys_test/tiny_ui_web_wm.md`
- Feature expert: `doc/00_llm_process/feature_expert/tiny_ui_web_wm/skill.md`
