# Feature Expert — Tiny UI/Web/WM

## Role

Own the bounded Tiny profile that connects shared UI semantics to an embedded fullscreen browser through TinyPane, TinyDrawStream, software Tiny 2D, and mandatory Tiny WM kiosk policy.

## Invariants

- Tiny is a strict shared-architecture profile, not a rival UI/Web/WM stack.
- Tiny WM owns final root/popup, input, damage, and present policy.
- TinyDrawStream is compact execution encoding; DrawIR/WebIR remain optional semantic/diagnostic adapters.
- Software rendering is mandatory and the correctness oracle; strict Vulkan never silently falls back.
- Every collection and parser/stream traversal is bounded with an explicit failure receipt.
- Embedded deployment groups individually addressable classes into feature packs.
- Static ELF, PT_LOAD payload, and mandatory dynamic closure are separate size claims.

## Entry points

- State: `.spipe/tiny_ui_web_wm/state.md`
- Architecture/design: `doc/04_architecture/tiny_ui_web_wm.md`, `doc/05_design/tiny_ui_web_wm.md`
- Source: `src/lib/nogc_sync_mut/tiny/`, `src/os/services/tiny_wm/`, `src/os/apps/tiny_browser/`
- Specs: `test/{01_unit,02_integration}/lib/tiny/` and `test/03_system/app/tiny_browser/feature/`
- Guide: `doc/07_guide/app/ui/tiny_ui_web_wm.md`

## Known state

Implementation is active. Do not claim RV32 fullscreen/input or the 409,600-byte gate until retained R0-R4/S0 evidence exists and the highest-capability review accepts it.

The browser/WM boundary uses retained owner mutation: call mutable methods on `self.wm` and `self.present` directly. A local-copy/mutate/reassign sequence is the tracked hypothesis for the isolated-unit/integrated-browser mismatch; it is not verified until B-1's pure-Simple integration command passes. Interaction setup admits the root before keyboard/text dispatch; wheel events route through WM before changing bounded scroll state.

The executable system spec intentionally retains fail-closed H4/R4, R0-R4, and S0 scenarios. Do not remove, skip, or count them as passing; replace each only with retained descriptor/device/target/size evidence and regenerate the manual with the pure-Simple runner.

Current production gaps are not only missing target evidence. The backend boundary must carry the versioned `TinyDrawStreamV1` envelope, presentation must identify the rendered surface/pixels and matching checksum, WM routing must constrain GUI dispatch, and every accepted state change must drive repaint -> damage -> present. `tiny_resource_request` is metadata validation, not a `TinyWebHostPortV1` implementation; component-map presence is not Row/Column/Stack/List/ScrollPane behavior. Track these under B-10 through B-13.

## Update rule

Update this file with new owners, traps, measured limits, and verified commands in the same change as the implementation.
