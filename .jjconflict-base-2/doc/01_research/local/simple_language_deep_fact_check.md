<!-- codex-research -->
# Simple Language Article Deep Local Fact Check

Date: 2026-06-07

Subject: `doc/07_guide/language/simple_language.md`

Method: six parallel research lanes inspected README/VERSION/CHANGELOG, language safety surfaces, verification/SPipe/SDoctest, UI/web/rendering/debug tooling, runtime/backends, and external comparisons. This file records the local repo evidence only.

## Summary

The article thesis is broadly supported: Simple is best described as a toolchain that turns common LLM-generated-code failure modes into compiler, lint, test, architecture, or verification gates.

The article needed three kinds of adjustment:

1. Some safety claims were too absolute: exhaustive matching is a lint that can be denied, not always a compile error; `high-robustness mode` is not a proven named mode; `nil`/`Option` is the safer no-null wording.
2. Runtime and pointer claims were too specific: runtime families are bounded; target-preset import restriction was not proven; handle-pointer pool semantics should be described as a supported direction with syntax/runtime hooks, not a finished checked-pool guarantee.
3. UI status was understated: native/user-facing GUI remains unfinished, but web/TUI-web test protocol, Draw IR Protocol v2, HTML/CSS browser rendering, UI-access MCP tools, and WASM GUI contracts exist in bounded form.

## Release And Status Evidence

Supported:

- `VERSION` is `1.0.0-beta`.
- `CHANGELOG.md` has `[1.0.0-beta] - 2026-05-20`.
- README has a historical suite snapshot: `4,067/4,067` passing on `2026-02-14` in `17.4 seconds`.
- README splits claims into `Implemented and safe to advertise`, `best described with qualifiers`, and `Implemented with bounded scope`.
- README binary install snippets still point at older `v0.6.1`, while source checkout path is `https://github.com/simple-lang/simple.git`.

Article impact:

- Keep `1.0.0-beta`.
- Keep test count as a dated README snapshot, not as a current fresh test run.
- Keep source checkout install block rather than hardcoded release asset URL.

## Testing, SPipe, And Documentation Evidence

Supported:

- SPipe mock policy supports full/system ban, HAL-only, and custom modes.
- Integration tests prove `Mock.new`, `Spy.new`, and `Stub.new` are blocked in system mode.
- Anti-dummy / anti-stub enforcement exists in lint and verify gates.
- SPipe BDD exports `describe`, `context`, `it`, `expect`, and built-in matchers.
- SDoctest runner extracts and runs Markdown/code examples; `--sdoctest` is wired in runner args.
- `doc/06_spec` is documentation output only; executable specs belong under `test/**`.
- `simple build check --full` is documented as coverage plus duplication detection; coverage and duplication tools/tests exist, though this pass did not trace the exact command chain.

Article impact:

- Name SPipe explicitly in the living-docs and status sections.
- Keep mock ban, anti-stub, SDoctest, generated docs, coverage, and duplication claims.
- Treat `--doctest` alias with caution unless source wiring is checked.

## Language Safety Evidence

Proven:

- Primitive-public-API lint exists.
- `unit` and `newunit` syntax are backed by README and parser support.
- Parser-friendly macro registry/validation exists.
- Explicit public boundaries through `__init__.spl` and structured exports are linted.

Qualified:

- User-facing absence uses `nil`, `Option`, `Some`, optional type syntax, and `?` propagation. Internal/FFI docs still mention null, so publish as "no user-level null; absence is explicit."
- Exhaustiveness checks exist for enum/bool/Option/Result matches, but default severity is warning. Deny-level configuration can turn it into an error.
- Borrow-checking infrastructure exists, but this is not a full Rust-style borrow checker claim.

Unsupported or over-specific:

- A named `high-robustness mode` for match exhaustiveness was not found.
- `GC` as a pointer kind was not proven. Parser evidence supports unique/shared/weak/handle plus borrow/raw variants; GC is better described through runtime families.
- Full handle-as-bounds-checked-pool semantics were not proven beyond syntax/runtime hooks and related concepts.
- "No `*` export" is proven for structured exports, not as a universal language statement.

Article impact:

- Replace `high-robustness mode` with deny-level lint configuration.
- Qualify `no null` as no user-level `null`.
- Replace five-pointer claim with "ownership/lifetime forms include unique/shared/weak/handle; GC is a runtime-family property."
- Move handle-pool semantics from shipped fact to bounded/conceptual rationale.

## UI, Web, WASM, Draw IR, And Debug Evidence

Supported, bounded:

- Shared UI contract says web backend and TUI-web proxy are protocol-stable, while pure Simple GUI/Electron/Tauri are lower-stage targets.
- `ui.tui_web` server wraps TUI as HTML and delegates `/api/test` to shared handler.
- Standalone TUI exists but is minimal/smoke-level.
- Browser engine guide describes HTML/CSS/rendering status as much stronger than "no rendering layer."
- Web render API names web, Electron, Tauri, Chromium, pure Simple, TUI-web, and WASM targets.
- WASM GUI guide describes artifact/contract readiness while linker path hardening remains.
- Draw IR Protocol v2 exists in `std.ui`/test API paths and has generated spec docs.
- UI access docs and MCP schemas expose snapshot/find/act style protocol for LLM-driven UI work.

Article impact:

- Replace "GUI does not work yet" with "native/user-facing GUI remains unfinished; web/TUI-web protocol, Draw IR, HTML/CSS renderer, WASM contracts, and UI-access MCP tooling are bounded implemented surfaces."

## Runtime, Backend, And Systems Evidence

Shipped or supported:

- Native/LLVM compile path and linker support exist.
- mmap-backed loader / executable-memory plumbing is documented.
- SFFI support matrix covers imports, exports, callbacks, layout verification, and tests for the supported subset.
- Performance benchmark infrastructure exists, but not a Simple-vs-Rust raw speed claim.

Bounded:

- Runtime families are documented, but portable parity evidence focused on `gc_async_mut`, `nogc_async_mut`, and `nogc_sync_mut`.
- Deep-learning examples exist; broader autograd runtime specs remain in progress by target/backend.
- GPU/CUDA claims need backend-specific qualifiers.
- VHDL/FPGA/RV32/baremetal claims are target- and lane-scoped, not arbitrary Simple-to-FPGA.
- AOP exists with support matrix constraints and runtime resolution caveats.

Unsupported:

- Automatic target-preset module restriction for `Baremetal`, `Hosted`, and `EmbeddedWithHeap` was not proven in this pass.

Article impact:

- Keep LLVM, loader, SFFI, VHDL, baremetal, AOP, and GPU claims, but preserve bounded-scope wording.
- Remove or qualify automatic target-preset import restriction.
