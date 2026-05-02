# UI Typed Core — Phase 11+ Roadmap

Tracking follow-ups from the UI Typed Core migration (RFC: `doc/05_design/ui_typed_core_rfc.md`).
Current commit: 8c091c1.

## Compiler-track (blocks several items below)

### 11.1 Plumb SymbolTable through resolve_methods
What: Pass a real `SymbolTable` into `resolve_methods` instead of the empty-table workaround used in the partial unstub.
Why: Lets `MethodResolver` find instance methods directly rather than always falling through to UFCS. Required for correctness when method and UFCS names collide.
Where: `src/compiler/` — method resolution layer (resolve_methods / MethodResolver).
Dependency: none; prerequisite for 11.2.

### 11.2 MethodResolver for trait method dispatch
What: Extend `MethodResolver` to look up trait impls for typed trait calls (e.g. `IntoAction.into_action()`), not just fall back to UFCS.
Why: Typed trait dispatch is needed for `Action`/`IntoAction` pipeline (Phase 5) to work without UFCS workarounds.
Where: `src/compiler/` — method resolution layer; caller in `src/lib/common/ui/event.spl`.
Dependency: 11.1.

### 11.3 Bare-enum literal callsites
What: Once `doc/05_design/compiler_rfc_bare_enum_literals.md` lands, simplify call sites that currently use qualified form (`Toast(..., StatusVariant.Success)` → `Toast(..., Success)`).
Why: Reduces boilerplate at every typed-action / status-variant call site across UI and app code.
Where: `src/lib/common/ui/`, `examples/ui/`, any app code using `StatusVariant`/`Accent`/`LayoutKind`.
Dependency: bare-enum RFC merged and compiler support shipped.

### 11.4 Chain syntax in examples
What: Once `doc/05_design/compiler_rfc_method_chain_fix.md` lands, update `examples/ui/fluent/method_modifiers_example.spl` to use true dot-chains (`node.width(120).height(40).accent(Primary)`) instead of intermediate-`var` form.
Why: Phase 3 shipped methods but deferred chain syntax pending compiler fix (RFC §4.1 risk 3).
Where: `examples/ui/fluent/method_modifiers_example.spl`.
Dependency: chain-fix RFC merged and compiler support shipped.

## UI-track

### 11.5 Typed Color/Rgba
What: Replace the ~50 hex/rgba color string literals in the UI library with a typed `Color`/`Rgba` enum/struct.
Why: Explicit non-goal of Phases 0–10 (RFC §1.2); a parallel agent may be implementing this now — reference that work, do not duplicate.
Where: `src/lib/common/ui/` — theme files, token files, style.spl; see `doc/01_research/ui_modernization_plan.md:101`.
Dependency: none (orthogonal to wire format).

### 11.6 Delete duplicate with_* helpers
What: Remove the ~50 free `with_*` builder functions once UFCS dedup (`doc/05_design/compiler_rfc_ufcs_dot_operator.md`) is shipped and the Phase 3 fluent methods are the sole API.
Why: RFC §7 risk 7 — two API styles confuse users; lint marks `with_*` legacy after Phase 8.
Where: `src/lib/common/ui/builder.spl:340-459`.
Dependency: UFCS RFC shipped; Phase 3 methods stable for one release cycle.

### 11.7 Remove Phase 7 deprecation shims
What: Delete the six `pub use` forwarding shims left at the old `common.ui.ios_*` / `common.ui.glass_*` paths after Phase 7.
Why: Shims were intentionally left for one release cycle (Phase 6 gate row, completed 2026-04-17); removal is the planned next step.
Where: `src/lib/common/ui/ios_*.spl` and `src/lib/common/ui/glass_*.spl` shim files (6 files).
Dependency: one release after 2026-04-17; verify no remaining consumer references.

### 11.8 Hard-deprecate stringly authoring (lint → error)
What: Promote Phase 8 lint rules UI001/UI002/UI003 from warnings to errors after one release cycle.
Why: Phase 8 intentionally shipped as warnings to allow callsite migration; bumping to error enforces the typed-core contract.
Where: `src/lib/lint/ui/` — rule severity config; `src/compiler/90.tools/lint/main.spl`.
Dependency: Phase 8 complete (done 2026-04-17); wait one release cycle before flipping.
