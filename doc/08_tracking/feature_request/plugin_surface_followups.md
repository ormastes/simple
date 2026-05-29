# Plugin Surface — Follow-up Feature Requests

**Status: PARTIAL** — FR-PLUG-0002 and FR-PLUG-0003 structurally implemented (pure Simple, no Rust). FR-PLUG-0001 blocked by Rust seed dependency (no manifest-routed extern path exists). FR-PLUG-0004 blocked by interpreter-mode Cranelift verification constraint. FR-PLUG-0005 Open — no runtime-slot DI parser/loader exists yet. See per-item status below.

**Verification pass: 2026-05-29** — All five items reviewed against source. No new code added (no live-`.so` fixture available; FR-PLUG-0005 is deep-work). See per-item notes below.

Tracker for items deferred during the `runtime-api-block-sugar-plugins` work
(landed 2026-04-28 across commits `717b5d62`/`8a8c9145`/`0277f590`).

Each entry below is an explicit carve-out from the v1 plugin surface — none
were silently normalized as workarounds; all should land in a follow-up
release before the surface is declared stable.

## Open Requests

### FR-PLUG-0001 — WFFI f64 calling-convention extern

- **Filed-on:** 2026-04-28
- **Filed-by:** /dev runtime-api-block-sugar-plugins (sstack Phase 7)
- **Target:** plugin / runtime
- **Priority:** P1
- **Status:** Open — RUST-BLOCKED
- **Requested-semantics:**
  Add `extern fn spl_wffi_call_f64(fptr: i64, args: [f64], nargs: i64) -> f64`
  alongside the existing i64 variant. Today WFFI is i64-only; AC-3b's
  `rt_gemm_add(double*, double*, double*, i64, i64, i64) -> void` works
  through pointer args because pointers are i64-sized, but real GEMM kernels
  also want f64 `alpha` and `beta` scalars. v1 demos drop those scalars (use
  1.0 implicit) — the static-lowering follow-up needs the real signature.
- **Acceptance-criteria:**
  - [ ] `spl_wffi_call_f64` whitelisted in interpreter alongside `*_i64`
  - [ ] Round-trip test: a plugin function with f64 args+return invoked from
        Simple via `std.plugin`
  - [ ] `doc/04_architecture/sffi_bidirectional_interop.md §9` carve-out note
        updated to reference this FR's resolution
- **Related-upfront:** `doc/02_requirements/feature/runtime_api_block_sugar_plugins.md`
  REQ-PLUG-003b
- **Related-design-doc:** `doc/04_architecture/sffi_bidirectional_interop.md §9`
- **Related-issue:** none
- **Notes:** **Rust seed rebuild required — no manifest-routed path exists.**
  Investigation confirmed: the WFFI extern dispatch lives in
  `src/compiler_rust/compiler/src/interpreter_extern/wffi.rs` (whitelisted in
  `interpreter_extern/mod.rs:1635`) and `codegen/runtime_ffi.rs:1263`.
  There is no manifest-routed extern extension mechanism — any new `spl_wffi_*`
  variant requires editing those Rust files and rebuilding the seed via
  `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`. This cannot be
  done in pure Simple. Per `feedback_extern_bootstrap_rebuild`, this blocks
  in-place pure-Simple implementation. Unblocked only when a Rust-side seed
  rebuild is explicitly scheduled.

### FR-PLUG-0002 — `.so` block-proxy constructor for `activate_plugin`

- **Filed-on:** 2026-04-28
- **Filed-by:** /dev runtime-api-block-sugar-plugins (sstack Phase 5)
- **Target:** plugin / 15.blocks
- **Priority:** P1
- **Status:** Structurally-implemented — pending live `.so` roundtrip test
- **Verification (2026-05-29):** `_SoBlockProxy` struct present and `activate_plugin`
  constructs+registers it for each `"block:"` manifest entry via `spl_dlsym` in
  `src/compiler/15.blocks/plugin_startup.spl` (see `activate_plugin` loop, FR-PLUG-0002 DONE
  comment). `TODO-FR-PLUG-0003-COMPATIBLE` at line 267 intentionally left — manifest
  `desugar_rules` wiring is speculative without a live fixture.
- **Requested-semantics:**
  `activate_plugin(name)` in `src/compiler/15.blocks/plugin_startup.spl`
  currently returns true after dlopen for `.so`-backed manifest entries but
  does NOT instantiate a `BlockDefinition` from the dlsym'd C functions —
  no WFFI-callable constructor pattern exists yet. Pure-Simple plugins
  (registered via `register_simple_plugin`) work today; `.so` block plugins
  need a small adapter that takes (keyword, lexer-mode, parse-fn-fptr) and
  produces a `BlockDefinition` whose `parse_payload` body invokes
  `spl_wffi_call_i64`.
- **Acceptance-criteria:**
  - [x] A C-side block plugin can register a new block keyword from a manifest
        (`_SoBlockProxy` struct added to `plugin_startup.spl`; `activate_plugin`
        dlsyms `<ClassName>_keyword` and `<ClassName>_parse`, constructs proxy,
        calls `register_block`)
  - [ ] `is_block("csv-from-c")` returns true after `use_plugin("csv-c-plugin")`
        (requires a live `.so` test fixture — deferred until test harness available)
  - [ ] Round-trip parse via plugin's parse-fn returns the expected BlockValue
        (same blocker as above)
- **Related-upfront:** state.md REQ-PLUG-002 (`AC-2 custom block plugin`)
- **Related-design-doc:** `doc/04_architecture/sffi_bidirectional_interop.md §9`
- **Related-issue:** none
- **Implementation:** `src/compiler/15.blocks/plugin_startup.spl` —
  `_SoBlockProxy(BlockDefinition)` struct + updated `activate_plugin` loop.
  Convention: manifest `functions: ["block:CsvBlockDef"]` → dlsym
  `CsvBlockDef_keyword()→i64` and `CsvBlockDef_parse(i64)→i64`.
- **Remaining:** live `.so` test fixture for the two unticked ACs.

### FR-PLUG-0003 — Sugar registry AST round-trip

- **Filed-on:** 2026-04-28
- **Filed-by:** /dev runtime-api-block-sugar-plugins (sstack Phase 5)
- **Target:** plugin / 15.blocks / 10.frontend.desugar
- **Priority:** P1
- **Status:** Structurally-implemented — live rewrite demo deferred (no test .so)
- **Verification (2026-05-29):** `DesugarRule` has `ast_rewrite_fn: i64` field in
  `src/compiler/15.blocks/sugar_registry.spl`. `apply_rule_ast` and
  `apply_sugar_rules_ast` implemented and exported. `desugar_collections` loop in
  `src/compiler/10.frontend/desugar/collection_desugar.spl` carries `[FR-PLUG-0003 DONE]`
  comment confirming wiring. Two spec scenarios in
  `test/feature/plugin/sugar_plugin_spec.spl` verify struct shape and sentinel round-trip.
  `[STATIC-NEXT]` marker present in both `sugar_registry.spl` and `collection_desugar.spl`.
- **Requested-semantics:**
  `apply_sugar_rules(tag, "")` in
  `src/compiler/10.frontend/desugar/collection_desugar.spl:64` consults the
  rule registry but discards the returned text — the desugar loop operates on
  AST node indices, not text payloads. v1's contract is "consultation seam
  is wired and reachable"; the actual rewrite path needs an AST→AST rule
  shape (or a text-form serialize/parse round-trip if structural rewrite is
  off-table).
- **Acceptance-criteria:**
  - [x] `DesugarRule` struct extended with `ast_rewrite_fn: i64` field; sentinel 0
        means no-op (returns node_index unchanged). `apply_rule_ast(name, node_index)`
        and `apply_sugar_rules_ast(tag, node_index)` added to `sugar_registry.spl`.
        `desugar_collections` loop in `collection_desugar.spl` now calls
        `apply_sugar_rules_ast` after each built-in rewrite arm.
  - [x] Two spec scenarios in `sugar_plugin_spec.spl` verify the struct shape
        and sentinel round-trip.
  - [ ] PERF-SUGAR-002 (`A @ B + v` → `rt_gemm_add`) demo rule actually fires
        and visibly rewrites the AST in interpreter mode — requires a native
        `.so` or a pure-Simple AST allocator to produce replacement nodes;
        deferred until test fixture available.
  - [ ] Runtime-behavior proof in a spec scenario (needs live rewrite fixture).
- **Related-upfront:** state.md AC-3a/AC-3b
- **Related-design-doc:** `doc/04_architecture/sffi_bidirectional_interop.md §9`
- **Related-issue:** none
- **Implementation:**
  - `src/compiler/15.blocks/sugar_registry.spl` — `ast_rewrite_fn` field added;
    `apply_rule_ast` and `apply_sugar_rules_ast` functions added.
  - `src/compiler/10.frontend/desugar/collection_desugar.spl` — imports
    `apply_sugar_rules_ast`; calls it inside the desugar loop after built-in arms.
  - `test/feature/plugin/sugar_plugin_spec.spl` — `ast_rewrite_fn` field added
    to local `DesugarRule` class; two new FR-PLUG-0003 scenarios added.
- **Remaining:** live AST-rewrite demo test fixture for unticked ACs.

### FR-PLUG-0004 — Static lowering / fusion of sugar rules through Cranelift

- **Filed-on:** 2026-04-28
- **Filed-by:** /dev runtime-api-block-sugar-plugins (sstack Phase 1 explicit defer)
- **Target:** plugin / 70.backend.cranelift
- **Priority:** P2
- **Status:** Open — VERIFICATION-BLOCKED (interpreter cannot verify Cranelift path)
- **Requested-semantics:**
  AC-3 v1 ships a *dynamic-load* sugar registry consulted by the interpreter.
  The `[STATIC-NEXT]` marker at `c_backend_translate_ops.spl:145` (the
  Cranelift matmul emit site) is the insertion point for compile-time
  specialization: when a rule's pattern matches at codegen time, emit the
  fused call directly instead of consulting the dynamic registry.
- **Acceptance-criteria:**
  - [ ] PERF-SUGAR-002 fused call emitted at codegen time when the sugar rule
        is registered statically
  - [ ] Performance delta vs. dynamic-dispatch path measured (target: ≥10%
        for the GEMM-add hot path)
  - [ ] Existing dynamic registry remains the fallback for plugins not yet
        statically known
- **Related-upfront:** state.md AC-3 (`Static fast-path is explicitly deferred`)
- **Related-design-doc:** `doc/04_architecture/sffi_bidirectional_interop.md §9`
  ("Static specialization (next release)")
- **Related-issue:** none
- **Notes:** Verification of this in interpreter mode is impossible by
  design — needs a Cranelift-mode test harness (see
  `feedback_compile_mode_false_greens.md` for current limitations).
  The `[STATIC-NEXT]` annotation at `collection_desugar.spl` (in the
  `desugar_collections` loop added by FR-PLUG-0003) marks the exact insertion
  point for this future specialisation. No code changes in this work cycle.

### FR-PLUG-0005 — DI runtime-slot plugin loader integration

- **Filed-on:** 2026-05-22
- **Filed-by:** Codex DI graph session
- **Target:** plugin / compiler / DI
- **Priority:** P1
- **Status:** Open — NOT STARTED
- **Verification (2026-05-29):** No `runtime_slot`/`RuntimeSlot`/`slot...runtime` hits
  found in any `.spl` source. `src/compiler/00.common/di_runtime.spl` is a string-keyed
  lazy engine (`di_register`/`di_resolve`) — no slot syntax. `src/compiler/00.common/di_config.spl`
  parses `config/di.sdn` for `DiServiceConfig` entries but has no slot-type concept.
  The `slot` keyword in the interpreter codebase refers to variable slots in the eval
  engine, not DI plugin slots. This FR requires parser/HIR/SDN/secure-loader work;
  blocked until design-doc (`Related-design-doc: tbd`) is written.
- **Requested-semantics:**
  Connect first-class DI runtime slots (`slot PaymentProvider runtime`,
  collection slots such as `slot [ToolPlugin] runtime named plugins`, and SDN
  `runtime_slot` bindings) to the trusted plugin/SMF loader so mixed DI graphs
  can compile the static core while loading only explicitly declared runtime
  extension points. The DI graph must remain default-first and config-minimal:
  static conventions still resolve ordinary services, and plugin loading is
  only allowed for declared runtime slots.
- **Acceptance-criteria:**
  - [ ] A mixed DI graph can resolve a runtime slot from SDN to a plugin-backed
        implementation without enabling global reflection.
  - [ ] Runtime slot loading rejects undeclared slot types, path traversal,
        absolute config/plugin paths, and final DI bindings.
  - [ ] Collection runtime slots preserve deterministic plugin order and report
        missing or duplicate plugin implementations with typed diagnostics.
  - [ ] Startup and hot resolve paths are measured against the static DI graph
        baseline, with no repeated full-tree scans in hot resolution.
- **Related-upfront:** first-class DI graph design session, 2026-05-22
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Notes:** The current DI graph work implements parser/HIR/config/SDN,
  default conventions, secure local child config loads, configurable/final
  override rules, and runtime-slot resolution APIs. This request tracks the
  remaining integration with external plugin module loading.

## Implemented

### FR-PLUG-0002 (structural) — `.so` block-proxy constructor

Implemented in pure Simple. `_SoBlockProxy(BlockDefinition)` struct added to
`src/compiler/15.blocks/plugin_startup.spl`. `activate_plugin` now dlsyms
`<ClassName>_keyword` and `<ClassName>_parse` for each `block:` function entry,
constructs a proxy, and calls `register_block`. Two live-`.so` ACs remain
unticked pending a test fixture.

### FR-PLUG-0003 (structural) — Sugar registry AST round-trip

Implemented in pure Simple:
- `DesugarRule` extended with `ast_rewrite_fn: i64` in `sugar_registry.spl`
- `apply_rule_ast` and `apply_sugar_rules_ast` functions added to `sugar_registry.spl`
- `desugar_collections` loop in `collection_desugar.spl` now calls
  `apply_sugar_rules_ast` after each built-in rewrite arm
- Two spec scenarios added to `test/feature/plugin/sugar_plugin_spec.spl`
  verifying struct shape and sentinel round-trip

Live AST-rewrite demo (PERF-SUGAR-002 firing and runtime-behavior spec) remain
unticked pending a test `.so` fixture.

## Rejected

(none)
