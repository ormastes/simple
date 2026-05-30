# Plugin Surface — Follow-up Feature Requests

**Status: PARTIAL** — FR-PLUG-0001 is implemented in source and verified with a rebuilt debug driver. FR-PLUG-0002 and FR-PLUG-0003 are structurally implemented (pure Simple, no Rust). FR-PLUG-0004 now has pure-Simple static-marker verification, Cranelift single-op runtime-call emission for `MatMul` and broadcast ops, and a bounded Cranelift adjacent-pattern fusion gate that emits one GEMM-add runtime import for `MatMul` immediately consumed by `BroadcastAdd`. Linkable runtime GEMM-add and measured perf delta remain blocked on a real runtime/plugin symbol and shape/dimension ABI. FR-PLUG-0005 is implemented as an explicit DI runtime-slot index with plugin-backed binding validation and deterministic resolution. See per-item status below.

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
- **Status:** Implemented (2026-05-29)
- **Requested-semantics:**
  Add `extern fn spl_wffi_call_f64(fptr: i64, args: [f64], nargs: i64) -> f64`
  alongside the existing i64 variant. Today WFFI is i64-only; AC-3b's
  `rt_gemm_add(double*, double*, double*, i64, i64, i64) -> void` works
  through pointer args because pointers are i64-sized, but real GEMM kernels
  also want f64 `alpha` and `beta` scalars. v1 demos drop those scalars (use
  1.0 implicit) — the static-lowering follow-up needs the real signature.
- **Acceptance-criteria:**
  - [x] `spl_wffi_call_f64` whitelisted in interpreter alongside `*_i64`
  - [x] Round-trip test: a plugin function with f64 args+return invoked from
        Simple via `std.plugin`
  - [x] `doc/04_architecture/sffi_bidirectional_interop.md §9` carve-out note
        updated to reference this FR's resolution
- **Related-upfront:** `doc/02_requirements/feature/runtime_api_block_sugar_plugins.md`
  REQ-PLUG-003b
- **Related-design-doc:** `doc/04_architecture/sffi_bidirectional_interop.md §9`
- **Related-issue:** none
- **Verification (2026-05-29):** Implemented in Rust seed/source and verified
  with `src/compiler_rust/target/debug/simple` after rebuilding
  `simple-driver`. Evidence:
  `cargo test -p simple-compiler spl_wffi_call_f64_invokes_function_pointer --manifest-path src/compiler_rust/Cargo.toml -- --nocapture`,
  `cargo test -p simple-runtime spl_wffi_call_f64_invokes_no_arg_function_pointer --manifest-path src/compiler_rust/Cargo.toml -- --nocapture`,
  `SIMPLE_LIB=src/compiler_rust/lib/std/src:src src/compiler_rust/target/debug/simple check src/compiler_rust/lib/std/src/plugin/__init__.spl test/feature/plugin/runtime_api_plugin_spec.spl test/feature/plugin/sugar_plugin_spec.spl`,
  and
  `SIMPLE_LIB=src/compiler_rust/lib/std/src:src src/compiler_rust/target/debug/simple test test/feature/plugin/runtime_api_plugin_spec.spl --mode=interpreter --clean --format json`
  (`8/8`).
- **Notes:** The extern still requires a Rust seed/runtime rebuild because no
  manifest-routed extern extension mechanism exists. The source implementation
  now lives in `src/compiler_rust/compiler/src/interpreter_extern/wsffi.rs`,
  `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`,
  `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`, and
  `src/compiler_rust/runtime/src/value/wsffi_native.rs`. `std.plugin` exposes
  `plugin_call_f64(...)`; the fixture at `test/feature/plugin/fixtures/demo.c`
  proves positional f64 argument/return dispatch.

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
- **Status:** Open — FUSION-CONTEXT-BLOCKED
- **Status note (2026-05-30):** Cranelift adjacent-pattern context is no longer
  fully blocked for the simplest `tmp = A @ B; out = tmp broadcast_add C` MIR
  shape. The adapter now scans adjacent instructions, requires the MatMul
  destination to be a temp used exactly once, skips the standalone MatMul, and
  emits a single `__simple_runtime_gemm_add(A, B, C)` import. This is a true
  codegen fusion for that bounded MIR shape, but FR-PLUG-0004 remains open
  because the runtime/plugin ABI for a linkable GEMM-add kernel and the required
  performance measurement are still missing.
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
- **Verification (2026-05-29):** `[STATIC-NEXT]` marker confirmed present at
  `src/compiler/70.backend/backend/c_backend_translate_ops.spl:147` (file is under
  `backend/` subdir, not `cranelift/` — path in earlier notes was incorrect).
  Also present at `collection_desugar.spl:66` and `collection_desugar.spl:222`,
  and `sugar_registry.spl:24`. No Cranelift directory exists in the backend tree;
  the backend C codegen path is the target. Status unchanged — interpreter-mode
  verification impossible by design.
- **Verification (2026-05-30):** Added pure-Simple source-marker assertions to
  `test/feature/plugin/sugar_plugin_spec.spl` for the static insertion points in
  `sugar_registry.spl`, `collection_desugar.spl`, and
  `c_backend_translate_ops.spl`. Focused run passed:
  `SIMPLE_LIB=src bin/simple test test/feature/plugin/sugar_plugin_spec.spl --mode=interpreter --clean`
  (`12/12`). This verifies the handoff markers only; fused backend emission,
  performance delta, and dynamic fallback ACs remain open.
- **Verification (2026-05-30, focused blocker evidence):** Added a
  `sugar_plugin_spec.spl` assertion for the live Cranelift adapter. The adapter
  `translate_binop(ctx, op, a, b, left_operand, func)` receives the already
  lowered operands for one binary op and its fallback arm still documents
  `Pow, MatMul, Broadcast ops: fall back to integer add` before returning
  `cranelift_iadd(ctx, a, b)`. This proves FR-PLUG-0004 cannot be honestly
  closed within plugin/sugar docs/tests alone: codegen needs a real static-rule
  table plus MIR/codegen pattern context for `MatMul` followed by
  `BroadcastAdd`, then a backend emission path for the fused GEMM-add call.
- **Verification (2026-05-30, backend advance):** Cranelift no longer lowers
  `MatMul` and broadcast binary ops through the generic integer-add fallback.
  `cranelift_codegen_adapter.spl` now routes those single MIR ops through
  imported runtime calls (`__simple_runtime_matmul`,
  `__simple_runtime_broadcast_add`, and sibling broadcast helpers), matching the
  C backend's runtime-call shape. Focused spec coverage now fails if the old
  `Pow, MatMul, Broadcast ops: fall back to integer add` text returns. The
  smallest remaining missing piece for true PERF-SUGAR-002 fusion is explicit:
  codegen still visits one `MirInst` at a time and `translate_binop` sees only
  the current op plus already-lowered operands. To emit
  `rt_gemm_add(A, B, C, m, n, k)`, MIR/codegen needs adjacent-pattern context
  for `MatMul` result consumed by `BroadcastAdd`, plus shape/dimension operands
  (`m`, `n`, `k`) carried into the fused backend call.
- **Verification (2026-05-30, bounded fusion repair):** Cranelift now scans
  each block with a one-instruction lookahead before normal instruction
  translation. `cranelift_gemm_fusion.spl` recognizes adjacent
  `BinOp(..., MatMul, A, B)` followed by `BinOp(..., BroadcastAdd, tmp, C)` or
  the commuted addend form, requires `tmp` to be a temporary with exactly one
  use across the function, and the adapter emits one
  `__simple_runtime_gemm_add(A, B, C)` import while advancing the instruction
  cursor by two. `cranelift_runtime_imports.spl` centralizes the i64-handle
  runtime import declaration/call path used by both fused and unfused matrix
  operations. Unmatched matrix ops continue through the existing
  `__simple_runtime_matmul` and `__simple_runtime_broadcast_add` fallbacks.
  Focused unit coverage in
  `test/unit/compiler/backend/cranelift_gemm_fusion_spec.spl` exercises the
  actual detector for fuse/extra-use/non-add cases. Source-level plugin coverage
  in `test/feature/plugin/sugar_plugin_spec.spl` asserts the adapter wiring, the
  single fused import, and fallback preservation.
- **Notes:** Verification of this in interpreter mode is impossible by
  design — needs a Cranelift-mode test harness (see
  `feedback_compile_mode_false_greens.md` for current limitations).
  The `[STATIC-NEXT]` annotation at `collection_desugar.spl` (in the
  `desugar_collections` loop added by FR-PLUG-0003) marks the exact insertion
  point for this future specialisation.

### FR-PLUG-0005 — DI runtime-slot plugin loader integration

- **Filed-on:** 2026-05-22
- **Filed-by:** Codex DI graph session
- **Target:** plugin / compiler / DI
- **Priority:** P1
- **Status:** Implemented (2026-05-29)
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
  - [x] A mixed DI graph can resolve a runtime slot from SDN to a plugin-backed
        implementation without enabling global reflection.
  - [x] Runtime slot loading rejects undeclared slot types, path traversal,
        absolute config/plugin paths, and final DI bindings.
  - [x] Collection runtime slots preserve deterministic plugin order and report
        missing or duplicate plugin implementations with typed diagnostics.
  - [x] Startup and hot resolve paths are measured against the static DI graph
        baseline, with no repeated full-tree scans in hot resolution.
- **Related-upfront:** first-class DI graph design session, 2026-05-22
- **Related-design-doc:** `doc/05_design/di_runtime_slots.md`
- **Related-issue:** none
- **Notes:** Added `src/compiler/00.common/di_runtime_slots.spl` and
  `test/unit/compiler/di/di_runtime_slots_spec.spl`. The runtime-slot index is
  fed by trusted plugin/SMF metadata rather than global reflection: it validates
  declared slot names/types, rejects unsafe paths and final bindings, sorts
  collection plugins by order/name/implementation, reports typed diagnostics,
  and records startup scan/hot resolve counts.

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

### FR-PLUG-0004 (verification only) — Static lowering markers

Pure-Simple verification added to `test/feature/plugin/sugar_plugin_spec.spl`
for the `[STATIC-NEXT]` handoff markers in the sugar registry, collection
desugar loop, and backend matmul lowering site. Backend fusion remains open.

## Rejected

(none)
