# Plugin Surface — Follow-up Feature Requests

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
- **Status:** Open
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
- **Notes:** Must NOT be added by `bin/simple` rebuild without first verifying
  whether the existing manifest path can host the new variant; per
  `feedback_extern_bootstrap_rebuild`, new compiled-in externs require Rust
  seed rebuild — investigate whether a manifest-routed extension is feasible.

### FR-PLUG-0002 — `.so` block-proxy constructor for `activate_plugin`

- **Filed-on:** 2026-04-28
- **Filed-by:** /dev runtime-api-block-sugar-plugins (sstack Phase 5)
- **Target:** plugin / 15.blocks
- **Priority:** P1
- **Status:** Open
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
  - [ ] A C-side block plugin can register a new block keyword from a manifest
  - [ ] `is_block("csv-from-c")` returns true after `use_plugin("csv-c-plugin")`
  - [ ] Round-trip parse via plugin's parse-fn returns the expected BlockValue
- **Related-upfront:** state.md REQ-PLUG-002 (`AC-2 custom block plugin`)
- **Related-design-doc:** `doc/04_architecture/sffi_bidirectional_interop.md §9`
- **Related-issue:** none
- **Notes:** The pure-Simple path is enough for v1's spec coverage — this FR
  closes the C-side path that arch.md lists as supported.

### FR-PLUG-0003 — Sugar registry AST round-trip

- **Filed-on:** 2026-04-28
- **Filed-by:** /dev runtime-api-block-sugar-plugins (sstack Phase 5)
- **Target:** plugin / 15.blocks / 10.frontend.desugar
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  `apply_sugar_rules(tag, "")` in
  `src/compiler/10.frontend/desugar/collection_desugar.spl:64` consults the
  rule registry but discards the returned text — the desugar loop operates on
  AST node indices, not text payloads. v1's contract is "consultation seam
  is wired and reachable"; the actual rewrite path needs an AST→AST rule
  shape (or a text-form serialize/parse round-trip if structural rewrite is
  off-table).
- **Acceptance-criteria:**
  - [ ] `DesugarRule.rewrite_fn` accepts an AST node and returns either the
        original (no-op) or a replacement AST node
  - [ ] PERF-SUGAR-002 (`A @ B + v` → `rt_gemm_add`) demo rule actually fires
        and visibly rewrites the AST in interpreter mode
  - [ ] One spec scenario in `sugar_plugin_spec.spl` proves the rewrite
        affected runtime behavior (today: scenarios 8/9 are deferred placeholders)
- **Related-upfront:** state.md AC-3a/AC-3b
- **Related-design-doc:** `doc/04_architecture/sffi_bidirectional_interop.md §9`
- **Related-issue:** none
- **Notes:** Tagged with `[STATIC-NEXT]` markers at three sites
  (`sugar_registry.spl:19`, `collection_desugar.spl:203`,
  `c_backend_translate_ops.spl:145`) — those are insertion points but the
  static path itself is FR-PLUG-0004.

### FR-PLUG-0004 — Static lowering / fusion of sugar rules through Cranelift

- **Filed-on:** 2026-04-28
- **Filed-by:** /dev runtime-api-block-sugar-plugins (sstack Phase 1 explicit defer)
- **Target:** plugin / 70.backend.cranelift
- **Priority:** P2
- **Status:** Open
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

## Implemented

(none yet)

## Rejected

(none)
