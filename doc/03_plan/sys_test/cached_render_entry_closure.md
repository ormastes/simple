# Cached Render Entry Closure System-Test Plan

Status: **runtime-selection source complete; `TEST_BLOCKED`**
(TODO686/TODO688).

Current lane base: `f6cadcc36aff61d16d988651ea36a040d2af6aad`.
The focused source implementation removes implicit `bin/simple` and canonical
Rust-seed worker fallback. Runtime PASS remains unclaimed.

Historical static-contract evidence on the GitHub-synced source revision
`7ac900316dd5266595d8e2d713493ed174f0c8e4`, the nine-scenario structure,
requirement traceability, stub exclusion, numbered-artifact, direct-env, and
spec-layout checks passed once. The only available unadmitted `release/`
artifact then segfaulted with exit 139 before any scenario executed, with zero
stdout. That diagnostic is runtime-blocker evidence, so the current result is
`TEST_BLOCKED`, not a failed expectation and not an admitted SSpec PASS.

Executable modern SSpecs:

- `test/03_system/check/cached_render_entry_closure_contract_spec.spl`
- `test/03_system/check/cached_render_entry_closure_runtime_selection_spec.spl`

| Requirement | Coverage |
|---|---|
| REQ-RENDER-CLI-001 | Guide exposes `CachedRenderEntryClosureV1`, links plan/bug, and labels the workflow blocked/planned. |
| REQ-RENDER-CLI-002 | Existing contract names pure-Simple owners and no-artifact policy; runtime-selection spec directly checks configured-candidate priority, canonical seed rejection, and missing-candidate nonzero preflight. |
| REQ-RENDER-CLI-003 | Plan preserves exact sparse 8K correctness, performance, identity, and executor-only boundaries. |

REQ-RENDER-CLI-002 has three direct behavioral scenarios: happy path,
canonical-seed rejection, and unavailable-candidate rejection. The remaining
requirements retain the existing discovery/boundary scenarios.

## Environment and execution order

1. Qualify an admitted pure-Simple full CLI with `test`, `sspec-maintain`, and
   `spipe-docgen`; record path, hash, stage, and provenance.
2. Run the runtime-selection spec once.
3. Run the broader cached-entry contract once.
4. Scan each changed spec once, then regenerate only its mirrored manual.

Commands after TODO682 supplies that runtime:

```sh
<admitted-simple> test test/03_system/check/cached_render_entry_closure_contract_spec.spl --mode=interpreter
<admitted-simple> test test/03_system/check/cached_render_entry_closure_runtime_selection_spec.spl --mode=interpreter
<admitted-simple> sspec-maintain scan test/03_system/check/cached_render_entry_closure_contract_spec.spl
<admitted-simple> sspec-maintain scan test/03_system/check/cached_render_entry_closure_runtime_selection_spec.spl
<admitted-simple> spipe-docgen test/03_system/check/cached_render_entry_closure_contract_spec.spl --output doc/06_spec --no-index
<admitted-simple> spipe-docgen test/03_system/check/cached_render_entry_closure_runtime_selection_spec.spl --output doc/06_spec --no-index
```

## Pass/fail and manual policy

Acceptance requires twelve examples total (nine existing plus three runtime
selection), zero failures, all seven maintenance scores reviewed for each
changed spec, zero stubs, and current mirrors under
`doc/06_spec/03_system/check/`. The selection workflow is visible; helper
source and broader carrier details remain folded. TUI capture is sufficient;
there is no GUI/raster evidence in this criterion.

Missing runtime, missing output, timeout, signal exit, seed execution, or the
known-bad release artifact is `TEST_BLOCKED`/FAIL evidence, never PASS. Source review
can complete implementation but cannot close TODO688 runtime execution.

## Scope exclusions and risks

Excluded: Stage 4 construction/deployment, native carrier execution, 8K
performance, presentation, and Phase 4 rendering. Residual risk: path policy
rejects the canonical seed location but cannot authenticate an arbitrarily
renamed executable; provenance admission remains an upstream gate.
