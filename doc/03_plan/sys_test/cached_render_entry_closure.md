# Cached Render Entry Closure System-Test Plan

Status: **static contract PASS; self-hosted execution blocked** (TODO688).

On the GitHub-synced source revision
`7ac900316dd5266595d8e2d713493ed174f0c8e4`, the nine-scenario structure,
requirement traceability, stub exclusion, numbered-artifact, direct-env, and
spec-layout checks passed once. The only available unadmitted `release/`
artifact then segfaulted with exit 139 before any scenario executed, with zero
stdout. That diagnostic is runtime-blocker evidence, not a failed expectation
and not an admitted SSpec PASS.

The executable modern SSpec is
`test/03_system/check/cached_render_entry_closure_contract_spec.spl`.

| Requirement | Coverage |
|---|---|
| REQ-RENDER-CLI-001 | Guide exposes `CachedRenderEntryClosureV1`, links plan/bug, and labels the workflow blocked/planned. |
| REQ-RENDER-CLI-002 | Bug/plan name pure-Simple owners and fail closed on no artifact, seed, or stale substitution. |
| REQ-RENDER-CLI-003 | Plan preserves exact sparse 8K correctness, performance, identity, and executor-only boundaries. |

Each requirement has a happy-path, boundary, and rejection-oriented scenario.
Run once after TODO682 supplies an admitted runtime:

```sh
<admitted-simple> test test/03_system/check/cached_render_entry_closure_contract_spec.spl --mode=interpreter
<admitted-simple> sspec-maintain scan test/03_system/check/cached_render_entry_closure_contract_spec.spl
<admitted-simple> spipe-docgen test/03_system/check/cached_render_entry_closure_contract_spec.spl --output doc/06_spec --no-index
```

Acceptance requires nine examples, zero failures, all seven maintenance scores,
zero stubs, and the mirrored manual at
`doc/06_spec/03_system/check/cached_render_entry_closure_contract_spec.md`.
Rust-seed or source-only results do not close TODO688.
