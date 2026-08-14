# Cached Render Entry Closure System-Test Plan

Status: **implemented, self-hosted execution blocked** (TODO688).

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
