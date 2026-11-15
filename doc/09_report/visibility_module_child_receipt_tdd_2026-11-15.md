# Configured module-child receipt implementation checkpoint

Base: `cedc6b8b56a0f30529c1f97c80e3e6a5c6a6e3cc`.
Isolated branch: `work/visibility-route-tdd-20261115`.

## Implemented source slice

`ModuleChildSelectionReceiptV1` preserves the configured namespace and selected
name, selected parent surface/manifest identity, exact child ordinal/name/modifier,
semantic frozen-policy digest, snapshot, selected target path/SHA/kind, registry
allocation generation and stable configured-route generation.

The freeze owner first attempts an exact configured namespace-child branch. It
selects the parent through the configured registry name, then the explicit named
policy child, then verifies that child's snapshot-bound target. That branch
supplies the selected target and trace; it does not attach a receipt after a
legacy resolver happens to reach the same path. Parent and target source SHA are
retained from actual SourceFile content. Parent/target snapshot identities must
agree. Same-file package redirection retains its existing legacy branch.

Frozen import rows retain receipts and promotion roots retain all new carriers
and text. Surface semantic digests include semantic receipt data, excluding the
process-local allocation epoch. HIR source import writes capture provenance only
when the actual binding changes. No-op registration cannot replace an existing
route; binding identity includes scope, spelling, symbol and mutation version.
Module reset clears retained maps; generation, policy, snapshot and source checks
reject stale lookups.

## TDD and evidence

The executable regressions were authored before the receipt DTO and production
implementation. **RED/GREEN execution is BLOCKED, not demonstrated.** No general
admitted pure-Simple SSpec/check runner exists at `bin/release/*/simple` in the
active environment. The supplied pinned P2 supports native-build only, not
check/test/run. Its SHA is
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
A production HIR fixture requires the full parser/registry/lowering dependency
closure, outside this bounded no-full-build lane. No unsupported command, Rust
seed fallback, native build, SPipe/docgen or runtime test was attempted.

Local checks: `git diff --check` passed for the initial implementation;
`sh scripts/audit/direct-env-runtime-guard.shs --working` passed; executable
`*_spec.spl` count under `doc/06_spec` is zero. Final staged direct-env guard and `git diff --cached --check` also passed. These are source hygiene checks, not compiler/runtime acceptance.

## Explicit remaining limitations

Only exact configured namespace-child imports with retained parent policy qualify
for a receipt. Relative, lexical, legacy flat, policy-only-parent and TLDR-only
routes lacking these producer fields remain unavailable. A receipt covers one
selected child; it never asserts complete ancestor traversal or a positive access
grant. Named export predecessor chains remain a separate owner. Full expression,
qualified type and alias requester enforcement is not implemented by this slice.
No existing imports are denied merely for lacking a receipt.

The source-use map is module-local and bounded by actual source binding writes.
Its linear lookup and policy revalidation are not wired into general expression
hot paths; a future full requester consumer needs indexed lookup/cache design
and warm latency/RSS evidence. Freeze selection reads retained registry/policy
arrays only, without filesystem rescans. Performance, transient-lifetime,
compiler/core, MCP/LSP and full positive permission integration remain UNQUALIFIED.
