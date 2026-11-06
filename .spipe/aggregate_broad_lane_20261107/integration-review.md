# Broad aggregate source integration

Base: b065ff00f44e1d642057673cd1f37e6eaa1b3224. Order: PR7241 five commits, PR7344 one commit, PR7265 ten commits. PR7237 is subsumed by the exact stable-patch-id equivalents recorded in mapping.sdn. Only committed PR source was incorporated; prepared exported-statics work remains separate.

## Conflict decisions

Only textual conflict: FLAT_POOL_CODEC_VERSION. Both v14 layouts are incompatible with the aggregate. The new v15 identity combines declaration-index unsafe annotation metadata with parser original-source maps and structured diagnostics. The existing expectation and design reference now use v15; additional unexecuted assertions reject both v14 headers.

Automatic three-way merges preserved released unsafe_reason/unsafe_caps serialization and W2b HIR access-site fields, rather than replacing generated hir_codec wholesale. The released qualified-parser-state completeness audit remains unchanged relative to base. The released dotted numeric-directory closure normalization is retained alongside snapshot-provider routing.

## Evidence limits

Source integration only. No compiler, native build, or executable tests were run. All PR execution/admission limitations remain: node lifecycle cases unexecuted; source/MCP ownership gates and pure runtime qualification unavailable; merged seed compilation and behavior qualification unrun. Historical passes are not aggregate passes. No release admission claimed.

Normal Git hooks are retained without configuration overrides. Source-policy checks and exact preservation inspection are recorded separately; they do not qualify behavior. Root owns aggregate review, push, PR, merge, and closing superseded PRs.

## Static preparation checks

Working/staged direct-env guards: PASS. Whitespace: PASS. Full tracked doc/06_spec executable-spec count: 0 (sparse checkout does not limit this count).

- scripts/check/check-flat-ast-codec-complete.shs: 50 released added lines retained; missing=0
- src/compiler/20.hir/generated/hir_codec.spl: 111 released added lines retained; missing=0
- src/compiler/80.driver/driver_entry_closure_core.spl: 2 released added lines retained; missing=0

These are textual preservation checks, not execution evidence.
