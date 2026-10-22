# B2 interval and ast-link boundary

REQ-MC-008 additive extension of SOURCE_API_GO parsed-source packet. Status CODED / UNRUN; full B2 remains partial because the admitted producer only exports explicit primitive top-level functions. No type/name-analysis or all-kind completeness claim.

`semantic_link_from_line_v1(document, revision, first_line, last_line, package_qualified)` returns a URI only for a unique copied parsed span enclosing the entire non-whitespace byte range. Start-line matches outrank other containing spans; smallest width wins within rank. Equal best candidates refuse with AmbiguousTarget. An enclosing function supplies the available owner for unnamed body expressions. Blank, reversed, zero and past-EOF ranges refuse. No raw-outline declaration authority.

`resolve_semantic_links_source_v1(uris, document, revision)` preserves order, caps inputs at 4096, validates exact disk revision before and after indexed lookup, and publishes no partial result. Existing single-URI lookup delegates to the batch. Empty batches still validate revision. Documents are caller-owned bounded snapshots; replacing/discarding the snapshot explicitly invalidates it. No shared cache, tree walks, or arena handles. Source producer remains serial because the core parser uses global arenas. Each document is limited to 1 MiB / 4096 declarations; interval selection scans that bounded declaration array and source once. Batch lookup uses existing name/fingerprint indexes. Runtime latency/RSS targets are UNRUN.

Command handler `app.cli.ast_link.ast_link_command_v1(args)`:

```
ast-link from-line FILE#Lx[-Ly] --package P --module M --revision SHA256
ast-link resolve URI --file FILE --package P --module M --revision SHA256
```

Handler args exclude `ast-link`. From-line returns the strict B1 short URI; resolve returns `FILE:line:column`. Duplicate/unknown options refuse. Package/module/file/revision are explicit configured authority; no guessed package or latest revision. CLI dispatcher registration belongs to root integration; handler performs no output or process/env calls. Stable SymbolComponents schema and fingerprints are unchanged.

Tests authored before leaves: `test/03_system/app/ast_link/feature/semantic_from_line_spec.spl`. Covers start/body, cross-declaration range, EOF/stale source, tied spans, ordered batch/stale fingerprint, both command operations and invalid line zero. Original 23-scenario packet retained unchanged. Runtime, docgen, sspec-maintain, coverage, core/MCP smokes and performance UNRUN under parent phase-qualification constraint. Source-only whitespace check PASS once; no build/retry/commit/push.


## Revision2 source authentication

Public snapshot declarations/indexes/spans are externally mutable. Disk SHA256 alone never authenticates those fields. Both resolve batch and from-lines batch now call the actual parsed-source producer exactly once using explicit file/package/module/revision inputs and exclusively consume its fresh local facts. Single wrappers delegate. No identity or location is accepted from caller arrays. Producer calls remain serial under existing parser-global constraints.

Charged cost: resolve batch at most three bounded1MiB source reads (producer before/after, final validation); from-lines batch at most four (producer before/after, source bytes for line index, final validation). Exactly one parse per batch, none per individual URI/range. 4096 entries/declarations cap retained. This intentionally replaces cache-only lookup pending genuine opaque/private snapshot authority. Latency/RSS are UNRUN; no performance PASS.

Source forgery scenarios restore actual real-URI span and reject invented identity/index facts; duplicate caller intervals no longer create semantic ambiguity because they are discarded. All runtime UNRUN.
