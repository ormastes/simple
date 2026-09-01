<!-- codex-design -->
# Native module cache invalidation architecture

## Decision

Use a versioned, complete per-module `NativeModuleCacheWitnessV1` as cache-hit
authority. Keep a stable cache root keyed by compiler, target, options, and
provider configuration so unaffected modules remain discoverable across closure
revisions. Missing or unverifiable evidence always selects compilation. The
closure-wide fingerprint remains comparison metadata, never hit authority.

## Capsule boundary

The native driver remains the owner of cache admission. For each physical
module it constructs one immutable witness from:

- canonical physical module ID and own MIR digest;
- sorted `(direct module ID, interface digest)` dependencies;
- ordered resolver probes, selected path, resolver version and directory generation;
- sorted referenced external type/layout digests;
- compiler executable/source, target, backend provider receipt and normalized options.

The witness encoder is domain-separated and length-prefixed. Set-valued fields
are sorted; resolver candidates remain ordered. The witness digest is separate
from the object-content digest and capsule receipt.
Resolver generation is derived from the canonical registry-name/physical-path
content rather than process freeze order, so identical closures are stable.

## Admission flow

`source closure -> semantic facts -> complete witness -> object gate`

The stable root discovers a candidate; it does not authorize reuse. An object
hit requires the parse-time source snapshot, readable current schema, exact
complete-witness digest, exact physical identity, valid capsule/object receipt,
and existing object bytes to agree. A legacy witness may be read only to explain
a bounded comparison receipt and cannot hit. Receipts record the authoritative
per-module decision and closure-wide comparison separately.

## Invalidation boundaries

- Body-only dependency edits do not propagate when its interface/layout facts
  are unchanged; the edited producer itself still misses on own MIR identity.
- Signature, referenced layout, selected/higher-precedence resolution candidate,
  provider, compiler, target, and normalized-option changes invalidate affected
  consumers.
- Unrelated sibling interfaces are absent from a module's direct witness and do
  not invalidate it.
- Corrupt, missing, ambiguous, or legacy evidence is a reasoned miss.

## Performance and observability

Witness construction consumes the already-built closure and semantic tables;
normal builds perform no full-tree scan and no per-module subprocess. One
bounded receipt records schema, compiler SHA-256, target/mode, manifest,
action/hit/miss/mismatch counts, reason histogram, wall time, and max RSS.
Receipts cap per-action details and include an overflow count.

## Ownership and MDSOC

This is a driver/cache virtual capsule, not a new compiler layer. Canonical
identity, authoritative comparison, and receipt emission are feature transforms at the
single native cache-admission boundary. HIR/MIR producers expose facts; they do
not make cache decisions. Backend providers supply an admitted receipt; they do
not authorize reuse.

## Authoritative bootstrap evidence update — 2026-08-29

The retained Phase1 full matrix for compiler SHA-256 `8999d4e35513...`
ended `FAIL` with 11 terminal rows. Compiler unit tests and MCP native build
each reached the 1,800-second bound; LSP native build failed after 1,408
seconds. Its frontend and HIR caches both reported 0 hits and 22 misses. The
phase verifier had assigned MCP and LSP different cache roots, so an earlier
tool build could not seed unchanged per-file entries for the next one. The
current verifier uses one `tool_builds` cache namespace while retaining
separate outputs. Witness validation remains fail-closed.

The retained LSP profile was dominated by surface construction: `std.log`
166.2s, `std.nogc_sync_mut.io_runtime` 148.2s,
`lib.nogc_sync_mut.sffi.system` 136.7s, `std.common.string_core` 121.2s,
`process_ops` 92.5s, and `file_ops` 77.2s. The LSP entry now uses a narrow
runtime boundary. Focused core-C initialize evidence moved from 45 unresolved
runtime symbols to zero and linked a 126 KiB binary.

Full MCP cannot use the same source-only split: its dispatcher directly calls
every advertised handler category, while existing "lazy" registries store only
metadata/flags. The required native late-binding ABI is recorded in
`doc/05_design/mcp_startup_entry_closure_split_blocker.md`.

Phase2 previously hit governance-forced MC/DC wrappers whose standalone SMF
cannot represent interpreter-only constructs. Commit `099b40b5795` added an
honest interpreter fallback with `mcdc_skip_reason`; it does not claim missing
MC/DC evidence. The retained Phase2 matrix still has 9 terminal rows, so Phase3
is pending fresh Phase2 admission and a new immutable candidate.
