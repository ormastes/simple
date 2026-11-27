# SCV structural byte storage v1

Status: implementation checkpoint; runtime validation **NOT_RUN**. This is the
first integrated slice of master-plan sections 15–17. No production-readiness,
real Tree-sitter execution, compression-ratio, throughput or memory measurement
is established by static review or fixture cursor tests.

## Contract and integration

`store.scv_write_file_object_from_bytes` retains the exact whole-file SHA-256
chunk and adds `structure:` to the immutable file record. Existing snapshot,
FileBuffer, manifest-import and fast-import callers use this entrypoint. New
writes omit legacy CDC maps. Old file records without `structure:` retain their
raw restore behavior; existing content IDs and historical objects are unchanged.
New file object IDs change because their reconstruction link is part of their
canonical payload.

`wasm_executor.scv_wasm_verified_blob` is the only provider admission path used by
the source writer. It checks the exact registry lock, bounds the artifact, checks
its actual SHA-256 and WASM magic, invokes the existing shim, verifies artifact
bytes again, and validates the returned tree against UTF-8 byte length. Missing
providers/artifacts, unsupported grammars, invalid UTF-8, empty/malformed blobs,
ERROR/MISSING nodes, ambiguous zero-width nodes and overlapping/escaping spans
produce a whole-file opaque representation with an encoded reason. Neither the
legacy simulator nor query-pack line declarations supply structural boundaries.

The six-field shim protocol omits `is_missing`/`has_error`. Nonempty-source
zero-width nodes are conservatively rejected. Full recovered-parse admission
needs a richer provider contract and real execution tests. Artifact pre/post
equality assumes trusted repository filesystem ownership; it does not eliminate
adversarial replacement races or authenticate a provider binary. The shim and
host libraries are existing external capabilities, not newly qualified here.

`structural_span_v1` validates one preorder host tree. `structural_store_v1`
keeps complete syntax nodes and synthesizes exact intervening/leading/trailing
gap nodes. Repeated children remain repeated references. Injected trees must
remain overlays: overlapping sibling ownership or a second root is rejected.
Indivisible literals remain whole, including those larger than former CDC
limits. Invalid bytes are never decoded during reconstruction.

## Representation and identity

Byte nodes are fixed-order SDN records with a format tag, role, hex-encoded
kind/field metadata, exact length, secure payload reference, and ordered child
references. Their IDs use the existing `syntax_node_<SHA-256(record)>` namespace.
This deliberately uses the existing approved secure algorithm and does not
mislabel it BLAKE3. Node identities exclude file paths and absolute offsets.

The root envelope binds raw content identity, length, structural profile,
execution label, parser pin, language, grammar, version, fallback reason and
child root. Its ID is separate from raw content identity. Existing-hit writes
compare canonical record/payload bytes, beyond checking a secure digest.
Physical codec compression and structural deltas are absent; delta depth is
zero. The additive v1 archive packs complete canonical byte-DAG records in
identity framing under a content-addressed archive and sealed index. It never
cuts source at parser spans. Parser records whose IDs hash semantic inputs stay
loose and retain their prior identity contract. The archive is bounded to 64
MiB, records to 8 MiB, and the index to 16 MiB; reads verify the selected pack
and index in full (O(pack bytes)). A real compression provider is reported
optional and inactive until qualified. Loose records and raw chunks remain
retained. Raw reclamation is disabled by retention, not inferred from
deduplication.

## Restoration, retention and bounds

The parser-free decoder uses an explicit bounded frame stack, one output buffer
and one current payload. Closing frames verify each branch's exact aggregate
length. Every record and payload is rehashed; references, canonical decimal
lengths and metadata encodings are checked before following them. Limits are
256 MiB output, 8 MiB per metadata record, depth 514, 200,000 visited/pending
frames, and 65,536 input parser nodes. Provider source input remains limited to
16 MiB. These are admission bounds, not measured peak-RSS guarantees.

Normal commit restore checks the immutable file record and reconstruction before
removing tracked destinations, then revalidates immediately before publication.
Reconstructed bytes must equal the retained raw bytes and their secure identity.
A missing/corrupt linked structure is an error rather than a silent raw fallback.
This preserves the shadow-comparison gate before structural data can become the
only representation. Legacy raw-only records remain supported.

GC follows file `structure:`, ordered node `children:` and leaf `payload:` edges
through the same bounded record resolver. Checked destructive GC paths stop on a
missing or corrupt indexed archive before pruning or quarantine. File/tree
integrity validation invokes independent reconstruction. Existing pack and
deterministic syntax-object hash rules continue to accept these ASCII SDN
records. Backup/crash/GC execution gates remain pending.

## Validation and remaining work

Unit SSpec: `test/01_unit/lib/scv/structural_storage_v1_spec.spl`.
System BDD: `test/03_system/app/scv/feature/scv_structural_storage_v1_spec.spl`.
Fixture trees explicitly assert no provider execution. Cases cover exact binary
bytes, BOM/CRLF/comments, gaps, subtree reuse, giant literals, malformed spans,
injection overlap, tampering, malformed correctly-hashed records, bounds,
retention, empty/legacy records, public restore and destination preservation.

Neither checkout provided `bin/simple` or `bin/release`; no Rust seed was used
as feature-test evidence. SSpec execution, SPipe docgen/maintain, required core,
MCP/LSP and native smoke gates are **NOT_RUN**, not PASS. Coverage is unmeasured.

Loose publication still performs per-node/per-payload atomic writes. Batching
the complete record files into the optional archive does not remove loose
publication or raw retention. Actual codec packing, scheduler budgets, parser
session reuse, provider ABI/provenance qualification, benchmarked coexistence
accounting, crash/backup tests and raw reclamation gates remain explicit
follow-up work.
