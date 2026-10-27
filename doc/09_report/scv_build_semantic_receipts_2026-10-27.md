# SCV BuildRunner semantic receipt lane — 2026-10-27

STATUS: BLOCKED — production semantic acceptance is not implemented.
Execution: NOT_RUN. No admitted general runtime was supplied. No Rust-seed,
bootstrap compiler, source runner, or fabricated red/green evidence was used.

## Delivered boundaries

`compiler.driver.cache.gateway.scv_build_snapshot_relation_v1` compares actual
canonical compiler source rows and decoded blobs with the full frozen build
snapshot, and compares configuration, target, compiler, runtime, path-policy,
and separately observed environment identities. It checks canonical CAS source
identity rather than confusing raw-content and source-envelope digests. Extra,
missing, duplicate, foreign-namespace and byte-changed sources fail comparison.
ASCII paths are the only supported diagnostic correspondence: capture exact
UTF8 paths do not prove the compiler's NFC normalization policy for Unicode.

The returned value is explicitly diagnostic and always retains missing actual
namespace, path-policy, resolver/candidate/directory, generated-input,
provider/toolchain and live-readset authority. It does not translate SCV snapshot
IDs into compiler identities and cannot grant artifact reuse.

`scv_build_validation_receipt_v1` encodes strict bounded canonical SDN records,
binding the requested full build snapshot, action, exact semantic read manifest,
semantic generation, configuration, target, compiler, runtime, environment and
provider-version lock. A copied or stale ID, modified body, unsupported coverage,
unknown fields, duplicate/reordered fields or truncated record is refused.
Sealing authenticates contents only. Public struct construction grants nothing.

`scv_build_validation_receipt_archive_v1` provides immutable content archival
and retrieval against an exact parent-supplied accepted ID and expected subject.
It creates exclusive staging files, fsyncs data, publishes without replacement,
then fsyncs the destination and directory before returning. Root-wide OS locking
serializes publishers; children receive copied immutable inputs and return a
bounded result. No global temporary-directory argument slots are used inside
concurrent publication. Corrupt existing receipts are refused, not repaired.
A stale staging file after a crash requires explicit owner recovery. Root
ancestors must be real directories. The parent must keep that root private and
stable during operations; these path APIs do not provide an anchored-directory
capability against hostile concurrent ancestor replacement.

Archival is not accepted-root publication. Only the parent's actual authenticated
semantic validator may publish an accepted root after receipt archival succeeds.
This lane deliberately creates no fake complete semantic receipt or accepted root.

## Actual missing production owner entrypoints

1. `compiler.semantics.semantic_scope_issuers_v2`:
   `SemanticScopeIssuerReceiptV2.validate_issued_scope_v2` currently returns
   `coverage: Unknown`, `universe_complete: false`, and
   `gateway_install_available: false`. Those are truthful diagnostic projections.
2. `compiler.driver.cache.gateway.semantic_scope_live_owner_v2`:
   `install_semantic_issuer_v2` feeds that projection to `_issuer_candidate_v2`,
   whose completeness requirements reject it. Consequently five actual issuers
   cannot reach `seal_scope_v2` and no complete live grant is issuable.
3. The same owner has no production issuance route for
   `VerifiedThreePayloadWorkerResultV2`.
   `execute_three_payload_compile_v3` explicitly returns `AuthorityUnavailable`;
   parse preflight alone cannot substitute for complete semantic execution.
4. `declaration_semantic_issuer_install_boundary_v1` remains explicitly closed;
   its owner factory returns `AuthorityUnavailable`.
5. `scv_semantic_validation_adapter_v1` therefore correctly retains
   `semantic-nonsource-authority-relation-unavailable`. No existing adapter or
   fixture authority was weakened by this lane.

Completing these real producer capabilities, obtaining an actual complete
multiowner current `SemanticQueryReadManifestV1`, and linking compiler
namespace/resolution/generated/provider authority to capture ownership are
required before semantic acceptance. Changing copied DTO labels to complete,
inventing expected-authority projections, or creating a dummy provider would
not resolve these blockers.

## Tests-first history and validation

- `2ce1bbe18f2`: diagnostic relation and receipt identity negative controls.
- `32f0d3e5ef8`: durable, corrupt/replay/stale and simultaneous-publication specs.
- Runtime execution and generated SPipe manuals: NOT_RUN, admission required.
- No red/green, branch coverage, native feature acceptance, or full compiler/
  core/MCP smoke PASS is claimed.

The new source modules each remain below 800 lines. Required static audits and
whitespace checks are recorded in the implementation handoff; they do not
substitute for missing native runtime evidence.
