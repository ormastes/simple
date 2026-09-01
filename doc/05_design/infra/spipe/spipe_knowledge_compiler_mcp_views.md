<!-- codex-design -->
# SPipe Knowledge Compiler: MCP and Virtual Views Detail Design

**Date:** 2026-08-25  
**Status:** Implementation detail design  
**Scope owner:** MCP transport, virtual URI projection, and materialized read-only views

This document refines AC-5, AC-6, AC-13, AC-14, and AC-15 from
`.spipe/spipe_knowledge_compiler/state.md`. It implements the decisions in
`doc/01_research/infra/spipe/spipe_knowledge_compiler.md`; it does not redefine
artifact identity, graph ownership, search ranking, or refactor architecture.

## 1. Current Compatibility Baseline

The authoritative SPipe package surface currently mirrored in Simple is
`examples/05_stdlib/spipe/`:

- `cli/spipe.js` is a 1,917-line dependency-free Node dispatcher.
- `mcp/server.js` is a 187-line dependency-free newline-delimited JSON-RPC
  stdio server.
- `package.json` publishes `spipe` and `spipe-mcp` at version `0.1.0`.
- `plugin/manifest.sdn` and `plugin/.codex-plugin/plugin.json` name
  `mcp/server.js` as the MCP entry point.
- `scripts/build.shs` contains the existing package, link, CLI, and two MCP
  smoke checks.
- `mcp/README.md`, `cli/README.md`, and `README.md` document the public surface.

The server advertises protocol `2024-11-05`, six tools, and one resource:
`spipe://skill`. It has no resource templates, cursor pagination, subscriptions,
HTTP transport, workspace selection, cache metadata, or structured virtual
view API. Existing names and successful response shapes remain compatibility
contracts during extraction.

Simple tracks `.spipe/spipe` as a gitlink at the reviewed SPipe revision while
also tracking the mirror under `examples/05_stdlib/spipe`. Implementations must
change the upstream SPipe package first and update a host mirror or gitlink only
through the repository's established synchronization workflow.

## 2. Boundary and Module Layout

Keep both executable paths as thin compatibility entry points:

```text
cli/spipe.js                         command parsing and compatibility output
mcp/server.js                        stdio entry and dependency assembly
mcp/transport/stdio.js               framing, lifecycle, cancellation
mcp/transport/http_2026.js           optional target stateless transport
mcp/protocol/router.js               JSON-RPC dispatch and errors
mcp/protocol/initialize.js           version/capability negotiation
mcp/protocol/resources.js            list/templates/read/subscription facade
mcp/protocol/tools.js                model-callable tool facade
mcp/protocol/cache.js                visibility-safe cache hints
src/workspace/registry.js            explicit workspace resolution
src/view/uri.js                      URI parsing and canonicalization
src/view/projection.js               snapshot-to-view projection
src/view/directory_index.js          bounded generated Markdown indexes
src/view/materialize.js              safe `.spipe/view` synchronization
src/storage/materializer_safe_filesystem_port.js  materializer mutation port
src/storage/native_materializer_safe_filesystem.js native port provider
src/storage/trusted_fs_helper.js     admitted helper protocol adapter
```

Protocol and CLI adapters depend on immutable knowledge snapshots through these
ports; they do not parse or scan repositories directly:

```text
WorkspaceRegistry.open(workspace_id) -> KnowledgeSnapshot
ResourceResolver.resolve(snapshot, uri) -> ResourceTarget
ProjectionPortV1.render(authorityView, canonicalTarget, verifiedReadGrant)
  -> Result<ProjectionDocumentV1, ProjectionError>
ProjectionPortV1.list(authorityView, directoryTarget, verifiedReadGrant, verifiedCursorGrantOrNull)
  -> Result<ProjectionPageV1, ProjectionError>
Materializer.sync(snapshot, view, output_root) -> MaterializeReceipt
```

`ProjectionPort` is the only internal projection boundary name.
`ProjectionProvider` is the only external/runtime implementation name and is
adapted once to `ProjectionPort`; no alternate projection boundary name appears
in schema, code, wire contracts, or tests.

Every request receives one immutable snapshot. A request must not trigger a
full-tree scan, reread all artifacts, or spawn a search provider. Index and
watch maintenance publish a new snapshot outside request handling.

## 3. Workspace Resolution

Workspace identity is explicit and stable. Resolution precedence applies only
before a request has selected a URI family or presented an admission receipt:

1. tool/resource workspace identifier;
2. server configuration supplied at launch;
3. `SPIPE_HOST_ROOT` compatibility environment value;
4. one configured default workspace.

There is no per-request current-working-directory inference. Once a URI names a
workspace, or a receipt/cursor binds one, the resolver uses that exact
workspace; it never falls through to server configuration, environment, or a
default workspace. Workspace-less project and legacy aliases are first resolved
by the registry to one canonical workspace; a legacy alias then yields only a
candidate that must pass sealed target proof before reauthorization in that
exact workspace. Ambiguity is a closed admission failure. Startup resolves
and realpaths the module root, host root, canonical content roots, cache root,
and materialization root. The registry binds workspace ID to project IDs,
revision, worktree ID, visibility policy, and current snapshot ID.

## 4. Canonical URI Contract

The authoritative URI families are:

```text
spipe://workspace/{workspace}/
spipe://workspace/{workspace}/view/{view}/{segments...}
spipe://workspace/{workspace}/trace/{artifact_uid}
spipe://workspace/{workspace}/diagnostics
spipe://project/{project}/artifact/{artifact_uid}
spipe://project/{project}/section/{section_uid}
```

The workspace-root resource has exactly the trailing-slash form shown above;
`spipe://workspace/{workspace}` is not a synonym and is rejected as malformed.
No URI family permits an implicit selector remap: a request selects the named
workspace, project, base/authority snapshot pair and revision, view, and scope, and all later checks
must bind those exact values. In particular, a legacy alias, cursor, or receipt
for one workspace may not resolve a same-named project or view in a foreign
workspace.

`view` is one of `lifecycle`, `feature`, `component`, `layer`, `matrix`,
`trace`, `project`, `status`, or `diagnostics`. The legacy `spipe://skill`
resource remains an alias to its canonical artifact for all supported legacy
clients.

URI parsing performs exactly one percent decode and then rejects any remaining
encoded percent that could become a separator, dot segment, NUL, colon, or
backslash after a second decode. It rejects malformed escapes, NUL, forward or
backslash traversal, `.`/`..`, encoded separators, empty identity segments,
fragments where unsupported, duplicate/ambiguous query parameters, and control
characters. A path segment cannot use a Windows drive prefix, UNC or device
namespace (`\\server`, `\\?\\`, `\\.\\`), alternate-data-stream colon,
or a trailing dot/space. These checks apply on every host OS so a snapshot
created on Unix cannot become unsafe when consumed on Windows.

Input is validated as well-formed UTF-8 and normalized to NFC for comparison.
The original spelling remains display metadata; two spellings with the same
normalized form are an ambiguity diagnostic rather than aliases. URI identity
never derives from locale-sensitive or case-folded display text. Resolution
authorizes the explicit project and revision before reading content. Physical
targets are resolved from pinned root directory handles, not from a later
string-based realpath check. Allowlisted textual prefixes are insufficient
because a symlink or junction can escape them or be swapped after validation.

## 5. Projection Semantics

Virtual paths are navigation handles. Every artifact/section virtual document
resolves to one canonical artifact or section UID. Aggregate outputs such as a
directory index, search result page, trace projection, and diagnostic report
instead receive `ProjectionUid`, rendered exactly as
`spkp1-<lowercase-sha256>`, where `<lowercase-sha256>` is SHA-256 over canonical
SDN `projection_v1(workspace_uid, snapshot_id, view_kind,
normalized_logical_path, normalized_parameters_hash,
effective_auth_scope_hash, page_start_key)`. There is no alternate aggregate
identity formula. For an entirely public projection, `effective_auth_scope_hash`
is a stable public-policy/version digest shared across principals. For a private
or mixed projection, it covers principal, tenant, effective grants/denials, and
authorization-policy version. An aggregate must never claim an artifact UID or
receive canonical-file mutation operations. The binding prevents private reuse
across a different principal, policy, snapshot, query, or page while preserving
principal-independent identity and shared caching for genuinely public output.
Directory membership may reference the same canonical UID from many views
without copying ownership.

Children are ordered deterministically by normalized display key, artifact
kind, then immutable UID. A unique slug is emitted without a suffix. A collision
uses `<slug>--<short-uid>`. The directory manifest always records the complete
virtual-path-to-UID mapping, including unsuffixed paths.

Directory reads return generated Markdown with counts, relevant artifacts,
lifecycle grouping, and trace gaps. Limits are:

- no more than 100 direct entries per response;
- no more than 200 Markdown lines or 6,000 `spipe-markdown-token-v1@1` tokens;
- cursor pagination before either bound would be exceeded.

A cursor is an opaque, versioned `CursorReceiptV1`, signed by the same admitted
receipt authority as reads. Its canonical signed payload binds **authority
key/epoch**, workspace UID, project UID or null, snapshot ID, revision ID, view
kind, normalized logical path, normalized filters, effective authorization
scope digest, ordering version, last sort key, and the issued page limit. The
next request independently resolves and authorizes the URI, then compares every
binding before consulting the cursor position. A valid receipt with a different
authority, workspace, snapshot, view, scope, selector, or limit is
internally classified `stale_cursor` and externally mapped to the bounded
`not_found_or_unauthorized` class; it never silently skips, duplicates,
remaps, or discloses results. Cursor verification never substitutes a current
default workspace or current snapshot.

`AuthorizationPort` is a branded, real signed-verifier boundary, not a
structural JavaScript object or duck-typed callback. `createAuthorizationPort`
returns an unforgeable branded instance after it loads an issuer/algorithm/key
allowlist and verified key epoch. `verifyCanonicalReadReceiptV1(receipt,
expectedBinding, clockNowMs)` verifies the brand, protocol version, canonical
payload bytes, signature, issuer/key/epoch allowlist, revocation epoch,
`issuedAtMs <= clockNowMs < expiresAtMs`, and exact `ExpectedReadBindingV1`,
including `authorityInstanceUid` and `authorityManifestDigest`. It returns only
an opaque verified-read grant; parser, projection, and cursor modules
cannot construct a grant or accept `{ verify() {} }` substitutes.

The required same-port extension is `issueCursorReceiptV1(readGrant,
{pagePosition, requestedExpiresAtMs}, clockNowMs)`,
`verifyCursorReceiptV1(receipt, readGrant, clockNowMs)`,
`rotateCursorReceiptKeyV1(request, clockNowMs)`, and
`applyDueCursorReceiptKeyTransitionsV1(clockNowMs)`. It is not currently
admitted merely because canonical-read verification exists. The read grant is
opaque and carries the sealed `ExpectedReadBindingV1`'s trusted
`baseSnapshotUid`, `authoritySnapshotUid`, `worktreeUid`, `authorityInstanceUid`,
and `authorityManifestDigest`; cursor issuance derives
all other binding fields from it, not from an adapter request.

MIME types are `inode/directory` for directory resources, `text/markdown` for
rendered documents, and `application/vnd.spipe.sdn` for structured graph data.

## 6. MCP Resource and Tool Contract

Resources implement deterministic `resources/list`,
`resources/templates/list`, and `resources/read`. List-change notifications and
subscriptions are advertised only after their invalidation implementation is
available. Templates cover project artifact/section and workspace view/trace
families.

Equivalent model-callable tools are mandatory because hosts surface resources
inconsistently:

| Tool | Input essentials | Output essentials |
|---|---|---|
| `spipe_list` | URI, cursor, limit | entries, next cursor, snapshot |
| `spipe_read` | URI, optional range | MIME, content, UID, snapshot |
| `spipe_search` | query and filters | explained ranked results |
| `spipe_resolve` | UID/key/path/alias | canonical UID and locations |
| `spipe_trace` | UID, direction, depth | bounded typed subgraph |
| `spipe_diagnostics` | scope and codes | bounded diagnostics |

The existing six tools and `spipe://skill` remain callable. New structured
results include a human-readable text representation for legacy hosts.

JSON-RPC failures preserve the request ID and distinguish protocol-envelope
errors (parse error, invalid request, method not found, invalid parameters,
resource limit, and internal error). Every **read-admission** denial is instead
the privacy-safe `not_found_or_unauthorized` class defined below. Notifications
never receive a response. Partial stdio chunks and multiple messages per chunk
are supported.
Initialize negotiates a mutually supported version, processes `initialized`,
and rejects requests that require initialization before lifecycle completion.

All public read-family admission failures (`malformed_uri`, unknown workspace,
foreign selector, receipt/signature failure, expired/revoked receipt, stale
cursor, unauthorized, and hidden/not-found) map to one privacy-safe external
`not_found_or_unauthorized` response class with the same bounded-work path.
Server telemetry retains a closed internal reason code. This rule applies to
both resources and tools and prevents an oracle for workspace/project/view
existence.

The protocol-neutral core supports legacy stdio and the target stateless MCP
2026 transport. Transport-specific sessions, headers, or authorization never
enter snapshot and projection services.

HTTP authorization validates a signed token against configured issuer,
audience, algorithm allowlist, key ID, and active key epoch. Signature keys are
refreshed out of band and a request never fetches keys on its hot path. `exp`
and `nbf` allow at most 60 seconds of configured clock skew; expired, premature,
unknown-key, wrong-issuer, and wrong-audience tokens fail closed. The preferred
client contract is an `Authorization: Bearer` token and rejects credentials in
query strings. If an adapter enables cookies, it additionally requires
`Secure`, `HttpOnly`, `SameSite=Strict`, an origin allowlist, and a bound CSRF
token on every state-changing request; cookie auth is disabled by default.

An unauthorized caller receives the same external status, response class, and
bounded-work path for an absent resource and an existing hidden resource. The
server performs one token verification, one constant-count registry lookup,
and one visibility decision before returning the generic result; it does not
render content, traverse a graph, or vary error detail. Timing is padded only
to a configured maximum small bucket, never with unbounded sleep. Detailed
reason codes are restricted to privacy-safe server telemetry.

### 6.1 Request resource limits

Defaults are configurable downward but cannot be disabled in production:

- stdio/HTTP JSON-RPC frame: 1 MiB; HTTP headers: 32 KiB; nesting depth: 64;
- method name: 128 bytes; URI: 8 KiB; query text: 4 KiB; filter values: 256;
- decoded JSON string: 256 KiB and aggregate arguments: 512 KiB;
- list limit: 100; search candidates: 1,000; trace depth: 8 and nodes: 2,000;
- read response: 1 MiB; generated Markdown: 200 lines/<=6,000 `spipe-markdown-token-v1@1` tokens;
- at most 16 in-flight requests per connection and a configured global/tenant
  budget; excess work returns a retryable resource-limit error;
- parser CPU deadline and request wall deadline are explicit, cancellation is
  propagated, and partial oversized frames are discarded without allocation
  proportional to the advertised size.

Unknown query keys and duplicate scalar parameters are invalid rather than
ignored. Pagination, range, graph, and search integers use bounded decimal
parsing with overflow rejection. Logs truncate and classify hostile inputs
without reproducing bearer tokens, cookies, or full private queries.

## 7. Cache and Invalidation Contract

Cache identity contains workspace, project, revision, worktree, snapshot,
schema, parser, projection version, effective authorization-scope digest, and
authorization-policy version. Read/list results are immutable for a snapshot.
Public/shared cache scope is legal only when every referenced node is public;
its public scope digest remains stable across principals. A private or mixed
result includes principal/tenant and effective policy in its digest, is
session/private scoped, and is never cached publicly.

HTTP public immutable snapshot resources return a strong content-derived ETag,
`Cache-Control: public, max-age=<bounded>, immutable`, and no `Set-Cookie`.
Authorization-sensitive or mixed/private results return
`Cache-Control: private, no-store`, omit shared-cache validators, and include
`Vary: Authorization, Cookie` when those inputs are accepted. Generic
not-found/unauthorized responses are `private, no-store`. Conditional requests
perform authorization before evaluating `If-None-Match`; a `304` must never
confirm a hidden resource. Mutable directory aliases use a snapshot-specific
ETag and bounded `max-age`/revalidation rather than `immutable`. Cache keys
include representation MIME, negotiated protocol version, content encoding,
and visibility class; `Vary` includes each request header that selects one of
those representations.

An index delta publishes a new snapshot and invalidates affected directory
indexes through reverse membership. Unaffected snapshot resources remain
cacheable. Observability records startup snapshot-load time, list/read/search
latency, cache hit/miss, entries returned, truncation, stale cursors, and maximum
RSS without logging private content.

## 8. Materialized View Contract

File-only agents browse `.spipe/view/<view>/`. Generated documents begin with:

```markdown
<!-- generated by SPipe; do not edit -->
<!-- canonical-uid: A-... -->
<!-- canonical-path: doc/... -->
<!-- snapshot: ... -->
```

That header is valid only for a single canonical artifact. Aggregate directory,
trace, search, and diagnostic documents instead contain
`<!-- projection-uid: spkp1-<lowercase-sha256> -->` plus snapshot and effective
authorization-scope digest; they omit `canonical-uid` and `canonical-path`.

`MaterializerSafeFilesystemPort` is the sole internal boundary for
**materialization** filesystem mutation. Only `AuthorizationPort` issues the
non-copyable capability `SafeFilesystem.Materializer`, and only the
`ProjectionService` materializer adapter may hold it. Filesystem providers and
helpers supply port operations invoked by that authorized holder; they never
receive, issue, grant, supply, or hold the capability. The exact API is:

```text
open_view_root(grant: MaterializerRootGrant) -> SafeViewRoot
stage_generated(root, projection_uid, relative_path, bytes) -> StagedGeneratedFile
create_generated_directory(root, relative_path) -> CreatedDirectory
atomic_replace_generated(root, StagedGeneratedFile, destination) -> AppliedMutation
remove_generated(root, relative_path, expected_projection_uid) -> AppliedMutation
sync_generated_file(root, relative_path) -> DurabilityReceipt
sync_generated_directory(root, relative_path) -> DurabilityReceipt
```

Inside the authorized `ProjectionService` materializer adapter,
`SafeFilesystem.Materializer` is consumed to create one non-authorizing
`MaterializerRootGrant`. The grant contains only opaque view-root identity,
normalized generated-path prefix/set, allowed materialization operation set,
projection/snapshot binding, byte/count budget, and expiry. It contains no
principal, tenant, policy, bearer token, credential, capability, or reusable
authorization authority. `open_view_root` and external helper messages receive
only this sanitized grant. A provider validates operation arguments against the
grant's bounds but cannot widen them or use the grant to authorize another
workspace, root, projection, or operation.

There are no raw-write, absolute-path, recursive-delete, or symlink-following
operations. The port cannot mutate canonical artifacts, aliases, journals, or
refactor targets. The `NativeMaterializerSafeFilesystem` provider implements
this port and pins directory handles for the authorized
worktree root and `.spipe/view` root after rejecting symlink/reparse-point roots.
Every create, inspect, replace, rename, and cleanup is descriptor-relative to
those handles (`openat`/`renameat`/`unlinkat` semantics on Unix and equivalent
handle-relative, reparse-point-resistant operations on Windows). Each component
is opened without following links and its file identity is checked before use.

Dependency-free `PortableNodeFilesystemVerifier` may use bounded
`lstat`/open/`stat` checks for read-only inventory and diagnostics only. It is
not a `MaterializerSafeFilesystemPort` provider, cannot create, replace,
publish, remove, or clean generated paths, and no check/open/recheck loop is
accepted as a mutation security boundary.

When native descriptor-relative operations are unavailable, mutation may use a
separately admitted trusted helper. `TrustedFilesystemHelper` is configured by
an absolute executable path plus pinned executable SHA-256 digest and exact
protocol version. Startup verifies ownership/permissions, digest, protocol,
the exact `MaterializerSafeFilesystemPort` operation set above,
descriptor-relative/no-follow guarantees, and a fresh
challenge response before admitting the helper as an operation provider.
Requests use bounded length-prefixed canonical messages containing the sanitized
`MaterializerRootGrant`, OS-equivalent opaque root identity, request nonce,
operation, relative components, expected file identities/hashes, and deadline.
They never contain the source capability or authorization metadata. Responses
bind nonce, protocol, helper build digest, result identities, and
durable-operation receipt. Digest/protocol drift, unexpected output, timeout,
restart, ambiguous identity, or missing guarantee revokes the helper's
operation-provider admission and fails closed. The helper never accepts an
arbitrary absolute mutation path and never receives the authorization
capability.

The `ProjectionService` materializer adapter opens the view root, creates
generated directories, stages each projection-bound file, publishes it with
`atomic_replace_generated`, and records durability through
`sync_generated_file` and `sync_generated_directory`. The manifest is staged
and replaced last as the commit marker. Content hashes prevent rewriting
unchanged files, preserving their modification times.
Operation-provider probing occurs once at startup. Materialization is enabled
only when `AuthorizationPort` has issued `SafeFilesystem.Materializer` to the
`ProjectionService` materializer adapter and an admitted native or trusted-helper
provider supplies the port operations. Otherwise materialization is unavailable
and fails closed while MCP read-only views remain usable.

Transactional refactoring is outside this module and uses the separate internal
`RefactorSafeFilesystemPort` plus capability `SafeFilesystem.Refactor`.
Admission to `MaterializerSafeFilesystemPort` or possession of
`SafeFilesystem.Materializer` does not authorize, implement, or imply support
for refactor operations.

Output roots must resolve below the selected worktree's `.spipe/view`; output
symlinks, junctions, mount/reparse transitions, and changed file identities fail
closed. Each worktree has an independent view root, lock, staging area, and dirty
overlay. Cleanup walks only by descriptor relative to the pinned view root and
removes only paths listed in the previous manifest whose marker, prior generated
hash, type, and file identity still match. It refuses symlink/reparse entries at
every depth. A user-modified, replaced, hard-linked, or unknown file is diagnosed
and preserved.

Read-only permissions are advisory. Correctness comes from generated ownership,
manifest validation, and refusing writes through MCP/editor adapters. Canonical
changes use the separately owned transactional refactor service.

## 9. Compatibility and Migration Sequence

1. Capture byte-level successful outputs for existing CLI commands and MCP
   tools/resources.
2. Extract protocol routing and services without changing public behavior.
3. Add explicit workspace configuration and immutable snapshots.
4. Add URI resolver, resource templates, and read-only list/read tools.
5. Add feature/component views, then remaining projections.
6. Add safe materialization.
7. Add the target stateless transport while retaining stdio.
8. Advertise notifications, subscriptions, and cache hints only when verified.

Package binaries, plugin manifest paths, dependency-free Node baseline, setup
links, and doctor behavior remain intact. New CLI commands add
`--format text|sdn|json`; old commands retain their existing default text.

## 10. Executable Test Contract

### 10.1 Unit and protocol fixtures

Dependency-free Node tests cover URI normalization, encoded traversal, symlink
escape, slug collisions, deterministic order, cursor/snapshot binding,
visibility cache scope, JSON-RPC error IDs, notification silence, partial input,
and manifest-safe cleanup.

The URI matrix includes slash/backslash traversal, drive/UNC/device paths,
alternate data streams, trailing dot/space, NFC/NFD collisions, invalid UTF-8,
mixed-case identity, single and double encoding, encoded percent, and query
duplication on Linux and Windows policy emulation.

Golden stdio transcripts cover:

- legacy initialize, `initialized`, tools list/call, resource list/read;
- resource templates and paginated list/read;
- malformed JSON, unknown method, invalid arguments, and concurrent IDs;
- EOF with complete and incomplete frames;
- preservation of all six legacy tools and `spipe://skill`.

### 10.2 Materializer integration

A temporary host fixture proves first publish; byte-identical no-op with
unchanged mtimes; one-artifact delta rewriting only affected file, index, and
manifest; interrupted staging preserving the prior committed view; refusal of
malicious symlink/output roots; safe cleanup; and isolation between two dirty
worktrees.

Race tests pause after each authorization/open/create boundary and swap a
directory for a symlink, junction, mount/reparse point, hard link, or different
file before resuming. Create, replace, publish, rollback, and cleanup must either
operate on the originally pinned object or fail without touching the attacker
target. Run native symlink tests on Unix and native junction/reparse tests on
Windows CI.

The same positive suite runs the `ProjectionService` materializer adapter after
`AuthorizationPort` grants it `SafeFilesystem.Materializer`, first against
`NativeMaterializerSafeFilesystem` and then against every admitted
`TrustedFilesystemHelper` operation provider. First publish, incremental
replace, cleanup, crash recovery, identity preservation, and
descriptor-relative race resistance must work on each declared supported
platform. Tests assert that the adapter derives exactly one bounded
`MaterializerRootGrant`, neither provider observes or possesses the capability,
and captured native/helper requests contain no principal, policy, token,
credential, or authorization authority. Tests also reject widened path/operation
bounds, expired or replayed grants, cross-snapshot/projection use, digest or
protocol drift, replayed nonce, arbitrary absolute paths,
malformed/oversized frames, timeout, and helper restart.
`PortableNodeFilesystemVerifier` has read-only diagnostics tests only. A
platform is not reported as supporting materialization if it has only portable
verification or rejection tests and cannot safely materialize the normal
fixture through an admitted mutation provider.

HTTP protocol tests cover issuer/audience/key-epoch/skew validation, stale key
failure, bearer query rejection, cookie-disabled default, CSRF/origin enforcement
when cookies are enabled, hidden-versus-absent response equivalence, conditional
request authorization, `Cache-Control`/`Vary`/ETag rules, and bounded work for
unauthorized requests. Frame/parser tests hit every size, depth, concurrency,
deadline, overflow, and cancellation boundary at limit and limit-plus-one.

### 10.3 SPipe system scenario and manual

The focused MCP executable scenario, normalized to the authoritative system-test
plan, is:

```text
test/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.spl
```

Its generated/manual companion is:

```text
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_mcp_spec.md
```

The cross-spec top-level vocabulary is frozen to these exact literals; this MCP
spec makes `Browse virtual knowledge views` visible and folds the others when
they appear as shared context:

1. `Index canonical knowledge artifacts`.
2. `Browse virtual knowledge views`.
3. `Search and trace artifacts`.
4. `Apply a transactional refactor`.
5. `Audit tree balance and promotion candidates`.

The scenario uses built-in matchers only. MCP exchanges use typed `protocol`
captures and materialized output uses `artifact` captures. Setup is hidden with
`@prev`/`@inline`; the manual must show usable URI/tool examples, pagination,
canonical UID resolution, a trace gap, and the read-only failure without
exposing fixture mechanics as its main flow.

### 10.4 Performance and release gates

The realistic fixture contains 50,000 artifacts and bounded large directories.
Record warm startup, P50/P95 list/read/search latency, maximum RSS, cache hits,
and delta update cost. Verify that request paths perform no full-tree scan or
provider spawn, and that one-file incremental output equals a clean rebuild.

`scripts/build.shs` remains the package smoke gate and gains transcript checks;
it is not the sole verification. The focused system spec, generated-manual
review, traversal/symlink security suite, compatibility transcript, and
materializer fault-injection suite are release-blocking evidence.

## 11. Failure Behavior

All virtual reads fail closed on ambiguous UID, unavailable project revision,
stale cursor, unauthorized visibility, escaped path, or snapshot corruption.
Optional HTTP, editor, semantic, and OS-mount adapters may be unavailable
without disabling legacy stdio, core resource tools, or materialized views.
Provider failure returns a bounded diagnostic and retains exact/lexical core
behavior; it never causes a hidden full rebuild on a hot request.

## 12. Wave 5a SnapshotAuthority and ProjectionPort admission prerequisite

URI parsing and receipt validation do not themselves prove that a claimed
`targetKind`/`targetUid` exists in the selected immutable snapshot. The current
`ImmutableSnapshotStore` exposes project/revision snapshot records but neither
a target inventory nor a workspace/worktree-bound read. Therefore URI,
resources, tools, and materialization are **non-admitted** until this contract
is implemented; adapters must not use a raw store lookup as a substitute.

The composition root creates two non-forgeable ports. `SnapshotAuthorityPortV1`
owns authoritative snapshot membership and its opaque
`SnapshotAuthorityViewV1`; `ProjectionPortV1` owns only deterministic
read-only projection. Their exact operations are:

```text
SnapshotAuthorityPortV1.openBoundSnapshot(
  {workspaceUid, projectUidOrNull, worktreeUid, baseSnapshotUid,
   authoritySnapshotUid, revisionId, registryRevisionId}
) -> Result<SnapshotAuthorityViewV1, SnapshotAuthorityError>
SnapshotAuthorityPortV1.resolveCanonicalTarget(
  view, {targetKind, targetUid}
) -> Result<CanonicalTargetV1, SnapshotAuthorityError>
SnapshotAuthorityPortV1.resolveCanonicalAlias(
  view, {normalizedAliasUri}
) -> Result<CanonicalTargetV1, SnapshotAuthorityError>
SnapshotAuthorityPortV1.listDirectoryTarget(
  view, {viewKind, normalizedLogicalPath, selectorDigest}
) -> Result<CanonicalDirectoryTargetV1, SnapshotAuthorityError>
SnapshotAuthorityPortV1.createExpectedReadBindingV1(
  view, canonicalTargetOrDirectory, normalizedRequest
) -> Result<ExpectedReadBindingV1, SnapshotAuthorityError>
ProjectionPortV1.render(authorityView, canonicalTarget, verifiedReadGrant)
  -> Result<ProjectionDocumentV1, ProjectionError>
ProjectionPortV1.list(authorityView, directoryTarget, verifiedReadGrant, verifiedCursorGrantOrNull)
  -> Result<ProjectionPageV1, ProjectionError>
```

`CanonicalTargetCandidateV1` contains only normalized canonical kind/UID and
an alias-index digest; it is deliberately not a `CanonicalTargetV1` and cannot
be passed to ProjectionPort. `openBoundSnapshot` validates registry workspace/project/worktree ownership,
immutable snapshot UID/revision equality, and a manifest digest before it
returns an opaque view. The manifest inventory has canonical entries for
artifacts, sections, trace/diagnostic aggregates, and virtual directory
mappings. The target and directory operations must prove membership against
that inventory and return the bound manifest digest. `ProjectionPortV1` repeats
the binding/digest equality check and refuses a target or view from another
authority instance. It never scans repository paths, creates identities, or
refreshes indexes.

`ResourceResolver` performs this sequence: (1) parse and normalize once; (2)
resolve the named workspace and worktree exactly; (3) open the receipt-named
authority snapshot only as an untrusted candidate; (4) a legacy alias resolves
through that view's sealed alias index only to a canonical candidate, which is
then passed to `resolveCanonicalTarget`, while a canonical URI proves its
target/directory directly; (5) create the trusted `ExpectedReadBindingV1` from
that sealed proof, including `authorityInstanceUid` and
`authorityManifestDigest`, and verify the canonical-read receipt through
`AuthorizationPortV1`; (6) a direct read calls `render` with that grant, while
a directory list verifies its inbound cursor against the same grant, calls
`list`, then issues the outbound cursor from the page's next position. Every
error before a ProjectionPort call has the bounded public denial class and
cannot disclose a canonical path. An alias never contributes authority or
bypasses target proof; authorization never precedes that proof.

Wave 5a acceptance uses this matrix before any URI implementation is admitted:

| Case | Required observation |
|---|---|
| Correct workspace/worktree/snapshot/revision and artifact/section | Target renders from one matching manifest inventory entry |
| Correct receipt but absent or kind-mismatched UID | Denial before ProjectionPort call |
| Same snapshot UID in foreign workspace/worktree | Denial before inventory access |
| Current project with stale revision or manifest digest | Denial before inventory access |
| Duck-typed authority/projection substitute | Construction or invocation rejects |
| Legacy alias | Canonical target is freshly authorized and then membership-proved |
| Clean rebuild versus incremental update | Equal inventory manifest and projection bytes |
| Directory view | Only manifest-proved children, deterministic page/cursor bindings |

This explicit Wave 5a slice precedes Wave 5 URI/MCP/materializer work. It is a
read-only authority addition; it does not grant write capability or enable
HTTP, notifications, editor VFS, or FUSE/ProjFS.

### 12.1 Binding correction: sealed target inventory before receipt verification

`TargetInventoryManifestV1` has canonical bytes for `{version, scopeKind,
workspaceUid, projectUidOrNull, worktreeUid, baseSnapshotUid, revisionId,
registryRevisionId, entries, aliasIndex, projectionRoot, contributingProjectRoots, rootDigest}`.
`rootDigest` is recomputed
over canonical bytes excluding itself. A separate content-addressed
`AuthorityManifestV1.authoritySnapshotUid` commits the base snapshot UID,
inventory root, scope tuple including `registryRevisionId`, and
`contributingProjectRoots`. Read bindings,
grants, and receipts carry both `baseSnapshotUid` (the exact immutable
SnapshotStore open) and `authoritySnapshotUid` (the authority
manifest/inventory lookup). This avoids a
snapshot/inventory hash cycle. Authority validates both canonical roots before
a view is returned; missing, swapped, or tampered root rejects.

`scopeKind=project` requires a non-null project UID. Workspace root/view/trace/
diagnostics use `scopeKind=workspace_aggregate`, with null project UID and a
sorted committed set of contributing project-snapshot roots. The registry
selects that aggregate only for the exact workspace/worktree/revision.

The resolver does: parse; exact workspace/worktree lookup; open the receipt's
snapshot/revision as an untrusted candidate and validate its sealed inventory;
for an alias, resolve only a canonical candidate then prove it with
`resolveCanonicalTarget`; for a canonical URI, prove its target directly;
derive `ExpectedReadBindingV1` from the proved view/target/request, including
its `authorityInstanceUid` and `authorityManifestDigest`; verify the
canonical-read receipt; for a directory, verify any inbound cursor against
the opaque read grant, list, and issue an outbound cursor only from the returned
next position; for a direct target, render with the read grant.
`CanonicalReadReceiptV1` deliberately has no serialized worktree field, but
`VerifiedReadGrantV1` receives the sealed `ExpectedReadBindingV1`'s trusted
worktree, authority-instance, and authority-manifest claims; cursor code never
derives them. Architecture §21 is the sole cursor
schema and durable-rotation contract. All pre-render failures coalesce to the
bounded public denial class.

## 14. CursorReceiptV1 authority implementation gate (2026-08-26)

The detail implementation persists exactly one `CursorReceiptKeyPolicyV1` with
ordered key and unique rotation records. `rotateCursorReceiptKeyV1` writes a
future `pending` key through a policy-version CAS; the root-only
`applyDueCursorReceiptKeyTransitionsV1` durably changes it to `current`, moves
the prior current key to verification-only `grace`, then to `revoked` at the
recorded deadline and advances the cursor revocation epoch exactly once. A
pending key neither signs nor verifies; a current key signs and verifies; grace
verifies only; revoked does neither. A restart reuses durable state and fails
closed if its current private KeyProvider handle is unavailable. The resolver
may consume only opaque verified grants and never performs these transitions on
its request path. The field order, expiry rule, and rotation request are those
in architecture §21, so this document does not define a second ABI.

### 12.3 Production port and evidence correction

Only branded composition-root `WorkspaceRegistryV1`, `SnapshotStoreV1`, and
`TargetInventoryStoreV1` may implement this design. Valid worktree UIDs are
`W-<opaque-base32>` only. The exact operations are
`WorkspaceRegistryV1.resolveExactWorkspaceWorktreeV1({workspaceUid,worktreeUid})`,
`SnapshotStoreV1.openExactSnapshotV1({workspaceUid,projectUidOrNull,worktreeUid,baseSnapshotUid,revisionId,registryRevisionId})`,
`TargetInventoryStoreV1.publishAuthorityInventoryV1({permit,build})`, and
`TargetInventoryStoreV1.openPublishedAuthorityInventoryV1(exactBinding)`.
`exactBinding` is the closed `{workspaceUid, projectUidOrNull, worktreeUid,
baseSnapshotUid, authoritySnapshotUid, revisionId, registryRevisionId}` tuple: SnapshotStore opens
only `baseSnapshotUid`, while the inventory store uses `authoritySnapshotUid`
to locate the matching content-addressed authority manifest. Neither identity
is inferred from the other.
`publishAuthorityInventoryV1({permit,build})` belongs only to the production commit flow and
requires its branded, non-forgeable `AuthorityInventoryPublishPermitV1` minted
while the transaction fixes `registryRevisionId`; strings,
structural substitutes, and caller-selected aggregate roots deny. That
transaction selects all and only complete project roots for the exact registry
revision.
`openBoundSnapshot` calls only `resolveExactWorkspaceWorktreeV1`, then
`openExactSnapshotV1`, then `openPublishedAuthorityInventoryV1`, and revalidates
registry plus snapshot revision before returning a view. The production KnowledgeCompiler
snapshot-commit path alone publishes complete project/aggregate roots and the
matching authority manifests. Directory requests accept only `1..100` and
produce <=100 entries, <=200 Markdown lines, and <=6,000
`spipe-markdown-token-v1@1` tokens.

`CursorReceiptKeyPolicyStoreV1` persists the single §21.2 logical policy as
an append-only policy/key/issuer/rotation/revocation record family. It must fsync
initial-directory creation and each monotonic-CAS record before acknowledgement;
operation UID equality is replay-idempotent and altered/stale operations deny.
Admission needs production clean/incremental parity for artifact, section,
directory, and aggregate plus restart/fault injection at create/write/fsync/
rename/CAS. Mocks, raw fixtures, and rejected sealed-read drafts are
`NOT-EVIDENCE`.

### 12.4 Production implementation sequencing correction

Before an adapter receives `SnapshotAuthorityViewV1`, the authority store loads
by closed dual-snapshot binding, validates canonical inventory/manifest roots,
and revalidates the live exact registry and snapshot revisions after open. A
cache record, serialized view, caller map, or manifest assertion cannot replace
this sequence.

The commit root owns closure-branded `AuthorityInventoryPublishPermitV1`; its
transaction selects every registry contributor and publishes only
schema-complete ordered project roots, aggregate root, and authority manifest.
No URI/MCP/materializer caller can choose, omit, add, or reorder roots.

`DirectoryInventoryEntryV1` canonically seals `{childTargetUids,
orderingVersion,maxPageLimit,tokenBudget}`. `tokenBudget`
is `{tokenizerId:"spipe-markdown-token-v1",tokenizerVersion:1,unicodeVersion:"15.1.0",maxTokens:6000}`:
reject invalid UTF-8, normalize CRLF/bare CR to LF, then split scalar runs on
ASCII `U+0009..U+000D,U+0020`, Unicode-15.1 White_Space
`U+0085,U+00A0,U+1680,U+2000..U+200A,U+2028,U+2029,U+202F,U+205F,U+3000`, and
ASCII punctuation `U+0021..U+002F,U+003A..U+0040,U+005B..U+0060,U+007B..U+007E`.
`continuationDomain` is derived only after both manifests pass canonical digest,
schema, exact-binding, and live-revision verification. It is SHA-256 of
canonical `{authorityManifestDigest,targetUid,orderingVersion,maxPageLimit,
tokenBudget}` and is never stored in an inventory/manifest, root, or authority
digest. The frozen cursor ABI remains unchanged: existing signed
manifest/target/ordering/limit claims rederive and bind the domain at issue and
verification, preventing a self-dependent manifest digest. Listing requires
`1..100`, returns only unique sealed children in sealed order, and accepts
continuation only for the same bound domain, position, and limit. The policy
ledger uses cross-process CAS, atomic write/rename, file/parent fsync, schema
validation, and contiguous-log recovery. These foundations require
production-oracle PASS before cursor or URI/MCP/projection admission.

### 12.5 Commit-path publisher slice (required before authority admission)

Current `ImmutableSnapshotStore` and graph snapshot publication do not implement
the KnowledgeCompiler transaction assumed above: they do not materialize the
complete sealed artifact/section/directory/project/aggregate inventory. A
standalone authority implementation is therefore **not evidence** for W5A-18/19.

Implement `src/core/knowledge_compiler_commit_publisher.js` with private
`target_inventory_materializer.js` and
`src/storage/authority_publication_journal.js`. The composition-root-only entry
`commit({commitId,workspaceUid,projectUidOrNull,worktreeUid,revisionId,
expectedRegistryRevisionId,expectedBaseSnapshotUidOrNull,
expectedPublicationUidOrNull,inputDeltas})` opens the exact prior tuple (both
expected IDs null only initially), then normalizes deltas;
creates the immutable base snapshot; selects the exact registry revision;
materializes target/section/bounded-directory entries; selects all-and-only
complete contributors; derives project/aggregate inventories; seals both
manifest layers; mints the closure permit; and calls
`publishAuthorityInventoryV1({permit,build})`.

`build` is not caller data: it carries the exact base/registry tuple, ordered
complete roots, target/section digests, sealed pages, and authority manifest.
`AuthorityPublicationJournalV1` stages and fsyncs objects, records, and their parent directories,
then executes one atomic durable current-pointer CAS for a closed
`AuthorityPublicationRecordV1` with registry/base tuple, ordered project roots,
aggregate root, paired authority snapshot UIDs, and manifest digests. The CAS
exposes the head only at its durable pointer boundary, so reads see old-or-new
complete heads only; `AuthorityPublicationJournalV1` supports
deterministic replay/recovery. Equal commit-ID/input replays; altered/stale
input denies. URI/MCP/projection/materializer adapters remain readers only.

Focused production tests must prove all-kind clean/incremental byte parity,
all-and-only aggregate selection, permit/root rejection, substitution/revision
denial, and stage/write/fsync/CAS/rename/parent-fsync/restart recovery. Until
independent review passes, authority and dependent cursor/URI/MCP paths remain
`NON-ADMITTED`.

### 12.6 Publisher re-admission implementation order

The prior publisher candidate is **`NON-ADMITTED`**. Replace it in this order;
do not reuse public journal/`instanceof` admission, in-memory manifests, or
fixture-only recovery as evidence.

1. Make `TargetInventoryStoreV1` validate an unexported closure brand issued by
   `PublisherPermitIssuerV1` during `KnowledgeCompilerCommitPublisherV1.commit`.
   The build, roots, contributor selection, and permit are private transaction
   outputs; URI/MCP/projection callers cannot fabricate them.
2. Canonicalize `CommitInputV1` after delta normalization and persist one
   versioned SHA-256 replay-envelope digest binding commit ID, all exact tuple
   IDs, expected IDs, and deltas. Exact digest replay returns the recorded
   result; every altered envelope or stale expected tuple denies.
3. Put every inventory/manifest object and its content hash under
   `AuthorityPublicationJournalV1` ownership. Journal states are `staging`,
   `objects_durable`, `record_durable`, `current_cas`, `acknowledged`; each
   stage uses atomic replacement/rename plus file and parent fsync. Recovery
   handles a dead writer's lock and an actual process crash at every boundary.
4. Before `openPublishedAuthorityInventoryV1` or recovery returns a head,
   recompute all referenced object hashes, record/project/aggregate/page roots,
   both manifest digests, and exact workspace/project/worktree/revision/base+
   authority snapshot bindings. After an initial head, readers may receive only
   the old complete or new complete record, never null/staged/partial state.
5. Run W5A-26 as a real clean-vs-incremental production comparison and W5A-28
   with independent processes and concurrent readers. Include sealed directory
   ordering, authenticated continuation, `1..100` limits, and the exact 100
   entries/200 lines/6,000 token limits in those oracles.

### 12.7 Admission remediation matrix and implementation handoff

| Seal | Interface that must exist first | Required production oracle | No-shortcut rule |
|---|---|---|---|
| P2 publisher | P1-branded `TargetInventoryStoreV1`, canonical replay envelope, `AuthorityPublicationJournalV1` | Same envelope replays; any changed revision/expected ID/delta denies. Two independently launched writers and SIGKILL recovery expose only a complete predecessor/successor. The durable first-use directory chain is fsynced, and stale recovery unlinks only an exact revalidated owner/lock identity. | No public journal/`instanceof`, in-memory mutex, path-blind stale unlink, process-free race, or fixture recovery. Current `EEXIST` first-use race keeps P2 non-admitted. |
| Read authority | P2 durable records; composition-root `SnapshotAuthorityPortV1`, opaque view, canonical target, closed expected binding | `openBoundSnapshot` opens actual registry/snapshot state through branded `TargetInventoryStoreV1.openPublishedAuthorityInventoryV1`; prove all dual-snapshot/manifest/instance/worktree/revision/target substitutions deny before authorization or projection, and clean/incremental parity passes. | No raw manifest, cache, resolver result, caller map, structural/serialized authority value, or public journal access. |
| URI/projection | Read-authority view plus branded `AuthorizationPortV1` and frozen receipt ABI | Resolve URI/alias only to candidate; prove sealed membership, verify receipt/window/revocation, compare every frozen receipt/binding field, then render/list. Exercise hostile URI/Unicode/path/receipt and canonical-positive matrices with one public denial. | No raw filesystem lookup, alias-only success, local signer, duck-typed grant, or rejected URI candidate reuse. |
| Cursor/MCP/materializer | Admitted URI binding and ProjectionPort | Authenticate continuation domain/position/limit; prove sealed order, `1..100`, <=100 entries, <=200 lines, <=6,000 tokenizer-v1 tokens, zero pre-admission ProjectionPort calls, cache partitioning, and read-only materialization. | No synthetic cursor table, mock projection, adapter-only evidence, or write-through materializer. |

Each row is a merge gate: run its production oracle once, inspect its exact
diff, and obtain an independent highest-capability PASS before starting the
next row. A failed row may be repaired only within that boundary; it cannot be
masked by a compatibility adapter or by advancing an adapter slice.

The matrix adds admission sequencing only. It retains all existing normative
authority/cursor interfaces, raw snapshot APIs, and the exact
`spipe-markdown-token-v1@1` <=6,000-token rule; rejected cursor candidates are
forensic evidence and cannot delete or relax them.
