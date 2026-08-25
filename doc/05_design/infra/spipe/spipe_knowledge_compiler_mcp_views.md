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
ProjectionPort.list(snapshot, target, cursor, limit) -> ResourcePage
ProjectionPort.read(snapshot, target, range) -> ResourceContent
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

Workspace identity is explicit and stable. Resolution precedence is:

1. tool/resource workspace identifier;
2. server configuration supplied at launch;
3. `SPIPE_HOST_ROOT` compatibility environment value;
4. one configured default workspace.

There is no per-request current-working-directory inference. Startup resolves
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
- no more than 200 Markdown lines or approximately 6,000 model tokens;
- cursor pagination before either bound would be exceeded.

A cursor is an opaque signed or integrity-checked encoding of snapshot ID,
view identity, filters, effective authorization-scope digest, last sort key,
and limit. Reuse against a different snapshot or effective scope returns
`stale_cursor`; it never silently skips, duplicates, or discloses results.

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

JSON-RPC failures preserve the request ID and distinguish parse error, invalid
request, method not found, invalid parameters, stale cursor, unauthorized,
not found, resource limit, and internal error. Notifications never receive a
response. Partial stdio chunks and multiple messages per chunk are supported.
Initialize negotiates a mutually supported version, processes `initialized`,
and rejects requests that require initialization before lifecycle completion.

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
- read response: 1 MiB; generated Markdown: 200 lines/~6,000 model tokens;
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
