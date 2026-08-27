<!-- codex-architecture -->
# dynSMF production startup trust-registry cutover

## Status

Implemented as a focused source/interpreter slice. Native Stage 4, bootstrap,
release, signing-root authenticity, and cross-host performance remain outside
this evidence claim.

## Context

The admitted-byte dynSMF loader already failed closed, but production
`src/app/main.spl` supplied an empty trusted-request list and reported the trust
registry as unconfigured. Component startup likewise stopped before its real
graph/loader call. Test-only callers could construct an
`AspectPackLookupRequest`, but app-owned descriptors or resolver catalogs must
not be able to manufacture OS authority.

## Decision

`src/os/smf/dynsmf_trust_registry.spl` owns the exact trust-config grammar,
artifact read, digest check, aspect-directory parse, logical catalog build, OS
export contracts, final admission, and retained byte image.

Each `trust_artifact` binds:

- exact library id and path;
- library ABI and `precompiled_smf` artifact kind;
- ordered, exact manifest export set;
- facet id, aspect id, module id, module ABI, export symbol, and interface ABI;
- SHA-256 of the complete outer SMF image.

The pack-content hash is derived from the aspect directory inside those exact
outer bytes. This is safe because the trusted outer digest transitively binds
the inner bytes. It is an integrity/installation-identity claim, not publisher
authentication or E-APACK003 signature proof.

The registry copies and retains the one artifact content read. Ordinary startup
uses `dynsmf_startup_session_with_registry_dynload_config`; component startup
uses `component_dynsmf_startup_from_registry_config_path`. Both hand the same
retained bytes to `dynsmf_session_load_admitted`. Production never falls back to
the compatibility path-based loaders when registry admission fails.

## Startup ordering

`src/app/main.spl` retains this sequence:

1. parse log and canonical option routing;
2. return from empty, help, or version paths;
3. load the fixed OS trust config and ordinary dynload config;
4. report dynSMF status, run configured component startup, or continue ordinary
   command dispatch.

The canonical option router remains the sole owner of the hard `--` boundary;
trust and component options after it are program arguments and are not
intercepted.

## Failure and compatibility policy

Missing/malformed config, duplicate authority, missing/ambiguous manifest or
image entries, and every id/path/ABI/kind/export/digest mismatch return a typed
failed registry with zero admitted artifacts. Component startup fails before
artifact mapping. Ordinary startup records a failure only when its dynload plan
actually selects a dynamic startup library.

Legacy value/config APIs remain for compatibility tests and static/deferred
planning. They receive no implicit trust: an empty trusted-request list cannot
load, and the non-admitted session APIs remain fail closed.

## Cache, invalidation, and performance

The registry is process-local and immutable-by-convention. There is no global
cache and therefore no stale cross-run invalidation problem. Artifact paths are
not reopened after admission, so same-path replacement cannot change the image
mapped in that startup session. A new process/config load is the explicit
invalidation boundary.

The fast paths do no trust/config/artifact I/O. Non-fast-path admission is
linear in configured artifacts plus bindings and reads each configured artifact
once. Focused closure evidence lives in
`test/05_perf/startup/dynsmf_trust_cutover_source_closure_spec.spl`; the existing
argument-parser/mmap startup spec remains the regression gate.

## Verification boundaries

Mutation tests replace path bytes after registry construction and require
successful loading from the retained image. Negative tests mutate each exact
identity dimension and require a distinct fail-closed reason. No result from
this slice may be described as Stage 4, native performance, bootstrap, Git,
release, signature authenticity, or cross-host proof.
