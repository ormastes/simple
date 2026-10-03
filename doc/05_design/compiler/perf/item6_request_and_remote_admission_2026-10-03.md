# Item 6 request and remote admission implementation

The user authorized completing code/tests and pushing without waiting for a
usable self-hosted runner. This updates implementation state, not qualification:
all new SSpec scenarios still require admitted runtime execution.

## Reader transaction

`package_module_index_read_current_v1` acquires the publication lock, captures
the pointer and bounded payload, then releases the lock before local SHA256 and
decode. Missing storage creates no directories. Lock/unlock failures refuse
admission. All returned graph data is owned; collection may retire the backing
file after acquisition without invalidating that value. Archive lifetimes are
not implied by this guarantee.

## Daemon request ownership

`PackageDaemonSessionV1` binds exactly one workspace identity and cache root.
`begin_request` admits the current index before marking the request active.
Nested requests, mismatched workspace identities and closed sessions refuse.
Refresh during an active request refuses, even if publication advances CURRENT.
The next request revalidates CURRENT and receives the newly admitted generation.
Corrupt refresh clears stale graph state rather than returning a previous hit.

The host owns at most 128 workspace sessions. It balances daemon lifecycle
activity with successful starts and matching ends. A host-monotonic sequence
prevents a token from an earlier closed workspace lifetime ending a new request.
Root substitution for an existing workspace refuses. Closing an active session
refuses; closing an idle session clears generation/root state and removes the
session from the host. Authentication remains the opaque host admission owner;
workspace strings are state isolation keys, not credentials.

`reload_count` counts changed admitted generations. The current implementation
still reads/hashes/decodes on refresh; that counter is not a cache-hit or latency
claim. Warm-performance qualification must measure actual work separately.

Daemon start/stop uses explicit owned-value results because `DaemonBase` is a
struct. The host writes back the returned state and checks PID-removal success
before declaring shutdown complete. Failed removal retains retryable ownership.
The existing host authority serializes PID ownership; path/PID comparison alone
is not a new atomic authentication or lock protocol.

## Remote content integrity

`remote_result_manifest_encode_v1` frames every field except the manifest's own
digest. It preserves ordered references, uses explicit optional-block presence,
and rejects duplicate/invalid digest references and bounded-size violations.
The manifest is at most 1 MiB and each digest list at most 4096 entries. Artifacts
are at most 64 MiB each and 256 MiB in total, with subtraction-before-addition
checks to avoid overflow. Transport allocation before return remains the
transport owner's separate resource boundary.

Admission computes manifest and payload SHA256 locally. The compatibility
`RemoteTransport.recompute_digest` method is never trusted or invoked by
admission. A transport returning a forged field, digest or byte sequence cannot
authenticate itself. `Verified` certifies content integrity only; local action,
target, configuration, producer and dependency admission remain required before
publishing a reusable local action. Remote content never supplies graph or
dirty-state authority.

## Executable evidence

- Reader acquisition/error release: `package_module_index_reader_transaction_spec.spl`.
- Daemon generation/workspace/token lifecycle: `package_daemon_generation_spec.spl`.
- Daemon owned PID state: `daemon_base_owned_spec.spl`.
- Remote forgery, identity, framing and bounds: `remote_client_integrity_spec.spl`.
- Persistence mutations: `package_index_persistence_admission_spec.spl`.

The acceptance CLI invokes real owners and exposes explicit `--scope owner`.
This scope cannot satisfy whole-compiler scenario claims. Default full scope
must report missing filesystem, compiler completion or lifecycle evidence until
those observations exist; it must never print inferred zero scan/compile counts.

## Follow-up source implementation

The driver derives per-module changes from a digest-bound previous/current
generation receipt. It rejects incompatible authority, variants and graph
topology and uses conservative invalidation if the receipt cannot be admitted.
The receipt embeds the prior graph, so collection of that generation file does
not invalidate an already owned transition. Interrupted publication can leave
unreferenced transition files; orphan maintenance remains outstanding.

Archive loading now admits actual member bytes and semantic interface/action
payloads before reporting a cache hit. The same member validator serves warm
and cold paths. Routing reuses its first admitted archive record within the
request. A returned path remains subject to the downstream pin/revalidation
boundary; successful validation does not grant a filesystem lifetime lease.

Generated output consistency uses a caller-supplied declaration and typed producer
receipt. The cold compiled-output boundary checks expected producer and frozen
inventory independently, requires exactly the supplied declaration's input/output
paths and digests, and rejects inconsistent or missing outputs. Canonical emitted receipt
bytes bind provenance; reusable generated identity excludes unrelated inventory
entries while including declared producer, inputs and outputs. This admits
producer results; it does not implement execution of arbitrary generators.

OPEN: both declaration and receipt currently arrive inside the compiled artifact.
There is no independently selected build-plan declaration digest at this boundary.
Replacing both can redefine the allowed output set; current checks prove internal
consistency, not authorization against the user's declared build plan. Bind an
independent plan declaration before treating this as full undeclared-output
admission. The full cold producer still omits generated receipts and its facet
producer refuses domain blocks, so generated producer integration is also open.

New specs exercise real Git inventory refresh, snapshot materialization and
retention, frozen-source refusal, dependency closure, archive corruption and
generated-output admission. Runtime execution, whole-compiler filesystem
observations, process crash qualification, performance and cross-mode parity
remain unverified. No full PSI acceptance or release PASS is asserted.
