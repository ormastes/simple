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
