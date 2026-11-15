# Server context implementation design

See [architecture](../04_architecture/server_contexts.md) for the trust and
transport boundary. Public contract types are `ServerRecordV1`,
`ServerContextV1`, `ServerConfigV1`, and `ResolvedServerV1`.

`decode_server_config_v1` rejects malformed SDN and references before
`resolve_server_context_v1` selects a record. `default_server_config_v1`
preserves local defaults; it is never used to mask an invalid explicit file.

The SSH profile decoder binds auth/trust references to local identity and
known-hosts paths. `server_ssh_argv_v1` constructs strict fixed-command argv.
`server_ssh_start_v1` and bounded poll/cancel turns retain their process lease.
Shared gateway framing validates request/reply correlation. Authenticated SSH
provides transport identity, while domain authority remains independently checked. Remote controller config independently fixes root, identity
and allowed actions before dispatch to existing domain owners.

An explicit endpoint is configuration intent until actual DNS/connectivity,
host-key identity, installed peer policy and compiled runtime are tested.
Missing capabilities and unresolved leases return failure/uncertainty.

Host identity commands reuse the retained `HostIdentityStoreV1` owner. Private
keys, public pins and protected profiles occupy distinct `.key`, `.hosts` and
`.profile` roles. Generation obtains OS entropy only after store admission and
absence validation, publishes atomically without replacement, and rereads the
actual winner after a race. Pins bind a separately verified fingerprint and
immutable alias. Profile installation verifies key/pin bindings and transport
preflight before publication. A dedicated unavailable path projection preserves
logical key/pin publication facts; other errors and unresolved cleanup stay
nonzero with typed owners. No native namespace prefix is downgraded.

`container-plan-prepare` is the application entry to unsigned public discovery
projection. It strictly decodes an unverified candidate context containing
backend, host scope and native provider policy, decodes the provider's retained
request, selects the configured container endpoint and calls the existing typed
pre-sign constructor. The output carries the complete unsigned execution
request and its request/plan digests. It explicitly requires signing and
admission and asserts neither owner verification nor execution authorization.
No runtime owner opens or native effects occur during preparation.

The existing assignment, host reservation and dispatch state machines remain
the authority for a later composed workflow. This increment does not provide
the application composition that obtains their receipts and required signatures
then submits and dispatches the candidate. The actual provider owner must still
verify scope, policy, resources and signed grants; candidate input is no proof.

Implementation status is source-only. Windows protected storage and the native
counted-stdin process owner do not establish a safe external OpenSSH key-path
projection. That capability remains unavailable and the client fails closed.
Compiler, native provider, OpenSSH and live deployment checks are NOT_RUN.
