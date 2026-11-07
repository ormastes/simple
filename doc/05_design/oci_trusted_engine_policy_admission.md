# Explicit trusted-local Podman policy admission

Status: **AWAITING_VERIFICATION** source slice; executable qualification remains blocked.

## Approved scope and ownership

The root coordinator approved an explicitly selected trusted-local-admin engine
policy after command PR #7574. This extends `LinuxOciRuntimeProviderV1`; it does
not introduce another provider framework. Host owns the protected policy file
selected by `runtime_class_ref` and signed enrollment. The provider owns the
canonical policy codec, observation, and every native engine invocation. A
remote workload request cannot select an executable, policy file, or store.

Initial policy mode is `trusted-local-admin-v1`, Linux rootless Podman only.
Unknown modes, including an unsupported sealed mode, fail explicitly. Existing
unqualified provider constructors remain compatibility APIs and cannot satisfy
the new host enrollment observation requirement.

## Trust boundary

An installed administrative policy names an absolute canonical executable,
expected effective UID, graph root, run root, storage driver, and ordered storage
options. The provider observes executable bytes through an existing retained
file owner, records the hash, and checks identity stability across that read.
The executable must have a non-root parent directory, such as `/usr/bin`:
the retained trusted-directory owner cannot open `/`, so a path such as
`/podman` is rejected during policy validation before native observation.
This is an observation of an administratively trusted mutable path. It is not
sealed execution, a race-free hash-to-exec guarantee, or proof that shared
libraries and runtime helpers are immutable. Dynamic ELF executables are within
the selected trust model; static-only executable pinning is not a universal gate.

The policy digest binds the canonical codec's fields, including storage options.
The observation identity digest binds that policy digest, actual executable
digest, native effective UID, engine version, local/rootless status, and observed
store identity. Host compares the observation to its signed retained enrollment;
the provider retains its own established observation and refuses subsequent
drift before lifecycle effects. Changed observations do not advance generation
or release host capacity automatically.

## Native route and observations

Every scoped engine invocation uses the approved absolute executable and typed
global arguments selecting local mode and the approved storage scope. There is
no PATH engine resolution, remote environment fallback, shell concatenation,
or implicit fallback to Docker. UID evidence uses a native owner rather than a
second PATH-selected `id` command.

Explicit root/driver flags clear configured driver storage options in Podman.
The policy therefore retains those options instead of silently discarding
fuse-overlayfs configuration. Every option remains one argv entry and enters
the policy digest. An intentionally empty option set uses only syntax supported
by the Podman manual. Returned graph options must agree with the requested
scope; unsupported representations fail explicitly.

Engine info is external JSON interoperability. Output is bounded before parsing;
a lexical nesting bound precedes the existing strict JSON parser, which rejects
duplicate keys and trailing tokens but does not itself bound recursion. Missing
or wrongly typed identity fields, remote service operation, non-rootless state,
wrong UID/store/driver/options, and executable changes all fail closed.

Re-observation before effects has bounded but nontrivial hashing/process cost.
This slice makes no latency/RSS qualification claim. A later cache may only be
introduced with an explicit invalidation contract and evidence.

## Agreed consumer API

Provider-local `engine_policy_v1` exports `LinuxOciEnginePolicyV1`,
`LinuxOciEngineObservationV1`, canonical
`linux_oci_engine_policy_encode_v1`/`decode_v1`, and
`linux_oci_engine_policy_digest_v1`.

`LinuxOciRuntimeProviderV1.new_with_engine_policy(...)` returns a result rather
than silently downgrading invalid policy. `engine_observation_v1()` supplies
the actual observed identity for host enrollment and comparison. Existing
request digest/retained V2 intent binding remains required before effects;
policy observation does not grant permission to execute a workload.

The latest scope instruction ends this slice at coherent source, fixtures, and
documentation awaiting verification. Host is completing its enrollment core
separately; it has not yet connected this provider observation API to a shipped
CLI execution path. API agreement is not evidence of that vertical composition.

## Terminal owner follow-up

The daemon lane owns generation-bearing `PipedProcessRefV1` over the existing
native piped-process registry. Caret owns the authenticated smux consumer and
sole pane output reader. A future provider `LinuxOciTerminalSessionV1` transfers
that reference after exact runtime identity/policy validation; it never exposes
caller-selected argv as authority. Raw PIDs cannot provide stale-copy safety.

The attach helper must explicitly disable signal forwarding before smux cleanup
can terminate that helper. Workload stop/remove stays a separate authorized
provider operation. This policy slice does not claim terminal support, native
PTY resizing, binary-clean streaming, or completed smux session adoption.

Caret's consumer-side contract is
`smux_pane_adopt_terminal_transport(session_id, window_id, pane_id,
expected_epoch, expected_revision, expected_child_incarnation, reference)`.
Failure leaves cleanup with the caller; success transfers the canonical
process-local reference to the pane and means owned/opening, not an engine
attachment acknowledgement. The first proposed provider adapter is output-only
(`--no-stdin --sig-proxy=false`), with input, geometry, and interactive support
false. That adapter and the authenticated runtime binder remain unimplemented
here; native references must never be deserialized from a remote request.

## Primary-source evidence

- [Podman global options](https://docs.podman.io/en/stable/markdown/podman.1.html):
  local/remote selection, root/runroot/driver scope, and storage option behavior.
- [Podman info](https://docs.podman.io/en/latest/markdown/podman-info.1.html):
  host, security, version, and store observation structure.
- [Upstream info implementation](https://github.com/podman-container-tools/podman/blob/main/libpod/info.go),
  fetched 2026-11-07 through the GitHub connector, file blob
  `a9dec0609fcbd38449a7b93e96992d71647c45c0`: ordinary graph option values are
  strings; `mount_program` values become objects containing `Executable`,
  `Version`, and `Package`. This supports a narrow explicit
  `overlay.mount_program` adapter. Other transformed option shapes need separate
  supported parsing rather than guessed coercion.
- [Podman attach](https://docs.podman.io/en/v5.4.2/markdown/podman-attach.1.html):
  explicit signal-proxy selection for independent helper teardown.

## Evidence limits

Source acceptance and prevention cases:

| Criterion | Required independent assertion |
|---|---|
| Canonical policy | Encode/decode roundtrip; unknown/missing/duplicate fields rejected; changed semantic fields change the computed digest |
| Explicit mode | Unknown or sealed mode fails before any engine execution; Docker policy is unsupported |
| Exact route | Full absolute program and global argv prefix independently compared for info and lifecycle effects |
| Scope | Wrong UID, remote/rootful state, graph/run root, driver, or observed option fails |
| Storage options | Empty, scalar, and `overlay.mount_program` cases preserve/check values; unknown nested shapes fail |
| Parser bounds | Duplicate JSON keys, trailing tokens, oversize output, malformed/deep nesting fail |
| Observation binding | Changed binary/version/store observation cannot authorize a later lifecycle effect |
| Literal argv | Spaces and metacharacters remain one value; NUL cannot cross the process boundary |
| Compatibility | Existing no-policy constructor fixtures retain their existing scope and behavior |

These source fixtures are not a substitute for a future live matrix: an actual
installed dynamic Podman, configured rootless user/store, immutable workload
request, real journal, known output, independent inspection, and exact cleanup.

Podman was absent during this campaign. No tools or services are installed or
started by this change. Native specs, core/MCP checks, and SPipe remain
unexecuted until an admitted runtime is available. The known unchanged
`common.crypto.secure_memory.fill_span` producer failure is not retried under
another lane name. Authored fixtures and source review are not live backend
conformance, runtime continuity attestation, or release qualification.
