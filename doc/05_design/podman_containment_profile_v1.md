# Podman containment profile selection

Status: configured provider source, AWAITING_VERIFICATION. Profile data, request
binding, actual configured observation/creation, and live native capture
association are implemented. Common protected installation/factory composition
is a separately reviewed dependency. Lifetime confinement, teardown proof and
capacity discharge are not implemented by this observation capability.

## Authority and compatibility

The protected provider profile binds the original CLI policy digest, an approved
absolute OCI runtime program, its expected observed digest and inspection name,
and the cgroup manager. The profile version fixes the requested configuration:
enabled cgroups, private PID and cgroup namespaces, nonprivileged operation,
dropped capabilities and no-new-privileges. These are requested configuration,
not evidence that all descendants remain contained throughout their lifetime.

Only `containment_profile_digest` enters the workload request. A nonempty
selection uses retained-request and semantic-digest version 4, including explicit
terminal and user fields. An empty selection preserves historical V1, V2 and V3
bytes and digests. The operation ID remains separately bound recovery metadata.
An existing started workload cannot acquire a containment claim retrospectively.

Providers without an installed profile and the public legacy create-command
builder refuse a selected profile before producing a runtime effect. Decoding V4
therefore cannot silently downgrade to old behavior. The configured provider
matches the selected digest before admission and replay, and refuses an unselected
request rather than changing its legacy configuration.

## Required configured route

The installed wrapper contains canonical base CLI policy and containment
profile bytes with their digests. The existing CLI identity stays unchanged; a
separate observed containment identity must be bound by a completed protected
installation and the common Container API factory. Caller-supplied expected
strings are not completed-installation evidence. No existing exec-control policy
or capped durable-exec state machine is changed by this work.

The runtime executable hash is an observation of a trusted-administrator mutable
path, not sealed execution or protection from an administrator changing it later.
The runtime program and inspection name are separate observed fields. Podman
5.2.5 reports the full absolute program as the name when `--runtime` selects an
absolute path; the configured wrapper requires that exact spelling and never
normalizes to a basename. Historical identifier-only candidate profiles remain
valid data but cannot instantiate this absolute-path route.
Any acquired native owner must survive error returns until confirmed retirement.

Podman runtime and cgroup-manager options are global and must be applied
consistently to observation and lifecycle commands. Create-only namespace/cgroup
options precede the image. The pinned upstream sources are
[Podman 5.2.5 global options](https://github.com/podman-container-tools/podman/blob/v5.2.5/docs/source/markdown/podman.1.md),
[cgroups](https://github.com/podman-container-tools/podman/blob/v5.2.5/docs/source/markdown/options/cgroups.md),
and [cgroup namespaces](https://github.com/podman-container-tools/podman/blob/v5.2.5/docs/source/markdown/options/cgroupns.md).
The global options source explicitly permits an absolute OCI runtime executable.

## Subsequent live observation

The provider brackets the native capture with exact retained full container
ID, ownership labels, request, scope, profile, CLI baseline, PID and cgroup
inspection. The native owner is a distinct kind in the existing storage registry;
it does not supervise, signal or adopt the primary process. Its initial
layout accepts one supported cgroup2 mount with root `/` and retains pinned
cgroup and namespace identities independently of the primary's later liveness.

`Populated` and `EmptySnapshot` are observations only. Deleted, replaced,
unreadable or unsupported cgroups remain unknown with ownership retained.
Neither an empty snapshot nor container-object absence permits capacity release.
Qualified teardown still requires lifetime confinement and a proven deletion or
no-repopulation ordering; helper, storage and workload cleanup remain separate.

## Verification boundary

Source specs cover canonical profile fields, request-version compatibility,
digest changes, malformed data, legacy refusal, configured common-API create
with independent argv, runtime drift, strict inspect fields and scripted-native
capture refusal. They are authored, not executed. The native owner dependency is
`21f03e9571f66890a0e7de59f8ee87d891d793f0`; the profile foundation is
`5644f854ec61e7bedc7ebc495b5f1b2d07c97c63`.

Completed installation and common configured factory/capture wrappers are
separately owned by Host and architecture. Native/SSpec compilation and positive
live Podman acceptance remain pending. Initial capture failure closes or retains
its not-yet-published owner; later common observation must never close a stale
copied owner merely because metadata validation failed.

Output-follow and exec control explicitly refuse containment-selected parents
until their helpers and separately installed Engine service bind this profile.
No old helper argv or exec identity silently substitutes. The closed durable-exec
owner/record files are unchanged. Synchronous executable hashing and CLI
observation are not a hard wall-time or responsive-event-loop guarantee. No
compiler retry, native build, package installation or live runtime campaign is
part of this checkpoint.
