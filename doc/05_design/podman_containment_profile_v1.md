# Podman containment profile selection

Status: source foundation, AWAITING_VERIFICATION. This checkpoint implements
profile data, request binding, and rejection by providers without an installed
profile. It does not implement a configured containment factory, native capture,
lifetime confinement, teardown proof, or capacity discharge.

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

The ordinary provider validation and public create-command builder refuse a
selected profile before producing a runtime effect. Decoding V4 therefore cannot
silently downgrade to old behavior. The subsequent configured route must match
the selected digest to the installed profile before admission and replay.

## Required configured route

The planned installed wrapper contains canonical base CLI policy and containment
profile bytes with their digests. The existing CLI identity stays unchanged; a
separate observed containment identity must be bound by a completed protected
installation and the common Container API factory. Caller-supplied expected
strings are not completed-installation evidence. No existing exec-control policy
or capped durable-exec state machine is changed by this work.

The runtime executable hash is an observation of a trusted-administrator mutable
path, not sealed execution or protection from an administrator changing it later.
The installed runtime program and expected inspection name are separate facts.
Any acquired native owner must survive error returns until confirmed retirement.

Podman runtime and cgroup-manager options are global and must be applied
consistently to observation and lifecycle commands. Create-only namespace/cgroup
options precede the image. The pinned upstream sources are
[Podman 5.2.5 global options](https://github.com/podman-container-tools/podman/blob/v5.2.5/docs/source/markdown/podman.1.md),
[cgroups](https://github.com/podman-container-tools/podman/blob/v5.2.5/docs/source/markdown/options/cgroups.md),
and [cgroup namespaces](https://github.com/podman-container-tools/podman/blob/v5.2.5/docs/source/markdown/options/cgroupns.md).
The global options source explicitly permits an absolute OCI runtime executable.

## Subsequent live observation

The provider must bracket the native capture with exact retained full container
ID, ownership labels, request, scope, profile, CLI baseline, PID and cgroup
inspection. The native owner is a distinct kind in the existing storage registry;
it does not supervise, signal or adopt the primary process. Its proposed initial
layout accepts one qualified cgroup2 mount with root `/` and retains pinned
cgroup and namespace identities independently of the primary's later liveness.

`Populated` and `EmptySnapshot` are observations only. Deleted, replaced,
unreadable or unsupported cgroups remain unknown with ownership retained.
Neither an empty snapshot nor container-object absence permits capacity release.
Qualified teardown still requires lifetime confinement and a proven deletion or
no-repopulation ordering; helper, storage and workload cleanup remain separate.

## Verification boundary

Source specs cover canonical profile fields, request-version compatibility,
digest changes, malformed data and actual provider/create-builder refusal.
They are authored, not executed. Native owner, configured common factory,
completed installation, positive create/capture and live Podman acceptance are
pending. No compiler retry, native build, package installation or live runtime
campaign is part of this checkpoint.
