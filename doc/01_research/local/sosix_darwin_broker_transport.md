# Darwin broker transport evidence — 2026-10-29

The coalition retirement primitive requires trusted authority for its coalition.
The bound image owner supplies a caller-trusted architecture-specific CDHash;
a mutable launch pathname is not an authority handle. This change supplies an
experimental bound-launch/peer-observation primitive, not a runtime V4 provider.

`launch_msg(SubmitJob)` accepts an in-memory `SpawnConstraint` dictionary with
an opaque 20-byte `cdhash`. No mutable job plist or `launchctl` subprocess is used.
Apple documents SpawnConstraint enforcement before the executable starts:
https://developer.apple.com/documentation/security/applying-launch-environment-and-library-constraints
The local SDK's `launch.h` declares SubmitJob/GetJob/RemoveJob and `sys/un.h`
declares LOCAL_PEERTOKEN. The native probe verifies those interfaces on Darwin
25.5.0 arm64, including AMFI's third-party launch-constraint enforcement gate.

A successful SubmitJob reply acknowledges registration; it does not establish
that the helper entered. Wrong CDHash and a same-path differently signed
replacement never enter the fixture constructor. The unbound replacement does
enter, establishing a working adversarial control. GetJob can disappear after
failed admission. Live RemoveJob can return EINPROGRESS; absence is ESRCH.
Neither response proves a descendant tree reaped.

Native LOCAL_PEERTOKEN returns the connected process's PID and PID version.
`csops_audittoken` operation 5 checks that incarnation's CDHash and rejects a
modified token version. The test also changes the peer image using exec on a
retained socket: the stale token is rejected. An unrelated same-UID process
running the exact same image is rejected against GetJob PID. A same-UID socket
pathname substitute receives zero protocol bytes because the helper authenticates
the controller PID/version supplied in the job arguments; this does not prove the
original submission survived replacement.

An actual RemoveJob/re-submit of the same label and exact trusted helper cannot
rebind an already authenticated transport: its kernel unique ID/version differs.
Labels remain discovery/housekeeping identifiers, never authority for signalling.

## Blocking provenance result

Independent review identified initial label replacement, which is distinct from
replacement after an incarnation has been pinned. Native probing confirms GetJob
returns program/arguments/PID but omits EnvironmentVariables and SpawnConstraint.
The adversarial checker now removes the original registration before its first
observation, recreates the same label/image/argv with an injected variable, and
proves the environment changed while the kernel peer/code observation succeeds.
The API is therefore named `observe_peer` and has no admission-authorized state.
Original-job provenance remains unavailable; V4 ownership stays unavailable.

A separate investigation submitted a socketpair endpoint through legacy Sockets.
`launch_activate_socket` did not recover it. Legacy `launch_msg(CheckIn)` returned
Sockets but no submitted control endpoint either. Neither is accepted as an
independent bootstrap proof on this host. No mutable pathname or missing GetJob
field is substituted for that missing authority.
