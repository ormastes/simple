# Darwin admission evidence — 2026-10-29

Baseline: release/1.0.0 `5f86f2992df`, after #5243. Existing launchd tests prove
that GetJob conceals changed EnvironmentVariables after same-label replacement.
A current PID/CDHash observation cannot recover original-job configuration.

A useful closed boundary is possible without those labels: a kernel-created
retained direct child, AMFI-bound canonical helper, explicit empty spawn
environment, closed descriptors, and mutual Unix stream kernel peer identity.
This trades away launchd's disjoint coalition; it is a bootstrap primitive and
cannot be advertised as complete BuildRunner containment.

The native fixture links a constructor into a copy of the canonical helper. It
requires an empty environment and only descriptors 0–2 before main, then records
entry. The controller deliberately holds an inheritable descriptor and hostile
DYLD_INSERT_LIBRARIES, MallocStackLoggingDirectory, and application variables.
A separate injected dylib writes a marker before main when run unbound (RED
control); bound direct spawn excludes it. Wrong spawn CDHash cannot create the
helper constructor marker. Actual same-UID rogue listeners and impostor peers
receive no admission-authorizing bytes.

Additional evidence covers PID-version/hash mismatch, a silent closed gate,
stopped-child cancellation and bounded reap, saturated endpoint backlog, and
ECHILD cleanup without signalling. On macOS, listen backlog zero does not force
a zero-length queue; the saturation fixture uses backlog one.

Primary sources consulted:
- Apple launch constraints describe executable-context predicates, not an
  attestation of arbitrary environment-variable values:
  https://developer.apple.com/documentation/Security/applying-launch-environment-and-library-constraints
- Apple's dyld process configuration handles environment variables before
  executable main and prunes them based on AMFI policy:
  https://github.com/apple-oss-distributions/dyld/blob/main/dyld/DyldProcessConfig.cpp
- Apple spawn documentation exposes explicit argv/environment inputs:
  https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/posix_spawn.2.html

A helper-main getenv check alone cannot protect earlier constructors. The
implemented boundary is the empty environment passed to the kernel at spawn;
the helper's own empty-environment check is defense in depth.
