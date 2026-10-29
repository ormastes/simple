# Darwin AMFI executable identity, 2026-10-29

## Result and scope

On the tested Darwin 25.5.0 arm64 host, an AMFI spawn constraint containing an
exact CodeDirectory hash binds the image selected by the kernel. A replacement
signed executable is killed before its constructor, even when replacement occurs
after the caller has attached the constraint. Mutation through an already-open
writable descriptor is also rejected before constructors. This is a bound image,
not an immutable filesystem object: denial or SIGKILL is an allowed outcome.

The implementation is an experimental private primitive, not a registered SOSIX
or BuildRunner provider. Public V4 capability flags remain unchanged. It does not
solve strict descendant ownership, cumulative accounting, or lifecycle cleanup.

## Apple mechanisms

- [Defining launch environment and library constraints](https://developer.apple.com/documentation/security/defining-launch-environment-and-library-constraints)
  documents `cdhash` as binary data identifying one code directory and `$in` for
  multiple admitted hashes.
- [Applying launch environment and library constraints](https://developer.apple.com/documentation/security/applying-launch-environment-and-library-constraints)
  documents kernel enforcement of launch and library constraints, including
  `launchd`'s public `SpawnConstraint` configuration.
- [Protect your Mac app with environment constraints](https://developer.apple.com/videos/play/wwdc2023/10266/)
  explains the distinction between a signing identity and an exact code hash.
- The installed `codesign(1)` documents `--library-constraint` and explicitly
  states that OS libraries cannot be restricted by this mechanism. The OS and
  its library trust remain in the trusted computing base.

Direct attachment through `posix_spawnattr_setmacpolicyinfo_np` and serialization
through `/usr/lib/libTLE.dylib`'s Objective-C `LWCR` class are private SPI, not a
publicly supported direct-spawn API. The experiment resolves them dynamically,
requires `security.mac.amfi.launch_constraints_3rd_party_allowed == 1`, uses
constraint version 1/category 0, and returns `ENOTSUP` when prerequisites are
absent. Category 1 rejected even the expected system executable in exploratory
tests and is not used. API availability alone does not prove enforcement.

The private spawn attribute retains a pointer to policy bytes. An initial
temporary-NSData implementation killed even the correct image after its buffer
was released. Caller-owned `SosixDarwinSpawnConstraint` storage fixes that
lifetime; it must remain alive and unchanged until `posix_spawn` returns.

## Dependency closure

The native fixture embeds a signed library constraint permitting only explicit
custom-library CDHashes. Unconstrained positive controls first prove that the
direct, transitive, and injected library fixtures can actually execute. The caller then binds the resulting executable's
CDHash. The fixture uses `hard,kill` signing flags. Tests show an allowed library
loads; a different library, an allowed library's unlisted dependency, and
`DYLD_INSERT_LIBRARIES` injection cannot execute a library constructor. Removing
the signed constraint changes the main image's CDHash and prevents launch.

This does not retrofit arbitrary compiler artifacts. Production admission still
needs an authenticated manifest binding the requested content digest to the
architecture-specific CDHash and its embedded dependency policy, supported
artifact/signing provisioning, and explicit OS-version qualification. Reading
the expected hash from a mutable pathname without authenticating it does not
establish trusted identity. Scripts, interpreters, JIT pages, plugins with broad
policies, and arbitrary mutable data inputs are outside the tested profile.

## Evidence and TDD

`scripts/check/check-sosix-darwin-spawn-constraint.shs` builds small native
fixtures; no P2 compiler rebuild occurs. The RED control deliberately omits the
constraint and executes a differently signed replacement. The bound path then
passes the corresponding rejection check. Both executable and library
constructors create unique markers so a zero-length output cannot masquerade as
proof of nonexecution. All children are waited and temporary fixtures removed.

Native acceptance covers exact identity, post-attachment rename, retained-FD
mutation, direct/transitive dependency policy, injected code, and removal of the
signed policy. `darwin_spawn_constraint_spec.spl` invokes the real native suite
through the canonical process facade and asserts every evidence marker. It is a
macOS-only live spec: non-macOS hosts register an explicit framework pending outcome;
unavailable enforcement on macOS remains a failure and never a pass.
