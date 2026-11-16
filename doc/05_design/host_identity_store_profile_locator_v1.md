# Exact retained profile configuration locator V1

Status: SOURCE_AUTHORED_NOT_RUN. Narrow additive copies originate from actual
merged PR9497 commit `4f675325d9655e2a3e95aecb165b49ffba088962`. Existing
freezes, worktrees, index, app files, generic path/preflight and projection
behavior remain unchanged. The inherited source batch is 5/6; no runtime or
native campaign is restarted.

The one new function is
`host_identity_store_profile_locator_v1(owner: HostIdentityStoreV1, leaf: text)
-> Result<text,text>`. It accepts only exactly64 lowercase hexadecimal bytes
followed by .profile. Both the generic entry and platform method enforce this
role; .key/.hosts, alternate suffixes, traversal, NUL and malformed stems refuse.
No new registry, authority type, runtime export, app OS branch or generic raw
root/file getter is added.

The actual canonical platform guard and existing protected read validate the
current retained store and existing target before any locator data is returned.
Linux uses its genuine origin/main-thread check and retained inode/name/privacy
checks. Windows uses the actual private-root journal's proved-absence and file
privacy/current checks. The 65536-byte UTF8 bound remains unchanged. Existing
read/native/integrity failures propagate; actual absence is
identity-store-profile-absent. Bare Result errors never discard actual native
obligations: the caller's same owner alias retains canonical cleanup state.

Linux returns the actual root spelling plus /journal/leaf. Windows returns the
canonical original root namespace plus backslash journal/leaf, preserving
GLOBAL?? and refusing no original prefix solely for transport reasons. This
is a protected configuration locator, not an external SSH path, executable
authority or live owner. No OpenSSH normalizer is invoked. The function neither
parses profile SDN nor rewrites a profile as a key/hosts role. The installer
still requires actual paired current proof, canonical content hashing and
confirmed immutable publication/readback before exposing this locator.

The existing server_ssh_profile_load_v1 dependency is owner-bearing and strict:
it calls stdin_command_profile_read_v1 then strict full-profile decoding. Its
Windows branch preserves the root namespace, opens the actual protected store,
and reports a retained cleanup owner on failure; its POSIX branch retains the
documented trusted-namespace boundary. The real forward fixture closes the
original writer before calling that fresh loader, avoiding a competing journal.
The returned string does not retain authority after close: the loader must
perform its own actual protected validation, and the fixture retains every
loader cleanup capability. The positive full-profile fields are compared with
the strict decode of the actual originally protected bytes, including exact
store_root. No key material or raw profile bytes enter diagnostic assertions.

The mandatory actual fixture covers positive original namespace/loader binding,
exact production role refusal, stale owner, proved absence without poisoning a
valid owner, unsafe target refusal and surviving cleanup truth. All are authored
NOT_RUN. Native faults, same-user/root/kernel limits, Windows namespace/Service
interop, file substitution and process execution remain outside qualification.
Consumer percent/environment expansion checks remain required for actual SSH
paths; this locator is never routed into that transport path role.
