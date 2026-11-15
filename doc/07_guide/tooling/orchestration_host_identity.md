# Shared host identity, server trust and public-key exchange

Status: **SOURCE IMPLEMENTED / NOT_RUN / NOT DEPLOYED**. These are command
examples for the authored CLI, not evidence of a working installed binary,
native provider, cryptographic interoperability or a live server connection.
Replace example paths, hostnames, executable digest and independently verified
fingerprint with actual values before using an admitted runtime.

[Stronger OS secret storage and qualification TODOs](../../08_tracking/todo/orchestration_host_identity_secure_store.md)
remain open, including Keychain, DPAPI/libsecret, memory protection and Windows
external SSH path projection. Private files currently use owner/ACL protection
and contain unencrypted OpenSSH private material.

## 1. Generate one local identity

Choose a root whose **parent already exists and is trusted**. For
`/home/user/.simple-host-identities`, `/home/user` and its ancestors must satisfy
the platform ownership/permission policy and must not be replaceable through
untrusted writable directories or symlinks. Store open creates only the final
private root and fixed `journal` child; it does not recursively create an
untrusted ancestry. POSIX directories/files are private before secret bytes
(0700/0600); Windows uses protected retained ACL owners.

```text
simple orchestrator key-generate --store-root /home/user/.simple-host-identities --auth-ref secret://shared-host
simple orchestrator key-generate --store-root /home/user/.simple-host-identities --auth-ref secret://shared-host --name "operator laptop"
```

Choose the first invocation for a current-time public label (`host-<unix-micros>`)
or supply `--name` for a text hash fragment plus current time. An explicitly
empty name or a name longer than 256 UTF-8 bytes is rejected. The same existing
`authRef` returns its original identity without resampling key time/entropy or
renaming it, so these are alternative invocations rather than a rename sequence.

The store is admitted and identity absence established before clock/entropy
use. User text and current time only name the key: supplied text becomes a hash
fragment, so newline, CR and NUL cannot inject another key line. Omitting text
never makes time a private seed. The existing OS CSPRNG supplies 32 seed bytes and four
OpenSSH check bytes. The pure Ed25519 implementation derives the public key;
the OpenSSH codec checks embedded public/private consistency before publication.
The private seed/PEM is never printed, logged or placed in SDN configuration.

The same `authRef` returns the existing identity. Concurrent generation returns
the actual winning existing key, rather than claiming a discarded new key was
installed. Save the public fingerprint and supported `identityPath` receipt.

## 2. Independently verify and pin the server SSH host key

Obtain the server's SSH host public `.pub` file and expected SHA-256 fingerprint
from its administrator through an independently trusted channel. The file must
contain one canonical `ssh-ed25519` public key. No blind keyscan or implicit TOFU
is performed.

```text
simple orchestrator key-pin --store-root /home/user/.simple-host-identities --public-key-file /home/user/build-server.pub --trust-ref trust://build-server --server build --expected-fingerprint "SHA256:REPLACE_WITH_VERIFIED_FINGERPRINT"
```

Keep `knownHostsPath` when supplied; a path-free template also works when the
receipt contains only the logical trust reference. The alias is `build`. Existing pins
are immutable: changed keys and aliases fail, even when a caller supplies the
changed key's correct fingerprint. Explicit verified rotation is a separate
administrative operation.

The generated client identity must separately be authorized for SSH login.
**Pending registration is not passwordless login authorization.** If there is
no existing authorized SSH login/profile, export the public key and deliver it
to the administrator for an explicit initial grant before attempting exchange:

```text
simple-orchestrator key-public --store-root /home/user/.simple-host-identities --auth-ref secret://shared-host
simple orchestrator key-registration --store-root /home/user/.simple-host-identities --auth-ref secret://shared-host --server build
```

`simple-orchestrator` accepts the same arguments as `simple orchestrator`.
`key-registration` is an export-only SDN request: `sent: false`,
`serverGrantRequired: true`, `authorized: false`, `enrolled: false`. Public
inspection also accepts `--public-key-file /absolute/client.pub`; it does not
read a private file to produce arbitrary output. No command edits remote
`authorized_keys` or automatically grants access.

## 3. Install the protected SSH profile

For first setup, write `/home/user/build-ssh.sdn` as an installer-only template.
It has **no** `identityPath` or `knownHostsPath`: either field is rejected even
when empty. Replace the digest with that of the actual administrator-trusted
SSH executable:

```sdn
version: 1
kind: server-ssh-profile-template
authRef: "secret://shared-host"
trustRef: "trust://build-server"
user: builder
sshExecutable: "/usr/bin/ssh"
hostKeyAlias: build
storeRoot: "/home/user/.simple-host-identities"
sshDigest: "REPLACE_WITH_64_LOWERCASE_HEX_EXECUTABLE_SHA256"
```

`sshDigest` is required on Windows. `storeRoot` must exactly match the actual
retained root used for this identity and pin. Under the supported Windows
Service5 execution context, preserve the administrator-provided native root
spelling, including `GLOBAL??`; do not manufacture an ordinary drive alias.
Interactive Windows execution remains unsupported by the paired provider.

```text
simple orchestrator key-profile-install --store-root /home/user/.simple-host-identities --profile-file /home/user/build-ssh.sdn
```

The installer opens the actual protected store and acquires one paired owner
for the existing `authRef` key and `trustRef` host pin. A bounded acquisition
uses the existing service namespace/current-root/file proofs. Only the actual
current paired-path result supplies both credential paths. The installer then
builds the existing complete `server-ssh-profile`, applies its strict path and
field validation, verifies the actual pinned alias, and rechecks the same pair
immediately before publication. Unsupported SSH percent/environment expansion
syntax is refused. A template never becomes a runtime profile by itself and
never supplies dummy credential paths.

Existing complete `server-ssh-profile` input remains supported. Its supplied
paths must exactly match the actual pair; conflicting caller paths fail before
publication. Canonical complete-profile SDN and the existing immutable
`sha256(canonical-profile).profile` role are unchanged. Exact existing content
is idempotent; changed content has a different `profile://<digest>` reference.
The pair stays retained through publication and existing-byte comparison.

The returned `profilePath` is the positively validated **protected config
locator**, not an SSH credential projection. It may retain a native Windows
`GLOBAL??` prefix. Pass it unchanged as the SSH-profile argument after successful
cleanup; the existing protected loader consumes it only after the prior writer
has closed. It is not substituted into `identityPath`/`knownHostsPath`. The
installer never chmods or copies configuration into an ordinary unprotected
file. A successful immutable publication remains reported if later locator or
cleanup confirmation fails; such a command returns nonzero and keeps actual
pending owners for the existing cleanup flow.

Generic key/pin `path_v1` and transport preflight behavior remain unchanged.
Their dedicated `identity-store-transport-projection-unavailable` result may
still return logical key/pin success without a path; first-time installation
uses the separate actual paired proof instead. Pair invalidation, replacement,
reference/root mismatch or namespace failure never falls back to prefix
stripping or a newly created pair. Native/OpenSSH/Service5 qualification for
this setup remains **NOT_RUN**; source support is not deployment evidence.

## 4. Configure one shared server row

For example, `/home/user/servers.sdn` can bind all consumers to the same server
record. Replace the example host and installed remote executable with the
administrator's actual values:

```sdn
version: 1
currentContext: remote
servers:
  build:
    transport: ssh
    host: build.example.test
    port: 22
    authRef: "secret://shared-host"
    tlsRef: "trust://build-server"
    remoteExecutable: "/usr/local/bin/simple-orchestrator"
contexts:
  remote:
    sharedServer: build
    consumers:
      simple: build
      orchestrator: build
      caret: build
```

Simple and Orchestrator resolve the same `authRef` and trust reference, so they
use one local identity rather than duplicate keys. Caret may share this row;
it can instead have an explicit different server mapping when required. For
SSH, the existing `tlsRef` configuration field identifies the SSH host trust
reference. It does not turn the host key into an application signing key.

The server administrator must install the gateway with the exact `serverName`
(`build` here), `controllerId`, private `identityStoreRoot`, actual SSH **host**
`serverPublicKeyPath`, and an explicit allowlist containing `identity-register`
and/or `identity-server`. These roots/paths come from installed local
configuration, never the request wire. A real authorized SSH login/profile is
required to reach this gateway; local profile installation alone grants nothing.

## 5. Send the public key and receive the server key

Use the actual `profilePath` receipt in place of the marked profile argument:

```text
simple orchestrator key-sendserver /home/user/servers.sdn simple remote build host "REPLACE_WITH_PROFILE_PATH_RECEIPT" --store-root /home/user/.simple-host-identities --auth-ref secret://shared-host --server build --controller-id controller-1 --request-uid registration-1
simple-orchestrator key-takeserver /home/user/servers.sdn orchestrator remote build host "REPLACE_WITH_PROFILE_PATH_RECEIPT" --store-root /home/user/.simple-host-identities --trust-ref trust://build-server --server build --controller-id controller-1 --request-uid server-key-1 --expected-fingerprint "SHA256:REPLACE_WITH_VERIFIED_FINGERPRINT"
```

The positional arguments select config, consumer, context, server,
`host|container`, and SSH profile. `--server` must equal the selected installed
server name. The controller ID must match the installed gateway. Choose an
explicit request UID for correlation. Send also accepts
`--public-key-file /absolute/client.pub` instead of local store/auth flags.

`key-sendserver` sends only canonical public material through the existing fixed
authenticated SSH gateway. The server persists an immutable **pending** public
registration record. Exact duplicate uploads are idempotent; conflicting
records fail. Its correlated receipt says `pendingGrant: true`,
`registered: false`, `enrolled: false`, `authorized: false`, and
`uploadedKeyPossession: not-proven`. Current SSH authentication proves the
existing login key; it does not prove possession of a different uploaded key.
An administrator must separately approve any grant.

`key-takeserver` requests an empty-source `identity-server` action. The response
identifies `keyType: ssh-host-ed25519` and the server/controller/request IDs.
The client strictly checks schema, correlation, key/fingerprint consistency and
the independently supplied expected fingerprint, then reuses immutable pinning.
Existing SSH trust is necessary to make this request; it cannot bootstrap an
untrusted first connection. An SSH host key and an application signing key have
different roles.

## Storage receipts and remaining limits

The actual layout is `root/journal/<reference-hash>.key` for private identities,
`<reference-hash>.hosts` for pins, and `<canonical-profile-hash>.profile` for
protected profiles. Paths come from the retained owner, not root concatenation.
Atomic no-replace publication reports `fileSynced` and `namespaceSynced`
separately. File flush success does not prove directory metadata durability
through a crash; Windows currently leaves namespace durability unconfirmed.

The installer drains the paired owner in at most 64 normal cleanup phases,
then closes the parent store. It advances only the explicit normal pending-phase
marker; a retained native error stops the drain rather than retrying a consumed
descriptor or repeatedly failing call. Actual unresolved pair children remain
canonical in the same retained parent, which is carried in the process-local
reply. Output is nonzero with `cleanupPending`; original operation failures and
publication facts remain visible. The existing cleanup consumer must retire
pending owners before another writer/loader is treated as admitted. Generic
commands retain their prior cleanup behavior.

Mutable buffers receive best-effort wiping. Immutable entropy-hex/private-PEM
text and crypto intermediates do not have complete RAM-erasure or locked-memory
protection. The linked OS secret-storage TODO remains open. All native,
OpenSSH interoperability, profile setup and live exchange checks in this guide
are **NOT_RUN**; no deployment, grant or successful connection is asserted.
