# TODO: host identity private-store adapter and authenticated enrollment

Status: OPEN. Public parsing, fingerprint comparison, public registration
request export, generation and persistent pin installation are source
implemented. Authenticated public-key send/receive through the fixed SSH gateway
is source implemented; uploads remain pending administrative grant. The retained
platform-store adapter is assembled in its separate implementation lane.
Runtime verification: NOT_RUN.

Protected SSH profile installation is source implemented with canonical-content
`.profile` references and transport preflight. Windows external SSH transport
projection remains unqualified; native `GLOBAL??` persistence does not authorize
rewriting a path into the ordinary drive namespace. Key/pin receipts preserve
observed publication and logical references when the dedicated validated
projection-unavailable result occurs; profile setup requires projection before
publication. Qualify this boundary with actual namespace-rebinding evidence
before enabling Windows external SSH paths.

## Minimal private store qualification

- Qualify the generic retained POSIX private-store writer anchored to validated
  directory ancestry and effective UID ownership; directory mode 0700, file
  mode 0600 before any private bytes. Reject links, unexpected ownership,
  untrusted writable ancestors, replacements and changed identity metadata.
- Qualify reuse of the Windows protected-root/private-file owner from
  `43d32352d40d5f3a72f218c63a26865354400f75`; use its ACL/security_current,
  create_private_stage, seal and publish_no_replace methods. Do not interpret
  Windows chmod success or POSIX mode bits as proof of private ACLs.
- Publish private key, public metadata and immutable trust binding with an
  explicit crash recovery/uncertainty contract. Preserve unresolved cleanup
  owners until close/discard is confirmed. Never overwrite an existing
  reference, follow a symlink, or accept private output in logs/config/replies.
- Map each shared `secret://` reference to exactly one identity/profile for
  Simple, Orchestrator and Caret, with separate `trust://` server-host-key pins.
  Atomically reject conflicting alias bindings. Shared reference equality is
  not evidence of possession, enrollment or server authorization.
- Qualify the existing pure Ed25519 implementation and the internal OpenSSH
  private wire codec against an independent OpenSSH implementation. Verify
  private seed/public consistency, none/none KDF fields, nkeys, checkints,
  length fields, Ed25519 64-byte seed-plus-public field and block padding.
  Current implementation invokes no key-generation subprocess and has no
  external child-pathname handoff. Never derive a private key from text/time.
- User text/current time should affect only sanitized naming metadata. Obtain
  all private entropy from the OS CSPRNG; do not accept plaintext passwords.
- Pin an explicitly supplied offline server SSH key after independent expected
  fingerprint comparison. Read existing pins through retained authority;
  changed keys hard fail, including concurrent publication conflicts. Rotation
  requires a separate explicit verified administrative operation.

## Later OS secret storage

- TODO: macOS Keychain binding with narrow application access and opaque refs.
- TODO: Windows DPAPI/key protection or suitable native key storage; preserve
  protected file/root ACLs and retain private material outside ordinary config.
- TODO: Linux Secret Service/libsecret or approved keyring integration with
  explicit locked/unavailable behavior. No plaintext fallback on unlock failure.
- TODO: avoid immutable entropy-hex and private-PEM text intermediates; add a
  checked OS byte-buffer entropy owner, locked storage and complete crypto
  intermediate cleanup with evidence. Current best-effort mutable buffer wipes
  do not prove complete RAM erasure or protection from swapping/core dumps.

## Administrative grant and executable gates

- Integrate an explicit administrative grant policy beyond the existing
  authenticated pending-public-registration gateway. Pending receipts never
  authorize login, prove possession of a newly uploaded key or claim enrollment.
  Require a separately verified server grant before reporting enrollment.
  Current SSH authentication proves the existing login key only; avoid a
  redundant invented application challenge protocol.
- Test no-replace races, path swaps, symlinks/reparse points, invalid owner/ACL,
  permissions before data, failed fsync/close/discard, output limits/timeouts,
  existing/changed pins, conflicting aliases and secret-free diagnostics.
- Run the identity unit spec with an independently admitted self-hosted runtime.
  Add actual POSIX and Windows private-store/provider evidence before claiming
  production qualification. An export-only response is not enrollment proof.
- Run exchange unit/system/provider acceptance with installed controller
  allowlists, independent expected fingerprints, correlated request receipts,
  exact idempotent pending records, changed-pin refusals and transport/store
  cleanup ownership. Qualify the actual authenticated SSH send/receive path;
  authored callback code is not successful live-exchange evidence.
