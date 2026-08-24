# SimpleOS installed-artifact catalog follow-up

Status: bounded catalog owner implemented as an unverified draft; authenticated
bootstrap population and launch integration remain deferred.

The staged Simplebox lane now exposes the fail-closed producer contract in
`src/os/installer/simplebox_catalog_record_contract_v1.spl`. The current
image-builder receipt is explicitly classified as insufficient because it has
no authenticated manifest, signer identity, trust-root binding, or detached
signature. Exact canonical path, eight aliases, target projection, digest, and
the loader signing codec are frozen for a future signed record; no catalog row
is fabricated and no launcher authority is introduced. The exact active
blocker is
`simplebox-installer-receipt-has-no-authenticated-manifest-signer-or-signature`.

## Implemented prerequisite primitive

The common `SimpleArtifactManifest` owner now defines fixed collection,
element, aggregate-value, and canonical-body ceilings; bounded nested-array
deep copy; and a signature-free, domain-separated canonical byte projection.
This resolved the input-shape and allocation prerequisite. The catalog
lifecycle is now implemented by the bounded owner below; authenticated
bootstrap wiring and the launch transaction remain unimplemented.

## Catalog lifecycle implemented in the current draft

- package-private, one-way bootstrap session and population surface;
- maximum 16 immutable records and 8 exact aliases per record, with one shared
  collision domain and no reuse;
- deep-owned bounded manifest/alias retention and deep-owned public lookup;
- exact target, nonzero lowercase content digest, signer, scheme, and detached
  signature metadata;
- cached manifest/record identities with bounded out-of-lock integrity
  recomputation and slot-generation confirmation;
- synchronized fail-stop quarantine for committed-unknown unlock failure;
- no loader, filesystem, namespace, or scheduler authority.

The focused loader-package spec covers the public bounded input gate, forged
and stale bootstrap sessions, the 16-record ceiling, one-way seal, and nested
caller/output copy isolation. The pure transition oracle documents the required
committed-unknown quarantine rule but is not raw-mutex serialization evidence.
Direct raw-mutex failure injection remains unavailable; no test or build was
run for this draft.

## Resolved phase-1 blockers

The catalog design resolves these issues together:

- Bound every manifest collection count, every contained text/byte value, and
  the total canonical signing-body size before hashing, copying, or retention.
  Lookup must not rebuild and deep-copy an attacker-sized signing body while
  holding a global mutex; cache a validated immutable identity projection or
  signing-body hash with explicitly bounded output copying.
- Keep construction and population behind a package-private bootstrap owner.
  Public callers must not allocate all permanent owner slots, forge predictable
  coordinates, or inject installed metadata. If a handle crosses a trust
  boundary it needs an unforgeable boot-secret nonce and explicit lifecycle.
- Define unlock failure as fail-stop committed-unknown state, not a retryable
  ordinary error after mutation may have committed. Quarantine state must be
  synchronized without pre-lock data races (atomic owner state or a documented
  mutex primitive whose unlock failure is fatal).
- Deep-own nested manifest arrays on installation and any exported projection,
  then cover caller-mutation isolation. Revalidate cached record integrity on
  lookup without unbounded work.
- Preserve bounded open addressing, exact canonical path/target keys, exact
  alias metadata, duplicate/target/unsigned/digest rejection, and one-way seal.

Required focused coverage includes oversized collection/element/total-body
rejection, bootstrap-owner privacy/exhaustion, forged/stale handles, copy
isolation, alias capacity, post-seal integrity, and fail-stop serialization.

The bounded catalog stores immutable signed metadata but still is not execution
authority. Remaining launch work must be completed as one owner transaction:

1. populate and seal the catalog from authenticated boot/package metadata;
2. acquire and hash a stable MountTable snapshot of the canonical file;
3. compare the catalog digest and promote the same open handle without reopen;
4. cryptographically verify manifest/admission proof and mint a one-shot loader token;
5. let Scheduler consume the token, publish the task, and produce execution evidence;
6. retain the existing generic path-only fail-closed gates throughout.

Do not treat the installer receipt, catalog lookup result, pathname, caller ID,
or digest string as authority. Do not silently replace shell builtins with
filesystem aliases; explicit `/bin/...` launch remains a separate later policy.
