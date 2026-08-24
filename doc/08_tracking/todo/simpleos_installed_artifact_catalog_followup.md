# SimpleOS installed-artifact catalog follow-up

Status: blocked design audit; unsafe phase-1 draft reverted after the required
independent static re-review failed. No catalog or launch integration landed.

## Implemented prerequisite primitive (pending commit)

The common `SimpleArtifactManifest` owner now defines fixed collection,
element, aggregate-value, and canonical-body ceilings; bounded nested-array
deep copy; and a signature-free, domain-separated canonical byte projection.
This resolves only the input-shape and allocation prerequisite. The catalog
lifecycle and launch transaction below remain unimplemented and blocked on
their own owner/security review.

## Phase-1 blockers

The catalog must resolve these issues together before implementation is safe:

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

After those blockers are resolved, the bounded catalog will store immutable
signed metadata but still will not be execution authority. Remaining launch
work must be completed as one owner transaction:

1. populate and seal the catalog from authenticated boot/package metadata;
2. acquire and hash a stable MountTable snapshot of the canonical file;
3. compare the catalog digest and promote the same open handle without reopen;
4. cryptographically verify manifest/admission proof and mint a one-shot loader token;
5. let Scheduler consume the token, publish the task, and produce execution evidence;
6. retain the existing generic path-only fail-closed gates throughout.

Do not treat the installer receipt, catalog lookup result, pathname, caller ID,
or digest string as authority. Do not silently replace shell builtins with
filesystem aliases; explicit `/bin/...` launch remains a separate later policy.
