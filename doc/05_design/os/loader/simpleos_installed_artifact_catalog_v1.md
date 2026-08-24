# SimpleOS installed-artifact catalog v1

## Scope and authority boundary

`InstalledArtifactCatalogOwnerV1` is the sole mutable owner. The execution
domain is the checked raw-mutex critical section. Bootstrap submits scoped
manifest/alias loans; the owner validates and deep-copies them before commit.
Public lookup returns a fresh bounded copy. Neither a record, lookup result,
path, digest, signature, nor catalog status is loader or scheduler authority.

The population session and all lifecycle mutations are `pub(package)` within
`os.kernel.loader`. Public callers cannot construct a session, consume one of
the 16 permanent slots, seal the owner, or reset it. The lifecycle is one-way:

`Uninitialized -> Populating -> Sealed`, with any indeterminate serialization
or integrity failure transitioning permanently to `Quarantined`.

## Retained records

The owner retains at most 16 records and at most 8 aliases per record. Paths
are canonical absolute paths capped at 4096 UTF-8 bytes. Every record retains:

- the canonical path and exact aliases;
- the exact OS/architecture/ABI target;
- a nonzero lowercase SHA-256 content digest also declared by the manifest;
- signature scheme, signer identity, detached signature, and a signature-free
  canonical manifest digest;
- a fully bounded, deeply owned `SimpleArtifactManifest`.

Canonical paths and aliases share one 256-slot open-addressed collision domain.
At most 144 keys can be retained, keeping load below 57%. Duplicate or
ambiguous names fail before mutation. Sealing requires at least one record and
destroys the bootstrap nonce. No deletion or slot reuse exists in v1.

## Integrity and synchronization

Installation builds the bounded manifest identity and whole-record integrity
digest before taking the owner mutex. Lookup copies only the matched bounded
record under the mutex, releases serialization, recomputes integrity outside
the hot critical section, then reacquires the mutex to confirm the sealed slot
generation and cached digest. A mismatch quarantines the entire owner.

The raw-mutex contract used by existing kernel owners reports unlock failure
only while ownership remains retained. Therefore an unlock failure after a
mutation is committed-unknown: the owner publishes `Quarantined` while still
serialized, suppresses the result, and never offers retry. Quarantine is read
only after acquiring the same mutex, avoiding an unsynchronized pre-lock read.

## Complexity and memory

Bootstrap insertion and lookup use bounded open addressing. A cached path hash
avoids text equality for ordinary nonmatching probes: expected O(path bytes),
with the honest adversarial bound O(256 × path bytes) if every occupied key has
the same 64-bit hash. Copying and integrity work are O(one manifest's bytes),
with hashing outside the mutex on lookup. All counts and retained values have
fixed ceilings; no public request can cause persistent growth.

## Deferred work

The bootstrap owner is not yet wired to authenticated package metadata. There
is intentionally no snapshot acquisition, cryptographic signature decision,
loader token minting, scheduler admission, or launch alias policy in this
module. Those remain a later transaction and must not consume a catalog lookup
as authority.
