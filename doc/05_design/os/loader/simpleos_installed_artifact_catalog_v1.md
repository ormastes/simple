# SimpleOS installed-artifact catalog v1

## Scope and authority boundary

`InstalledArtifactCatalogOwnerV1` is the sole mutable owner. The execution
domain is the checked raw-mutex critical section. Bootstrap submits scoped
manifest/alias loans; the owner validates and deep-copies them before commit.
Public lookup returns a fresh bounded copy. Neither a record, lookup result,
path, digest, signature, nor catalog status is loader or scheduler authority.

The population session and all lifecycle mutations are `pub(package)` within
`os.kernel.loader`. Public callers cannot construct a session, consume one of
the 17 permanent slots per target, seal the owner, or reset it. The lifecycle is one-way:

`Uninitialized -> Populating -> Sealed`, with any indeterminate serialization
or integrity failure transitioning permanently to `Quarantined`.

## Retained records

The owner retains at most 17 records for each of the six canonical SimpleOS
targets (102 records total) and at most 64 aliases per record. The admitted target
tuples are `simpleos/simpleos` with architecture `x86_64`, `x86`, `aarch64`,
`arm`, `riscv64`, or `riscv32`. Paths
are canonical absolute paths capped at 4096 UTF-8 bytes. Every record retains:

- the canonical path and exact aliases;
- the exact OS/architecture/ABI target;
- a nonzero lowercase SHA-256 content digest also declared by the manifest;
- signature scheme, signer identity, detached signature, and a signature-free
  canonical manifest digest;
- a fully bounded, deeply owned `SimpleArtifactManifest`.

Canonical paths and aliases are keyed by the complete
`(path, os, architecture, ABI)` tuple in one 8192-slot open-addressed collision
domain. At most 6630 keys can be retained, keeping load below 81%. A duplicate
name for one target fails before mutation, while the same executable path may
soundly identify a distinct record for every target. Sealing requires at least
one record and destroys the bootstrap nonce. No deletion or slot reuse exists
in v1.

The target-bound package-private lookup is the canonical execution-facing API.
The original public path-only lookup remains for diagnostic compatibility, but
returns no record when a path or alias occurs in more than one target partition;
it never guesses a platform.

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

Bootstrap insertion and target-bound lookup use bounded open addressing. A
cached tuple hash avoids text equality for ordinary nonmatching probes: expected
O(path + target bytes), with the honest adversarial bound O(8192 × tuple bytes)
if every occupied key has the same 64-bit hash. The compatibility path-only
diagnostic scans at most 102 records and rejects a second match. Per-target
capacity admission scans at most 102 compact slots and occurs only during
bootstrap. Each admitted target tuple maps one-to-one to a compact integer tag
in the key table, avoiding three retained text fields per key; hashing does not
allocate a concatenated key. Copying and integrity work are O(one manifest's bytes), with
hashing outside the mutex on lookup. All counts and retained values have fixed
ceilings; no public request can cause persistent growth.

## Deferred work

The bootstrap owner is not yet wired to authenticated package metadata. There
is intentionally no snapshot acquisition, cryptographic signature decision,
loader token minting, scheduler admission, or launch alias policy in this
module. Those remain a later transaction and must not consume a catalog lookup
as authority.
