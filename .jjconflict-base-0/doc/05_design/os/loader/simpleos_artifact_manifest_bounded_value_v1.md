# Bounded SimpleOS artifact-manifest value contract v1

## Scope

The common executable-manifest owner now supplies dependency-free safety
primitives for a future installed-artifact catalog. This change does not add a
catalog, installer, cryptographic trust decision, handle lifecycle, or launcher
wiring.

## Ownership and bounds

- The caller owns its submitted manifest. A successful bounded copy owns fresh
  outer and nested arrays; text and scalar values are immutable value data.
- Every collection is capped at 64 entries and all collections together at 256
  entries. Every text value is capped at 4096 UTF-8 bytes and retained text at
  65536 bytes total.
- A conservative canonical-body bound is checked before allocating the body;
  the emitted body is additionally limited to 131072 bytes.
- Canonical bytes use a domain tag and length-prefixed fields, include every
  manifest field except the detached signature, and preserve declared array
  order. A fresh byte array is returned on every request.

## Complexity

Validation, deep copy, and canonical construction are each O(total manifest
bytes plus items). All temporary and retained allocations are bounded. The
byte writer appends in one pass and hoists each field's UTF-8 conversion so a
field is not converted twice.

## Deferred authority

These values are hash input only. They do not prove installation, identity,
trust, file contents, or permission to execute. A future package-private
catalog owner must still validate and retain them, verify a boot-installed
signer, bind a stable filesystem snapshot, and mint a one-shot loader token.
