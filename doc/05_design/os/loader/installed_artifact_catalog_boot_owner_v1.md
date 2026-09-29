# Installed-artifact catalog boot owner v1

This owner is the canonical transaction that turns authenticated image records
into the loader's sealed installed-artifact catalog. Authenticated boot policy
provides one exact SimpleOS target, its complete required canonical-path set,
and the trusted Ed25519 public keys. Each retained record supplies a bounded
manifest, digest, aliases, signature envelope, and expected trust-root digest.

The owner first rejects an empty, oversized, duplicate, cross-target, aliased,
or incomplete bundle. It initializes the existing loader trust capsule and
cryptographically verifies every manifest against its staged payload digest.
Only after all records pass does it begin the irreversible catalog session,
insert each record, and seal exactly once. There is no unsigned-receipt path,
verification boolean, fallback manifest, partial-success result, or public
catalog mutation API. Any unexpected insertion or seal failure after begin
consumes the session into permanent quarantine, so a partial catalog can never
be observed or retried.

The preflight is O(R² + A²), where R is capped at 17 and aliases are bounded by
the catalog at 8. Verification is O(total bounded manifest bytes plus Ed25519
work). All retained values are deep-copied by the catalog owner. This is a boot
path, not a request hot path.

Production population remains unavailable until the image builder emits signed
records for the required web, database, Simple interpreter/compiler/loader,
clang/LLVM, and primary-tool artifacts and authenticated boot policy transfers
the corresponding roots and exact required-path set. In particular, the
existing Simplebox installer receipt is unsigned and cannot satisfy this API.
