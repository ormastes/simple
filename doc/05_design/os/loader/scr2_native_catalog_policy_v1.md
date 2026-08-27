# SCR2 Native Catalog Policy v1 — Detail Design

The codec has two canonical layers:

1. `SNC2`: policy identity, delegated SCR2 key and digest, then 1–64 exact
   native records.
2. `SNE2`: `SNC2` bytes, boot signer key ID, detached 64-byte Ed25519
   signature, and expected boot-root SHA-256.

Rows are bounded to 64 collections/items and 4 KiB text values. Decode always
re-encodes and byte-compares to prevent alternate encodings. The codec is
crypto-free except for hash spelling checks; the loader owner verifies both
root and delegated-key SHA-256 bindings.

Package-private owner plumbing receives catalog bytes, SCR2 bytes, an
independently pinned root, and a private architecture-fixed target. Public
architecture adapters derive that root only from compiled pins. It validates root identity, verifies
the SNE2 signature, decodes SCR2, selects a unique row, compares all
row-controlled receipt identity fields, and verifies SCR2 against a singleton
trust policy. It returns either a typed failure or an immutable projection
containing the receipt and full catalog template. Image builder and boot loader
integration are intentionally outside this version.
