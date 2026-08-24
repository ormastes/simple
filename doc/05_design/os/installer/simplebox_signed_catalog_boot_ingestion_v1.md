# Simplebox signed catalog boot ingestion v1

The loader is the sole owner of catalog mutation. The hosted provisioner owns
safe-root reads and returns a bounded value result; that result is copied data,
not authority. `simplebox_signed_catalog_boot_ingest_provisioned_v1` validates
the provision status, safe-root path receipt, payload and signed-record hashes,
canonical SAM1 identity, and the exact one-payload/eight-alias Simplebox bundle.

After those pure checks, the adapter calls the existing loader-private boot
population transaction. That transaction installs the bounded trust-root set
once, performs Ed25519 verification for every record before opening a catalog
session, and either seals the complete catalog or quarantines an insertion or
seal failure. A provisioner boolean, digest, or receipt can never replace the
cryptographic verification receipt.

The loader-package hosted entry
`simplebox_signed_catalog_boot_ingest_from_safe_root_v1` performs the safe-root
provisioning and loader ingestion as one explicit call. It does not expose the
package-private catalog session or signature-verification receipt. Both
mutation-bearing ingestion functions are package-private, so copied
provisioning values and caller-selected roots cannot expose catalog mutation to
installer or application code. The public surface is a pure diagnostic shape
predicate only.

The v1 boundary accepts exactly one Simplebox payload record for one supported
SimpleOS target. Artifact bytes remain capped at 16 MiB by the provisioner;
receipt paths are relative and capped at 4095 bytes; all retained identities
are fixed SHA-256 strings. Work is linear in the canonical SAM1 size and adds
no unbounded queue, retry, or cross-domain mutable state.

Static specifications cover the value boundary, canonical safe-root path
rules, and substitution failures. Mutation-bearing behavior remains covered by
the existing boot-owner transaction contract rather than a public test hook.
Runtime verification was intentionally not run.
