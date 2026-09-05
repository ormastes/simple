# Simplebox pinned catalog image v1

The freestanding boot boundary owns the installed Simplebox payload bytes, its
SCR1 record bytes, their real media paths, the expected platform target, and
the ordered trusted signer set. Loader-package code deep-copies the bounded
bytes and roots with
`simplebox_pinned_catalog_image_create_v1`; no public constructor or catalog
mutation method exists.

SCR1 is decoded with exact envelope/version/reserved bytes, field and list
bounds, printable-ASCII text, and an exact end cursor. Its embedded SAM1 value
is decoded by the canonical common codec into a typed manifest. The reader
requires canonical SAM1 re-encoding, canonical SCR1 re-encoding, the embedded
SAM1 digest, its image hash, and the actual payload SHA-256 all to agree. Thus
boot never supplies a parallel manifest projection that could disagree with
the signed bytes.

After pure decoding and binding, the provider creates the existing one-record,
eight-alias Simplebox plan and feeds
`simplebox_signed_catalog_boot_ingest_provisioned_v1`. That loader-private
bridge initializes the retained roots, verifies Ed25519, and seals or
quarantines the installed-artifact catalog. The only public entry is a pure
shape diagnostic; it cannot initialize trust, open a catalog session, or mint
loader authority.

Payloads are capped at 16 MiB, SCR1 at 256 KiB, SAM1 at 128 KiB, roots at 16,
aliases and every SAM1 collection at 64, and total retained manifest values at
64 KiB. Parsing is linear in the bounded image and allocates one owned copy of
each pinned input plus one typed projection. There are no retries, filesystem
reads, environment reads, runtime shortcuts, or public mutation hooks.

Static specs cover canonical typed SAM1 recovery, exact-end rejection, payload
substitution, SCR1 trailing data, and duplicate signer identities. Runtime
verification was intentionally not run.
