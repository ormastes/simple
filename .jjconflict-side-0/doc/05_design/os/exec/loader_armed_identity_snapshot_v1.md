# Loader Armed Identity Snapshot V1

## Purpose

The executable-authority registry is the sole mutable owner of admitted image
tokens. A future SSH/filesystem joint-launch transition needs to compare its
request lease with that exact owner state without consuming the token, opening
the path again, or receiving a copy of the executable handle.

## Contract

`executable_authority_snapshot_armed_identity` is package-private to the loader.
Under the existing checked registry mutex it validates the owner epoch and the
complete `{slot, generation, nonce}` token, requires the slot to remain
`Armed`, and returns one owned identity record. The record contains the
token coordinate, canonical source path, SHA-256 image identity, admission ID,
role, exact target tuple, and an explicit optional entry-point identity.

Authenticated ELF admission binds `has_entry_identity=true` only after the
loader parser proves the entry lies in a verified executable range. Legacy
diagnostic admission binds `has_entry_identity=false` and entry zero. A joint
launch consumer must reject that missing identity; zero is never interpreted
as an entry point.

## Ownership and bounds

Canonical mutable state remains the single fixed-capacity loader registry.
The snapshot is a non-authorizing owned copy: it exposes no open file handle,
load ranges, image bytes, close lease, or state transition. Text is copied
while the mutex is held, with byte ceilings derived from the already-validated
handle contract: 16 KiB for the UTF-8 canonical path, 64 bytes for SHA-256, and
1 KiB for each identity/target field. This makes work independent of image size
and bounds the mutex critical section.

The operation is O(number of identity bytes), at most roughly 22 KiB, and uses
one bounded allocation per returned text. Slot lookup is O(1). It does not
consume, commit, retrieve, close, or otherwise mutate authority state.

## Deferred joint transition

This change deliberately does not wire SSHD. The future loader-owned joint
transition must validate both the SSH launch lease and this exact Armed
identity under their respective owners, reject `has_entry_identity=false`, and
linearize success or rollback without turning either copied record into
authority.
