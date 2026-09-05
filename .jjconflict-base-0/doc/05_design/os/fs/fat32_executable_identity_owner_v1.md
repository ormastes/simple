# FAT32 executable object identity owner v1

Status: implemented as a static prerequisite; unverified by explicit user direction.

## Boundary and owner

`Fat32ExecutableIdentityOwnerV1` is the sole mutable owner. It has 16 mount
slots and 128 object slots behind one mutex. A mount is admitted from a device
identity, FAT volume serial, and root cluster; the owner assigns the mount
generation and opaque nonce. Callers retain only a seal.

The FAT backend supplies an exact 32-byte live directory entry and the already
validated raw UTF-16 LFN code units, including well-formed surrogate pairs.
The owner derives the first cluster, size,
8.3 checksum, short-name hash, exact/folded long-name hash, locator, and a
non-wrapping object generation. The returned snapshot receipt is copyable and
proves only the owner's state at the call's linearization point. It is neither
a lease nor an authority, and `fat32_executable_identity_snapshot_current_v1`
must not be used as a check-before-open or check-before-dispatch gate.

## Alias and replacement policy

- The padded 11-byte 8.3 field is backend-canonical and compared by hash.
- A second folded `NAME.EXT` hash places 8.3 and ASCII LFN spellings in the
  same lookup domain, closing cross-class aliases in both directions.
- ASCII LFNs are hashed after case folding; aliases at distinct locators are
  rejected.
- Non-ASCII LFNs retain their exact UTF-16 identity. They may be consumed only
  from a backend-resolved locator; v1 makes no Unicode case-folded path claim.
- A changed dirent or LFN at the same locator increments the generation and
  nonce, making every earlier receipt non-current.
- Deletion explicitly forgets the locator. Unmount invalidates all receipts for
  that mount. Generation exhaustion retires a slot instead of wrapping.
- Hash collision is treated as alias ambiguity and rejected. State and memory
  remain fixed-size; admission and snapshot lookup are O(128) and O(1),
  respectively, after bounded name hashing.

## Safe integration boundary

This module deliberately does not enable FAT32 in
`clang_filesystem_pipeline_owner_v1`. The current FAT reader decodes non-ASCII
LFN units lossily and does not validate the complete LFN sequence/checksum.
The safe next integration is a FAT-backend adapter that extracts and validates
the raw LFN chain, acquires identities for every existing path component, and
reserves absent output leaves against a proved parent-directory generation.
That adapter must share the FAT mutation serialization domain through handle
acquisition; a point-in-time owner check followed by an unlocked open is
explicitly insufficient.
Until that adapter exists, filesystem Clang launch continues to reject FAT32.
