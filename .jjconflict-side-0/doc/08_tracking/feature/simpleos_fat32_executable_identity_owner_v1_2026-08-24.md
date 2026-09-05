# SimpleOS FAT32 executable identity owner v1

Status: prerequisite implemented; unverified by explicit user direction.

Implemented bounded, owner-issued FAT32 mount/object identity bookkeeping covering
8.3 aliases, ASCII case folding, exact raw UTF-16 long-name identity, stable
directory locator plus first-cluster generation, replacement/deletion
invalidation, mount teardown, and fail-closed counter exhaustion. Its receipt
is explicitly point-in-time evidence, not an unlocked launch authorization.

Not yet complete: the live FAT directory walker must validate LFN ordinal,
last-slot, checksum, padding, and UTF-16 rules and feed its raw chain into this
owner. Consumption must be atomic with FAT mutation serialization; an unlocked
check-before-open has a TOCTOU window. Output creation additionally needs an atomic absent-leaf reservation
bound to the parent directory generation. Therefore this change does not turn
on FAT32 in the Clang filesystem pipeline and makes no filesystem-launch claim.
