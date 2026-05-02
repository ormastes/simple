# Feature: NVFS arena_* API surface
# Anchors: doc/05_design/nvfs_design.md §4.1 (core signatures), §4.2 (capability/publish/buffer),
#          §4.3 (contract details)
# Target: src/lib/nogc_sync_mut/fs/nvfs/api.spl
# Status: pending — Phase 5 lands trait declarations matching these signatures.

Feature: NVFS arena_* trait surface exists and matches §4.1 / §4.2
  As a Phase 5 engineer
  I want the arena_* trait signatures in src/lib/nogc_sync_mut/fs/nvfs/api.spl
  So that spostgre and svllm can depend on the NVFS contract before impl lands

  Background:
    Given §4.1 enumerates 11 core signatures and query helpers
    And   §4.2 enumerates 5 capability / publish / buffer signatures

  Scenario: File location
    Given the NVFS trait contracts live in "src/lib/nogc_sync_mut/fs/nvfs/"
    When  the skeleton is inspected
    Then  "src/lib/nogc_sync_mut/fs/nvfs/api.spl" exists and is non-empty
    And   it is imported by "spostgre_if" modules that need NVFS types

  Scenario: arena_create is declared per §4.1
    Given §4.1 gives "fn arena_create(class: StorageClass, hint: ArenaHint) -> Result<ArenaId, FsErr>"
    When  the api.spl file is inspected
    Then  "arena_create" is declared
    And   it takes parameters named "class" of type StorageClass and "hint" of type ArenaHint
    And   it returns a Result of ArenaId and FsErr

  Scenario: arena_append is declared per §4.1
    Given §4.1 gives "fn arena_append(arena: ArenaId, bytes: Slice<u8>, durability: Durability) -> Result<Offset, FsErr>"
    When  the api.spl file is inspected
    Then  "arena_append" is declared with exactly those three parameters
    And   the return type is Result<Offset, FsErr>

  Scenario: arena_append_aligned is declared per §4.1
    Given §4.1 gives "fn arena_append_aligned(arena, bytes, granule: u32, durability) -> Result<Offset, FsErr>"
    When  the api.spl file is inspected
    Then  "arena_append_aligned" is declared
    And   a "granule: u32" parameter is present between "bytes" and "durability"

  Scenario: arena_group_commit is declared per §4.1
    Given §4.1 gives "fn arena_group_commit(arena: ArenaId) -> Result<Offset, FsErr>"
    When  the api.spl file is inspected
    Then  "arena_group_commit" is declared
    And   its doc states it waits for in-flight durable writes

  Scenario: arena_read and arena_readv are declared per §4.1
    Given §4.1 gives "fn arena_read(arena, off: Offset, buf: Slice<u8>) -> Result<u64, FsErr>"
    And   §4.1 gives "fn arena_readv(arena, iov: Slice<ReadReq>) -> Result<(), FsErr>"
    When  the api.spl file is inspected
    Then  both "arena_read" and "arena_readv" are declared with the signatures above

  Scenario: arena_seal is declared per §4.1
    Given §4.1 gives "fn arena_seal(arena: ArenaId) -> Result<SealToken, FsErr>"
    When  the api.spl file is inspected
    Then  "arena_seal" is declared and returns a SealToken
    And   §4.3 requires the operation be idempotent

  Scenario: arena_discard is declared with generation pinning per §4.1 and §4.3
    Given §4.1 gives "fn arena_discard(arena, keep_gen_above: Generation) -> Result<(), FsErr>"
    When  the api.spl file is inspected
    Then  "arena_discard" is declared with a "keep_gen_above: Generation" parameter
    And   §4.3's "DiscardBlocked" failure mode is reflected in FsErr variants

  Scenario: arena_clone_range is declared per §4.1
    Given §4.1 gives "fn arena_clone_range(src, src_off, dst, dst_off, len: u64) -> Result<(), FsErr>"
    When  the api.spl file is inspected
    Then  "arena_clone_range" is declared with exactly those five parameters

  Scenario: arena_preferred_granule and arena_set_hint query helpers exist
    Given §4.1 gives "fn arena_preferred_granule(arena) -> u32"
    And   §4.1 gives "fn arena_set_hint(arena, hint: ArenaHint) -> Result<(), FsErr>"
    When  the api.spl file is inspected
    Then  both helpers are declared

  Scenario: Capability / publish / buffer signatures from §4.2 are declared
    Given §4.2 gives "fs_caps", "fs_register_buffer", "fs_unregister_buffer", "atomic_pointer_record_publish", "atomic_pointer_record_read"
    When  the api.spl file is inspected
    Then  all five functions are declared with the signatures in §4.2

  Scenario: Shared types come from src/lib/nogc_sync_mut/storage/
    Given §2.1 places Generation, SealToken, PublishResult in "src/lib/nogc_sync_mut/storage/"
    When  api.spl is inspected
    Then  these types are imported from the shared storage module
    And   they are not redefined locally inside fs/nvfs/
