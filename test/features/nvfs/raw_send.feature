# Feature: NVFS raw send/receive (N6b)
# Anchors: N6b — zero-copy raw block transfer between arenas or to external socket
# Target: src/lib/nogc_sync_mut/fs/nvfs/raw_send.spl
# Status: pending — wave 7 impl must satisfy these contracts.

Feature: NVFS raw send and receive for zero-copy block transfer
  As a replication engineer
  I want to send raw arena blocks to a remote peer and receive them into a local arena
  So that cross-node replication bypasses user-space copy overhead per N6b

  Background:
    Given an NVFS instance with at least 64 MiB available
    And   a sealed source arena SRC containing 1 MiB of data blocks

  Scenario: Golden path — raw_send produces a valid byte stream (N6b)
    Given arena SRC sealed at generation G
    When  I call "arena_raw_send(arena: SRC, range: 0..1MiB)" into a byte sink
    Then  the sink receives exactly the raw block bytes including any encryption overhead
    And   the transfer completes with Ok(bytes_sent) where bytes_sent == on-disk size of SRC

  Scenario: raw_receive reconstructs arena contents
    Given a byte stream S produced by arena_raw_send from SRC
    When  I call "arena_raw_receive(stream: S, class: SRC.class)" into a new arena DST
    Then  arena_read of each Offset in DST returns the same plaintext as SRC
    And   DST is in Sealed state after the receive completes

  Scenario: raw_send on unsealed arena returns NotSealed error
    Given an arena LIVE that has not been sealed
    When  I call "arena_raw_send(arena: LIVE, range: 0..all)"
    Then  the call returns Err(FsErr::NotSealed)
    And   no bytes are written to the sink

  Scenario: Partial range send transfers only the requested window
    Given arena SRC containing blocks at offsets 0, 512KiB, and 1MiB
    When  I call "arena_raw_send(arena: SRC, range: 512KiB..1MiB)"
    Then  the sink receives only the bytes covering the 512KiB..1MiB window
    And   arena_raw_receive of that partial stream into DST yields correct data at the corresponding offsets

  Scenario: raw_receive detects corruption via block checksums
    Given a byte stream S with one block's checksum corrupted
    When  I call "arena_raw_receive(stream: S, class: Standard)"
    Then  the call returns Err(FsErr::ChecksumMismatch)
    And   DST is left in an incomplete/discarded state
