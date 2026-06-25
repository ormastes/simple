# Feature: NVFS scrub detect+repair (N4a) and proactive scrub scheduler (N4b)
# Anchors: N4a (scrub scan + silent-corruption detect/repair),
#          N4b (background scheduler with configurable interval)
# Target: src/lib/nogc_sync_mut/fs/nvfs/scrub.spl
# Status: pending — wave 7 impl must satisfy these contracts.

Feature: NVFS scrub detects silent corruption and repairs via redundant copy
  As a storage reliability engineer
  I want on-demand and scheduled scrub operations
  So that bit-rot and media errors are detected and repaired before data loss occurs

  Background:
    Given an NVFS instance with MirroredStandard storage class providing two copies
    And   a sealed arena A containing 4 MiB of blocks with known-good checksums

  Scenario: Golden path — scrub on clean arena reports zero errors (N4a)
    Given all blocks in arena A pass their stored checksums
    When  I call "nvfs_scrub(arena: A)"
    Then  the call returns Ok(ScrubReport { corrupt: 0, repaired: 0 })
    And   no blocks are rewritten

  Scenario: Scrub detects and repairs a single corrupted block (N4a)
    Given block at Offset 1MiB in arena A has been silently corrupted on copy 1
    And   copy 2 at the same Offset retains the correct data
    When  I call "nvfs_scrub(arena: A)"
    Then  the report contains corrupt = 1 and repaired = 1
    And   a subsequent arena_read of Offset 1MiB returns the correct data
    And   copy 1 at Offset 1MiB now matches copy 2

  Scenario: Scrub with unrecoverable corruption (both copies bad) returns RepairFailed (N4a)
    Given block at Offset 2MiB has been corrupted on both copy 1 and copy 2
    When  I call "nvfs_scrub(arena: A)"
    Then  the report contains corrupt = 1 and repaired = 0
    And   the error list includes FsErr::RepairFailed for Offset 2MiB
    And   a subsequent arena_read of Offset 2MiB returns Err(FsErr::Unrecoverable)

  Scenario: Proactive scrub scheduler triggers at configured interval (N4b)
    Given the NVFS scrub scheduler is configured with interval = 24h
    And   the system clock advances by 25 hours
    When  the scheduler tick fires
    Then  nvfs_scrub is called automatically on all arenas that have not been scrubbed within 24h
    And   ScrubReport events are emitted to the NVFS event log

  Scenario: Scrub scheduler respects priority — active IO is not starved (N4b)
    Given the scrub scheduler is running and arena A is being scrubbed
    And   a concurrent arena_append to arena B arrives
    When  the scheduler observes the IO pressure signal
    Then  the scrub of arena A is paused or rate-limited
    And   the arena_append to arena B completes within normal latency bounds
