# Feature: spostgre M4 tier cache
# Anchors: spostgre M4 milestone — buffer pool tiering (hot/warm/cold) backed by NVFS arenas
# Target: examples/spostgre/src/business/ (sys_buffer_tier, BufferPool ECS component)
# Status: pending — wave 8 impl must satisfy these contracts.

Feature: spostgre M4 tier cache promotes hot pages and demotes cold pages
  As a buffer pool engineer
  I want hot pages kept in the L1 (RAM) tier and cold pages demoted to L2 (NVFS) tier
  So that working-set fits in RAM and cold data uses cheaper persistent storage

  Background:
    Given a BufferPool configured with L1 capacity = 256 pages, L2 capacity = 4096 pages
    And   a relation R with 1000 pages loaded in a mix of L1 and L2

  Scenario: Golden path — page read promotes L2 page to L1
    Given page P is in L2 (NVFS tier) with access_count = 0
    When  a transaction reads page P
    Then  P is loaded into L1 RAM
    And   P's tier label transitions from L2 to L1
    And   the access_count for P increments by 1

  Scenario: L1 eviction demotes cold page to L2 when L1 is full
    Given L1 is at capacity (256 pages)
    And   page Q in L1 has the lowest access_count (cold page)
    When  a new page is promoted into L1
    Then  Q is written back to L2 if dirty, or simply unmapped if clean
    And   Q's tier label transitions from L1 to L2
    And   the total L1 occupancy remains <= 256 pages

  Scenario: Dirty page demotion flushes data to NVFS arena before eviction
    Given page Q in L1 is dirty (modified but not checkpointed)
    When  Q is selected for demotion to L2
    Then  Q's modified bytes are written to the NVFS arena via arena_append
    And   Q is marked clean before its L1 slot is released
    And   a subsequent read of Q from L2 returns the correct modified data

  Scenario: L2 overflow triggers eviction to reclaim space
    Given L2 is at capacity (4096 pages)
    When  a demotion from L1 tries to place a page into L2
    Then  the cold-most page in L2 is discarded (if clean) or flushed to checkpoint
    And   the demoted page occupies the freed L2 slot

  Scenario: Tier statistics are exposed via sys_buffer_tier_stats
    Given the tier cache has processed at least 100 read operations
    When  I call "sys_buffer_tier_stats()"
    Then  the result contains l1_hits, l2_hits, l1_misses, demotions, promotions
    And   l1_hits + l2_hits + l1_misses equals the total page read count
