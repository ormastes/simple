# Feature: spostgre real HOT slack (FR-HOT-001)
# Anchors: FR-HOT-001 — Heap-Only Tuple update reusing slack space within the same page
# Target: examples/spostgre/src/business/ (sys_hot_update, page layout)
# Status: pending — wave 7 impl must satisfy these contracts.

Feature: spostgre HOT update reuses in-page slack without new index entries
  As a database performance engineer
  I want UPDATE of a non-indexed column to reuse slack space in the same heap page
  So that index bloat is avoided and WAL volume is reduced per FR-HOT-001

  Background:
    Given a spostgre relation R with a B-tree index on column "id" only
    And   a page P in R with 40% free slack space
    And   a tuple T in P with id=42, value="short"

  Scenario: Golden path — HOT update fits in slack, no new index entry (FR-HOT-001)
    Given the updated value "longer_value" fits within the slack of page P
    When  I UPDATE R SET value='longer_value' WHERE id=42
    Then  the new tuple version T' is written into page P at a fresh slot
    And   T.t_infomask carries the HEAP_HOT_UPDATED flag
    And   T'.t_infomask carries the HEAP_ONLY_TUPLE flag
    And   no new index entry is inserted for id=42
    And   a single WAL record is emitted covering the page delta only

  Scenario: HOT chain is followed during index scan
    Given a HOT chain T -> T' on page P for id=42
    When  an index scan on "id=42" resolves the index pointer to T
    Then  the visibility traversal follows the HOT chain to T'
    And   T' is returned as the live tuple if it is visible to the snapshot

  Scenario: Non-HOT fallback when slack is exhausted
    Given page P has 0 bytes of free slack
    When  I UPDATE R SET value='any_value' WHERE id=42
    Then  the new tuple version T' is written to a different page P2
    And   a new index entry for id=42 pointing to T' is inserted into the B-tree
    And   T does NOT carry the HEAP_HOT_UPDATED flag

  Scenario: HOT update on an indexed column falls back to non-HOT
    Given the relation R also has a B-tree index on column "value"
    When  I UPDATE R SET value='new_indexed_value' WHERE id=42
    Then  the update is NOT treated as HOT
    And   a new index entry for value='new_indexed_value' is inserted

  Scenario: VACUUM reclaims dead HOT chain slots
    Given a HOT chain T -> T' where T is dead (older than all active snapshots)
    When  sys_vacuum runs on page P
    Then  slot T is marked as free and its space is returned to the page slack
    And   the index pointer for id=42 is updated to reference T' directly
