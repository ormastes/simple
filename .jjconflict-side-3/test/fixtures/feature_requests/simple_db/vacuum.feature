# Feature: spostgre M5 vacuum
# Anchors: spostgre M5 milestone — reclaim dead tuple space, advance OldestXmin, update FSM
# Target: examples/spostgre/src/business/ (sys_vacuum, sys_vacuum_freeze)
# Status: pending — wave 8 impl must satisfy these contracts.

Feature: spostgre M5 vacuum reclaims dead tuples and advances the visibility horizon
  As a database maintenance engineer
  I want vacuum to reclaim space from dead tuples and advance OldestXmin
  So that table bloat is bounded and transaction ID wraparound is prevented

  Background:
    Given a relation R with 10 pages
    And   OldestXmin = 1000 (oldest active snapshot)
    And   page P2 contains 5 dead tuples with xmax < 1000 and 3 live tuples

  Scenario: Golden path — vacuum reclaims dead tuples and updates FSM
    Given no active transaction holds a snapshot older than xmax of the dead tuples
    When  sys_vacuum runs on relation R
    Then  the 5 dead slots on page P2 are marked free
    And   the Free Space Map (FSM) for R is updated to reflect the reclaimed bytes on P2
    And   the live tuples on P2 are unaffected
    And   a VacuumReport is emitted with dead_reclaimed = 5

  Scenario: Vacuum skips pages with no dead tuples
    Given page P1 contains only live tuples (no dead tuples)
    When  sys_vacuum runs on relation R
    Then  P1 is not rewritten
    And   the page LSN of P1 is unchanged after vacuum

  Scenario: Vacuum freeze advances FrozenXid for old tuples
    Given a tuple T in P2 with xmin = 500 (older than freeze_min_age threshold)
    When  sys_vacuum_freeze runs on relation R
    Then  T.xmin is replaced with FrozenTransactionId
    And   pg_class.relfrozenxid for R advances to at least 500
    And   a WAL record is emitted for the freeze operation

  Scenario: Vacuum respects active snapshots — does not reclaim visible tuples
    Given a tuple D with xmax = 950 and an active snapshot at xid = 900 (which sees D as live)
    When  sys_vacuum runs with OldestXmin = 1000
    Then  D is NOT reclaimed (900 < 1000, so D is still visible to the old snapshot)
    And   D remains in place until all snapshots older than xmax=950 have closed

  Scenario: Autovacuum trigger fires when dead tuple ratio exceeds threshold
    Given relation R has dead_tuple_fraction = 0.25 (above the 0.20 autovacuum threshold)
    When  the autovacuum scheduler tick fires
    Then  sys_vacuum is scheduled for relation R
    And   vacuum starts within the next scheduler tick
