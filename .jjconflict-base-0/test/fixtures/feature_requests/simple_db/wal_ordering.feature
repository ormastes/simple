# Feature: WAL-before-pmap-publish ordering invariants
# Anchors: doc/05_design/spostgre_design.md §3.2 (system ordering), §6.4 (durable-commit handshake),
#          §6.3 (group-commit formation), §6.5 (NVMe Flush / FUA)
# Target: examples/spostgre/src/business/ (sys_commit, sys_wal_flush, sys_checkpoint)
# Status: pending — scenarios encode contracts Phase 5+ impl must satisfy.
#         Step definitions stay empty here; impl lands in Phase 5, runtime checks in Phase 7.

Feature: sys_commit and sys_checkpoint honor WAL-before-pmap-publish ordering
  As a durability auditor
  I want the public boundaries sys_commit, sys_wal_flush, sys_checkpoint to flush WAL before making state visible or publishing pmap roots
  So that crash at any point leaves a recoverable state per §6.7

  Background:
    Given §3.2 states "Ordering: sys_wal_flush before sys_commit"
    And   §3.2 states sys_checkpoint issues "atomic_pointer_record_publish for pmap-root" only after sealing the active arena
    And   §6.4 states commit is NOT visible until the durable-LSN cursor crosses the Txn's commit LSN

  Scenario: sys_wal_flush runs before sys_commit within a tick
    Given a world tick scheduled by the ECS runner
    When  sys_wal_flush and sys_commit are both queued for the tick
    Then  sys_wal_flush executes first
    And   sys_commit observes only WAL records already pushed to NVFS

  Scenario: sys_commit does not promote COMMIT-PENDING to COMMITTED until durable LSN crosses commit LSN
    Given a transaction Txn in COMMIT-PENDING with commit_lsn = L
    And   the durable-LSN cursor reported by arena_group_commit is D < L
    When  sys_commit is invoked
    Then  Txn.status remains COMMIT-PENDING
    And   Txn.status transitions to COMMITTED only on a later tick where D >= L

  Scenario: Other transactions cannot see a committing Txn before its LSN is durable
    Given Txn_w is in COMMIT-PENDING with commit_lsn = L
    And   Txn_r is a reader started with a snapshot that would include Txn_w if visible
    When  the durable-LSN cursor has not yet reached L
    Then  Txn_r's visibility check for Txn_w's writes returns not-visible
    And   Txn_r sees Txn_w's writes only after the cursor crosses L

  Scenario: sys_checkpoint seals the active WAL arena before publishing pmap-root
    Given an active WAL arena with in-flight appends
    When  sys_checkpoint runs for generation G
    Then  arena_seal is called on the active WAL arena
    And   arena_seal is called on the active main arena
    And   atomic_pointer_record_publish for pmap-root is called with expected_gen = G-1
    And   the publish call comes strictly after both arena_seal calls complete

  Scenario: Group-commit boundary flushes before visibility changes (§6.3)
    Given a group-commit batch containing commits for transactions T1..Tn
    When  arena_group_commit returns durable LSN D covering all of T1..Tn
    Then  sys_commit awakens waiters only for Ti whose commit_lsn <= D
    And   no visibility flag is flipped for a Ti whose commit_lsn > D

  Scenario: Out-of-place page rewrite publishes pmap delta only after WAL
    Given a page rewrite triggered by an UPDATE
    When  the engine runs the "§9 out-of-place write pipeline"
    Then  the WAL record for the logical change appends to DB_WAL before the pmap delta
    And   the pmap root is not CAS'd until checkpoint time
    And   crash between WAL-append and pmap-publish is recovered by §6.7 redo replay

  Scenario: DURABLE_ON_RETURN commits map to arena_fua_append (§6.5, S7)
    Given a Txn committing with Durability = DURABLE_ON_RETURN
    When  sys_wal_flush picks up its WAL record
    Then  the NVFS call is "arena_fua_append" (preferred) or "arena_append + arena_flush" (fallback)
    And   sys_commit may not mark the Txn COMMITTED before that NVFS call returns Ok

  Scenario: DURABLE_GROUP_COMMIT commits coalesce without breaking ordering
    Given multiple Txns committing with Durability = DURABLE_GROUP_COMMIT
    When  sys_wal_flush coalesces them into one aligned append
    Then  their commit LSNs are all <= the durable LSN reported by arena_group_commit
    And   visibility flips occur in commit-LSN order, never before their LSN is durable
