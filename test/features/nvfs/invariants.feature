# Status: pending — property-test shape, runtime hook lands with the
# QuickCheck-style state generator (see research doc §4.4).
#
# Anchors:
# - Formal model: verification/formal/nvfs/Nvfs/Invariants.lean (I1..I10)
# - Preservation theorems: verification/formal/nvfs/Nvfs/Theorems.lean
# - Research: doc/01_research/nvfs_formal_verification.md
#
# Each scenario below is a *property*, not a fixture.  The NVFS language
# runner is expected to generate a valid `FsState` (one reachable from
# `FsState.empty` by a bounded sequence of legal ops), apply an
# arbitrary further sequence of legal ops, and assert the invariant
# holds on the resulting state.

Feature: NVFS state-integrity invariants hold after any legal op sequence
  As an NVFS integrator
  I want the ten core invariants (I1..I10) to hold on every reachable state
  So that no sequence of valid operations can produce a corrupt filesystem

  Background:
    Given an NVFS state "s" reachable from "FsState.empty" by a legal op sequence
    And   an arbitrary further legal op sequence "ops" of length 0..64
    When  "ops" is applied to "s" producing "s'"

  Scenario: I1 — pmap entries always point at non-discarded arenas
    Then  every pmap entry in "s'" references an arena that is present and not discarded

  Scenario: I2 — sealed arenas reject appends
    Then  no arena in "s'" that has "sealed = true" and "refcount > 0" is also "discarded = true"
    And   any attempt to arena_append to a sealed arena in "s'" returns "FsError.alreadySealed"

  Scenario: I3 — refcount consistency
    Then  for every arena "ar" in "s'", "arenaPmapRefs(s', ar.id) + arenaSnapRefs(s', ar.id) <= ar.refcount"
    And   any arena in "s'" with "discarded = true" has "refcount = 0"

  Scenario: I4 — WAL LSN strictly monotone
    Then  for every pair of consecutive WAL records "r_i" and "r_{i+1}" in "s'.wal", "r_i.lsn < r_{i+1}.lsn"
    And   "s'.durableLsn" never decreases across the op sequence

  Scenario: I5 — WAL durable before pmap publish
    Then  for every pmap entry "e" in "s'", there exists a WAL record "r" with "r.op = pmapPublish", "r.birthGen = e.birthGen", and "r.lsn <= s'.durableLsn"

  Scenario: I6 — at least one superblock replica is valid
    Then  "s'.superblock.replicaA.validChecksum = true" or "s'.superblock.replicaB.validChecksum = true"

  Scenario: I7 — active checkpoint roots point at live arenas
    Then  for the active checkpoint root "r" of "s'", "inodeRoot", "extentRoot" and "allocRoot" all reference live arenas

  Scenario: I8 — extent mapping injective modulo sharing
    Then  for any two pmap entries "e1" and "e2" in "s'" with "e1.logical != e2.logical", "e1.phys != e2.phys" or "e1.offset != e2.offset" or both entries have "shared = true"

  Scenario: I9 — reflinks match refcount
    Then  for every arena "ar" in "s'", "arenaPmapRefs(s', ar.id) <= ar.refcount"

  Scenario: I10 — snapshot-pinned arenas are not discarded
    Then  for every snapshot "sn" in "s'" and every pinned arena id "a" in "sn.pinned", the arena with "id = a" (if present) has "discarded = false"

  Scenario: Aggregate — AllInvariantsBool holds
    Then  "AllInvariantsBool(s') = true"
