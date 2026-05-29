# Feature: spostgre ECS business layer — 11 POD components
# Anchor: doc/05_design/spostgre_design.md §3.1
# Target: examples/spostgre/src/business/components.spl
# Status: pending — Phase 5 creates the POD structs.

Feature: The 11 ECS components from §3.1 are declared as POD structs
  As an ECS reviewer
  I want the 11 components named in §3.1 to exist as POD structs in examples/spostgre/src/business/components.spl
  So that systems (§3.2) can be wired to ComponentStore<T> without inventing new component names

  Background:
    Given §3.1 enumerates exactly 11 components
    And   all components are POD (no pointers, no GC references)
    And   layout is preserved by "std.ecs.ComponentStore<T>"

  Scenario: File location
    Given the ECS business layer lives under "examples/spostgre/src/business/"
    When  the component definitions are inspected
    Then  they appear in "examples/spostgre/src/business/components.spl"

  Scenario: Relation component is declared
    Given §3.1 defines Relation with fields oid, namespace_oid, relkind, main_arena_id, pmap_root_slot
    When  the component file is inspected
    Then  struct "Relation" is declared
    And   it contains an "oid: u64" field
    And   it contains an "main_arena_id: ArenaId" field

  Scenario: PageDescriptor component is declared
    Given §3.1 defines PageDescriptor with rel_oid among its fields
    When  the component file is inspected
    Then  struct "PageDescriptor" is declared as POD
    And   it contains a "rel_oid: u64" field

  Scenario: Tuple component is declared
    Given §3.1 defines Tuple with rel_oid and MVCC fields
    When  the component file is inspected
    Then  struct "Tuple" is declared as POD

  Scenario: WalRecord component is declared
    Given §3.1 defines WalRecord with lsn as the monotonic key
    When  the component file is inspected
    Then  struct "WalRecord" is declared
    And   it contains an "lsn: u64" field

  Scenario: Txn component is declared
    Given §3.1 defines Txn with xid as the transaction ID
    When  the component file is inspected
    Then  struct "Txn" is declared
    And   it contains an "xid: u64" field

  Scenario: Checkpoint component is declared
    Given §3.1 defines Checkpoint with gen as the generation field
    When  the component file is inspected
    Then  struct "Checkpoint" is declared
    And   it contains a "gen: Generation" field

  Scenario: BufferFrame component is declared
    Given §3.1 defines BufferFrame with frame_id as the pool slot
    When  the component file is inspected
    Then  struct "BufferFrame" is declared
    And   it contains a "frame_id: u32" field

  Scenario: PageMapEntry component is declared
    Given §3.1 defines PageMapEntry with rel_oid as the owning relation
    When  the component file is inspected
    Then  struct "PageMapEntry" is declared
    And   it contains a "rel_oid: u64" field

  Scenario: SegmentSummary component is declared
    Given §3.1 defines SegmentSummary with arena_id as the tracked arena
    When  the component file is inspected
    Then  struct "SegmentSummary" is declared
    And   it contains an "arena_id: ArenaId" field

  Scenario: TempSpill component is declared
    Given §3.1 defines TempSpill with spill_id as the session-local ID
    When  the component file is inspected
    Then  struct "TempSpill" is declared
    And   it contains a "spill_id: u64" field

  Scenario: BlobRef component is declared
    Given §3.1 defines BlobRef with blob_oid as the blob object ID
    When  the component file is inspected
    Then  struct "BlobRef" is declared
    And   it contains a "blob_oid: u64" field

  Scenario: No extra components are declared
    Given §3.1 enumerates exactly 11 components
    When  the component file is inspected
    Then  the count of public POD component structs equals 11
    And   every struct is POD (no heap pointers, no GC-traced fields)
