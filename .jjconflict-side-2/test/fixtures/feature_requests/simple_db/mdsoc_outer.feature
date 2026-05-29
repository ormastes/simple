# Feature: spostgre MDSOC outer capsule — five axes
# Anchors: doc/05_design/spostgre_design.md §2.1..§2.5
# Target: src/lib/nogc_sync_mut/spostgre_if/ + examples/spostgre/
# Status: pending — Phase 5 skeleton must declare the axes so the lint can see them.

Feature: spostgre declares the five MDSOC outer axes as designed
  As an architecture auditor
  I want the five MDSOC axes to be visibly declared in the skeleton
  So that the MDSOC+ capsule boundary is lint-checkable, not just comment-only

  Background:
    Given spostgre is an MDSOC+ module (outer MDSOC wrapping inner ECS)
    And   design doc §2.1..§2.5 enumerate the five axes

  Scenario: Axis 1 — Modules (§2.1)
    Given §2.1 lists five namespaces: shared storage traits, spostgre_if, engine impl, ECS business layer, CLI
    When  the skeleton is inspected
    Then  "src/lib/nogc_sync_mut/storage/" exists (shared trait contracts)
    And   "src/lib/nogc_sync_mut/spostgre_if/" exists (spostgre public traits)
    And   "examples/spostgre/src/engine/" exists (implementation)
    And   "examples/spostgre/src/business/" exists (ECS business layer)
    And   "examples/spostgre/src/tool/" exists (CLI surface)

  Scenario: Axis 2 — Dependencies (§2.2)
    Given §2.2 allows dependencies toward "std.ecs" and "fs/nvfs" trait contracts
    And   §2.2 forbids direct dependencies on NVFS implementation modules
    When  the skeleton module graph is inspected
    Then  "spostgre_if" imports from "std.nogc_sync_mut.fs.nvfs" (trait contracts only)
    And   "spostgre_if" does not import from "examples/nvfs/src/"
    And   circular dependencies are absent

  Scenario: Axis 3 — Side effects (§2.3)
    Given §2.3 lists side-effecting ops as WAL append, pmap publish, arena append, arena seal, arena discard
    When  the skeleton module headers are inspected
    Then  each side-effecting trait method is documented as side-effecting
    And   pure inner helpers (compute_page_crc, mvcc_visible, brin_range_covers) are marked pure

  Scenario: Axis 4 — Capabilities (§2.4)
    Given §2.4 says spostgre requires capabilities: nvfs-client, storage-class META_DURABLE, DB_WAL, DB_TEMP, GENERAL_MUTABLE, CHECKPOINT_SNAPSHOT
    When  the skeleton manifest is inspected
    Then  the required capability set is declared (even if as a comment list for Phase 5)
    And   MODEL_IMMUTABLE is NOT claimed (that class is svllm-only per §2.4)

  Scenario: Axis 5 — Ownership (§2.5)
    Given §2.5 maps owner subsystems to component stores
    When  the ECS business layer is inspected
    Then  "BufferManager" owns "BufferFrame" components
    And   "WalWriter" owns "WalRecord" components
    And   "Checkpointer" owns "Checkpoint" components
    And   "Vacuumer" owns "SegmentSummary" components
    And   "PageMap" owns "PageMapEntry" components
    And   "RelationOracle" owns "Relation" components
    And   "TempManager" owns "TempSpill" components
    And   "BlobStore" owns "BlobRef" components
    And   no subsystem mutates a component store it does not own
