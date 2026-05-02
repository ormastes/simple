# Feature: spostgre public trait surface
# Anchors: doc/05_design/spostgre_design.md §2.1 (modules), §5 (Storage API)
# Target: src/lib/nogc_sync_mut/spostgre_if/
# Status: pending — Phase 5 lands the skeleton that satisfies these.

Feature: spostgre_if trait contracts exist and match the design doc
  As a Phase 5 engineer
  I want the public trait surface for spostgre to be declared in src/lib/nogc_sync_mut/spostgre_if/
  So that downstream modules can depend on the contract before any impl lands

  Background:
    Given the design doc "doc/05_design/spostgre_design.md" §2.1 names the trait namespace as "spostgre_if"
    And   §5 enumerates the outer Storage-API boundary calls

  Scenario: Namespace is "spostgre_if" (the Phase 3 committed name)
    Given the architecture committed the trait-contract namespace in state §3-arch
    When  a Phase 5 engineer inspects the repo
    Then  the directory "src/lib/nogc_sync_mut/spostgre_if/" exists
    And   no sibling directory named "spostgre_traits" or "spostgre_api" is present

  Scenario: Public traits from design §2.1 are declared
    Given §2.1 lists traits: PageStore, WalWriter, BufferManager, PageMap, Vacuumer, Checkpointer, RelationOracle
    When  the skeleton lint runs "bin/simple build lint"
    Then  each trait above appears in some ".spl" file under "src/lib/nogc_sync_mut/spostgre_if/"
    And   each trait is exported (public) from its module

  Scenario: PageStore exposes the buf_* surface from §5
    Given §5 lists "buf_get(rel, page) -> PagePtr" and "buf_prefetch(rel, pages)"
    When  the PageStore trait is inspected
    Then  it declares a "buf_get" method returning a page pointer
    And   it declares a "buf_prefetch" hint method

  Scenario: WalWriter exposes wal_append and wal_group_commit from §5
    Given §5 lists "wal_append(record) -> Lsn" and "wal_group_commit(upto_lsn) -> Lsn"
    When  the WalWriter trait is inspected
    Then  it declares "wal_append" returning an Lsn
    And   it declares "wal_group_commit" returning an Lsn

  Scenario: PageMap exposes page_rewrite and pmap_publish from §5
    Given §5 lists "page_rewrite(rel, page, new_bytes) -> PageGeneration"
    And   §5 lists "pmap_publish(rel, root_bytes, expected_gen) -> Generation"
    When  the PageMap trait is inspected
    Then  "page_rewrite" is declared
    And   "pmap_publish" is declared with an expected-generation parameter

  Scenario: Checkpointer exposes checkpoint_begin and checkpoint_commit from §5
    Given §5 lists "checkpoint_begin() -> CheckpointGen" and "checkpoint_commit(gen) -> Result"
    When  the Checkpointer trait is inspected
    Then  both methods are declared
    And   checkpoint_commit takes the CheckpointGen returned by checkpoint_begin

  Scenario: Vacuumer exposes vacuum_range from §5
    Given §5 lists "vacuum_range(rel, lo..hi)"
    When  the Vacuumer trait is inspected
    Then  it declares a "vacuum_range" method over a page range

  Scenario: Inner helpers from §5 are NOT exposed on the outer traits
    Given §5 marks "compute_page_crc", "mvcc_visible", "brin_range_covers", "line_pointer_parse" as "inner"
    When  the public spostgre_if traits are inspected
    Then  none of these inner helpers appear on any public trait method
    And   they remain private to the ECS business layer in "examples/spostgre/"

  Scenario: Shared types re-export from src/lib/nogc_sync_mut/storage/
    Given §2.1 places shared types (Generation, SealToken, PublishResult, Durability, StorageClass) in "src/lib/nogc_sync_mut/storage/"
    When  spostgre_if modules are inspected
    Then  they import these types from "std.nogc_sync_mut.storage" (or the namespaced equivalent)
    And   they do not redefine them locally
