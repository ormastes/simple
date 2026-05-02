# Feature: NVFS virtual storage classes (authoritative enum)
# Anchors: doc/05_design/nvfs_design.md §3.1 (class table), §3.2 (svllm taxonomy mapping)
# Target: src/lib/nogc_sync_mut/fs/nvfs/ (StorageClass enum declaration)
# Status: pending — Phase 5 lands the enum; svllm/spostgre consume it.

Feature: The six NVFS storage classes from §3.1 are declared as the authoritative enum
  As a fs-API consumer
  I want StorageClass to be a single enum with exactly 6 variants matching §3.1
  So that svllm's 7-name taxonomy aliases onto these via §3.2 without duplicating the enum

  Background:
    Given §3.1 defines 6 virtual storage classes
    And   §3.2 maps svllm's 7 names (tensor_pack, manifest, adapter, append_only, temp, kv_spill, mutable) onto the 6 classes
    And   design §3 is the single source of truth for this enum

  Scenario: StorageClass is declared in src/lib/nogc_sync_mut/fs/nvfs/ or shared storage crate
    Given the skeleton compiles
    When  the NVFS trait module is inspected
    Then  "StorageClass" is declared exactly once in the workspace
    And   it is exported publicly from "src/lib/nogc_sync_mut/fs/nvfs/" (or re-exported via "src/lib/nogc_sync_mut/storage/")

  Scenario: META_DURABLE variant exists
    Given §3.1 row 1 names META_DURABLE for superblock, manifests, pmap roots, catalogs
    When  the StorageClass enum is inspected
    Then  variant "META_DURABLE" is declared

  Scenario: DB_WAL variant exists
    Given §3.1 row 2 names DB_WAL for spostgre WAL and svllm append_only logs
    When  the StorageClass enum is inspected
    Then  variant "DB_WAL" is declared

  Scenario: DB_TEMP variant exists
    Given §3.1 row 3 names DB_TEMP for temp forks and sort/hash spill, dropped on mount
    When  the StorageClass enum is inspected
    Then  variant "DB_TEMP" is declared

  Scenario: MODEL_IMMUTABLE variant exists
    Given §3.1 row 4 names MODEL_IMMUTABLE for svllm tensor_pack / adapter and spostgre blob fork
    When  the StorageClass enum is inspected
    Then  variant "MODEL_IMMUTABLE" is declared

  Scenario: GENERAL_MUTABLE variant exists
    Given §3.1 row 5 names GENERAL_MUTABLE for rel.main/pmap/vmap/fmap and svllm mutable state
    When  the StorageClass enum is inspected
    Then  variant "GENERAL_MUTABLE" is declared

  Scenario: CHECKPOINT_SNAPSHOT variant exists
    Given §3.1 row 6 names CHECKPOINT_SNAPSHOT for sealed checkpoint arenas
    When  the StorageClass enum is inspected
    Then  variant "CHECKPOINT_SNAPSHOT" is declared

  Scenario: No seventh variant is declared
    Given §3.1 authoritatively enumerates exactly six classes
    When  the StorageClass enum is inspected
    Then  the variant count equals 6
    And   svllm's 7 names do NOT appear as extra variants — they alias via §3.2

  Scenario: Durability defaults per §3.1 are documented on each variant
    Given §3.1 assigns DURABLE_ON_RETURN, DURABLE_GROUP_COMMIT, BUFFERED defaults per class
    When  the enum doc comments are inspected
    Then  each variant's doc names its default Durability from the §3.1 table
