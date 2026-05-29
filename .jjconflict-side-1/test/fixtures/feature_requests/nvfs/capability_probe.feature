# Feature: NVFS capability probe table
# Anchors: doc/05_design/nvfs_design.md §6 (capability probe table),
#          §4.2 (fs_caps signature), §11 (spostgre NVFS interface assumptions)
# Target: src/lib/nogc_sync_mut/fs/nvfs/ (FsCaps struct + probe trait)
# Status: pending — Phase 5 declares the trait + struct; M3 implements probes, M1 uses defaults.

Feature: NVFS capability-probe surface matches §6
  As a Phase 5 engineer
  I want the FsCaps struct and probe trait to enumerate every row from §6
  So that callers (spostgre, svllm) can depend on the cached capability shape

  Background:
    Given §6 names 10 capability rows, each with a probe mechanism and a baseline fallback
    And   §4.2 gives "fn fs_caps() -> FsCaps" as the cached-read entry point
    And   spostgre caches FsCaps at mount and refreshes at each checkpoint (per spostgre_design.md §5 and §11)

  Scenario: FsCaps struct is declared in fs/nvfs/
    Given the skeleton compiles
    When  the NVFS trait module is inspected
    Then  struct "FsCaps" is declared in "src/lib/nogc_sync_mut/fs/nvfs/"
    And   it is the return type of "fs_caps"

  Scenario: FsCaps carries the fields named in from_spostgre.md §S5
    Given §S5 lists preferred_write_granule, atomic_write_unit_power, supports_cas, supports_zns, supports_fdp, supports_copy_offload, supports_flush_fua, write_amp_hint, mount_generation
    When  the FsCaps struct is inspected
    Then  each of those nine fields is declared with the type given in §S5

  Scenario: Probe trait exposes one entry per §6 row
    Given §6 rows: ZNS, FDP, CMB, PMR, Flush, FUA, Compare-and-Write, Multiple Atomicity Mode, Copy offload, Dataset Management
    When  the probe trait is inspected
    Then  a probe method or FsCaps flag exists for each of the 10 rows
    And   every row has a documented baseline-fallback path

  Scenario: ZNS probe has a mechanism and fallback
    Given §6 row "ZNS" says "Identify Namespace CSI=02h (Zoned)" with fallback "Conventional NS"
    When  the probe for ZNS is inspected
    Then  the doc references CSI=02h
    And   a "Conventional NS" fallback is explicitly documented

  Scenario: FDP probe has a mechanism and fallback
    Given §6 row "FDP" says "Get Log Page FDP Configurations" with fallback "Conventional NS"
    When  the probe for FDP is inspected
    Then  the doc references the FDP Configurations log page
    And   a "Conventional NS" fallback is explicitly documented

  Scenario: Flush is always present
    Given §6 row "Flush" says "NVMe Flush command (always present)"
    When  the FsCaps field "supports_flush_fua" is inspected
    Then  its doc records that Flush is always available (FUA may still be absent)

  Scenario: FUA probe falls back to append + flush
    Given §6 row "FUA" says fallback is "Append + Flush"
    And   from_spostgre.md §S7 says arena_fua_append falls back to "append + flush" on non-FUA devices
    When  the FUA probe is inspected
    Then  its fallback path is the documented append + flush sequence

  Scenario: Compare-and-Write probe has double-buffered fallback
    Given §6 row "Compare-and-Write" says fallback is "Intent-log double-buffer"
    When  the CAS probe is inspected
    Then  the fallback doc references the intent-log double-buffer path
    And   from_spostgre.md §S6's CAS-vs-fallback note is cross-referenced

  Scenario: Multiple Atomicity Mode probe feeds atomic_write_unit_power
    Given §6 says the probe reads Identify Controller AWUPF / AWUN
    When  the atomicity probe is inspected
    Then  it populates "atomic_write_unit_power" in FsCaps

  Scenario: Copy offload probe has a read-then-write fallback
    Given §6 row "Copy offload" says fallback is "Read-then-write in NVFS"
    When  the copy-offload probe is inspected
    Then  arena_clone_range's doc references the capability-probed path selection

  Scenario: fs_caps_refresh is callable and bumps mount_generation behavior is documented
    Given §4.2 mentions fs_caps, and §3-arch notes FsCaps is refreshed at each checkpoint
    When  the refresh entry point is inspected
    Then  a refresh function exists (e.g., "fs_caps_refresh")
    And   its doc explains that callers re-read FsCaps after refresh rather than caching stale pointers
