# ARM64/macOS source and registry audit — 2026-11-03

Initial inventory: 71 unique records at ccb7f128, joined by platform terms, including shared dependencies and historical mentions. The immutable initial SDN is not a current defect count. Source review base: a41511004a0. No native acceptance is inferred from this audit.

This checkpoint records two newly demonstrated defects separately: ARM64 Linux seed numeric-conversion suffix rebinding (P0, bootstrap repair owner), and direct-native AArch64 scalar float integer/zero lowering (P2, fail-closed repair owner). Both remain fixing with target validation outstanding. The old i64-to_text MIR provenance record is distinct and unchanged.

Two stale source-cause records become verification-pending: seven ARM64 launcher paths repaired by c374fcca687, and x86-only Rust test macro cause removed by 41ae8509798. Remaining admitted-runtime/target test requirements are explicit. Historical macOS fixed/closed labels are retained; the crosscheck lists seven report/status inconsistencies for owner reconciliation, not proof of recurrence. GUI, Vulkan, Metal and Endpoint Security native evidence remains unresolved. Windows-only deployment context and Linux Metal emulation requests are not counted as demonstrated native macOS failures.

Root-authorized reaping of three unrelated abandoned claims is preserved exactly: indexed_char_to_i64_silent_zero_family_2026-08-10, mir_shard_worker_budget_16gb_serializes_mir_2026-10-19, native_build_step5_serial_threads_ignored_2026-09-04. Their status returns to open and released receipts remain; no source changes or acceptance claims for these lanes.

The ARM64 firmware owner is independently claimed while its source repair is reviewed. Its claimed status is not a repair PASS. Existing native macOS CI run41613080079 is bound to frozen ccb7f128; no duplicate run was dispatched. Prior SIGKILL is not a demonstrated OOM cause.

See macos-host.md and tooling-portability.md for source owners and exact remaining native gates; db-crosscheck.md/sdn for the 71-record ledger. These are source audits, not generated SPipe manuals or native qualification receipts.

## Final reconciliation checkpoint

`current_inventory.md` and `current_inventory.sdn` supersede initial counts for this scoped checkpoint. PR6384 firmware source repair is merged and waiting for real firmware acceptance. Explicit waiting-verification receipts also track the two previously repaired launcher/test causes. Only source-confirmed ARM64 PCI/ivshmem is reopened. Eight historical native acceptance gaps are linked separately without erasing closure history. Unexecuted direct-native float candidate remains unlanded.

## Active PCI checkpoint

Current claim-aware counts are 29 open, 3 fixing, 11 verification-pending, 18 fixed and 12 closed. PCI fixing reflects ongoing DTB/provider work, not a landed fix. LLD lightweight object/link diagnostics demonstrate the arbitrary-symbol quoting hazard but both canonical compiler path owners sanitize hyphens; the historical path-trigger recurrence is not established. No gratuitous linker patch or status reopening follows.
