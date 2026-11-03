# ARM64/macOS registry crosscheck — 2026-11-03

Read-only audit at `a41511004a04c4e700293bdfdaeedfef2b8d7456`; database SHA-256 `79f3e723d149ff5effa27fe5994606d0eb610bacbcb49f4cc65e49a23723626c`. No builds, native runs, claims, database edits, or closure proofs. The 71-row action ledger is `db-crosscheck.sdn`.

## Integrity

All 71 inventory IDs are unique and remain registered with unchanged priority, status and title. All cited owner paths and explicit single-path report/regression references exist. Four IDs appear identically in both registry tables; deduplicate these mirrors when counting. This inventory is keyword-derived, not exhaustive proof of platform coverage.

Outside the 71-row scope, `bugs_active` duplicates `native_identity_i64_receiver_type_loss_2026_10_11`; its P2 fixing row conflicts with P1 fixing in `bugs`. This may merit resolver-owner comparison before registering the fresh crash as unrelated. There are 294 cross-table mirrored IDs and five differing records overall. Other differences involve `pure_simple_nested_extern_registration_2026_10_12`, `p4_gui_browser_missing_owner_imports_2026-10-05`, `bug_add_rename_path_recursion_rewrites_db_2026-10-04`, and `mono_preflight_schema_pin_and_mirror_drift_2026_10_27`; leave unrelated lanes untouched.

## Proposed reconciliation

Source-owner review should resolve seven closed-row/report contradictions: ARM64 ivshmem, interpreter Option/struct parity, macOS Stage4 low-memory, Vulkan native entry, Vulkan provider availability, Vulkan WM mirror/input evidence, and LLD defsym quoting. Each canonical report explicitly remains OPEN/no resolution evidence. Reopening would correct bookkeeping; it would not prove recurrence in current source.

Consider `fix-implemented-verification-pending` for stdbuf, TMPDIR quoting, Metal clip, and GUI SMF dynlib. Their own reports retain native evidence requirements. GUI SMF was administratively closed because no Mac host existed; that is not acceptance. Metal clip report says P2 while registry says P3; preserve priority until owner reconciliation.

Retain copy_mem's scoped historical closure: its report records focused 7/7/runtime export evidence. Retain theme-install source-regression closure without claiming live QEMU admission. RV64 exit-facade closure is valid for RV64 but leaves ARM64 follow-up; split that scope if confirmed. Firmware composite record needs supersession review because its description retains spc=8/single-sector gaps.

## Scope cautions

Exclude Windows build no-op from native ARM64/macOS repair totals: Mac appears only as a deployment-host limitation. Linux Metal emulation is a capability request, not a native Mac defect. Char syntax/condition staging, Caret recovery, HIR retention, M5 checkout hygiene, cross-architecture Vulkan boundaries, object format selection and RV64 import leakage are shared dependencies.

The prior process audit and `macos_p0_p3_reconciliation_2026_11_03.md` support existing source repairs, not fresh native acceptance. No CI result or signal-cause inference was added.
