# DevHub workaround registration and preservation evidence

The audited DevHub/P2 compatibility workarounds are linked to canonical open bugs. The main Messenger database panic is not claimed fixed by this tracking work.

## Canonical registration

The existing BugDatabase API could not safely regenerate the complete registry: 20 legacy rows have field counts outside their table schema. A narrow append-only domain API now serializes only new records and keeps the entire old payload opaque. It validates the existing CRC, rejects pending WAL and duplicate IDs, holds the existing file lock across read/publication, and uses the real atomic file publisher. No database cells or CRCs were hand edited. The derived `.simple/workarounds.sdn` index was not manually edited.

After a qualified scratch copy, the API registered eight open underlying bugs on fresh release base `842d92702049268524a39e4d11d937e4106da6d4`. Strict independent inspection confirmed:

- All 5,267 original rows in six tables, including all 20 opaque legacy rows, remain intact.
- Removing only the 32 newly added row lines yields the exact original payload bytes, including comments and table metadata.
- Every new bug row, description, removal condition and investigation value matches the intended API input.
- The actual new unsigned CRC is 3989747835 and exactly matches Python zlib over the actual stored body.
- Duplicate-ID, invalid-CRC and pending-WAL controls each exited 1 without changing the input. Locks were released and WAL bytes retained.

The actual before-file SHA256 was `c617ac5ea12dfc2887fe2fb6e4e6433daf459ac8a4c74ef27b3c88e11e85fae4`; after-file SHA256 is `de927717baac960d519afd5c2677a5cbbffc575cc4ff5e0f8714eeca793c2846`.

## Producer and actual checks

The existing phase-2 producer remained unchanged: SHA256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`. No compiler was rebuilt. The qualified registration executable is SHA256 `4e7a0160881d43b5bf54df41b628c5c6ddc5651cb664658494705314f1849b18`.

The fourth bounded feature cycle compiled and executed successfully. It checked the independent CRC32 known answer 3421780262 for `123456789`, empty input, and chunked updates through high-bit-set register values before registry mutation. An earlier scratch API run internally accepted a negative CRC differing from zlib by 2^32; the independent unsigned oracle rejected it. Public i64 CRC outputs are now explicitly confined to their low 32 bits. The exact compiler widening/complement cause remains unisolated; the external oracle was not relaxed.

The first compile used the wrong independently copied BugDatabase owner and was corrected to the canonical sync writer with an explicit separate async read-snapshot type. The second compile encountered the already tracked native array.take issue in the sync query dependency; its established ordered-prefix source workaround is now mirrored without changing query limits. These are recorded failures, not passing executions.

## Source markers and limitations

Thirty new `@workaround` sites across sixteen files reference the eight actual canonical bug IDs. The sync query prefix loop also uses the already registered `native_array_take_method_missing_2026_10_21` marker. Markers immediately precede affected code; ordinary permanent fixes such as proper Windows DACL enforcement and normal explicit typing are not mislabeled as temporary workarounds.

The marker audit is static metadata validation, not a full native index or SSpec execution claim. Comment-only tags were inserted after native qualification. Formal append and CRC SSpec regressions are authored but unexecuted on the currently blocked standard SSpec path. All underlying workaround bugs remain open with explicit removal conditions; source-only review does not retire them.

## Registered underlying bugs

- `phase2_octal_permission_mode_lowering_2026_10_27`: Pinned Phase 2 lowers octal permission modes incorrectly.
- `phase2_u8_accelerated_sha256_ffi_carrier_2026_10_27`: Pinned Phase 2 byte carrier is rejected by accelerated SHA256 FFI.
- `windows_core_http_client_unavailable_2026_10_27`: Windows core runtime native HTTP client provider is unavailable.
- `phase2_result_tuple_try_binding_metadata_2026_10_27`: Pinned Phase 2 loses integer and byte tuple metadata across Result propagation.
- `phase2_bounded_process_text_abi_2026_10_27`: Pinned Phase 2 bounded process call loses command text ABI.
- `phase2_module_static_array_concat_initialization_2026_10_27`: Pinned Phase 2 cannot initialize DevHub module static arrays by concatenation.
- `bug_database_roundtrip_drops_overwide_legacy_rows_2026_10_27`: Bug database full save truncates opaque legacy row payloads.
- `phase2_crc32_i64_width_spill_2026_10_27`: Pinned Phase 2 CRC32 i64 boundary retains unexpected high bits.
