# Stage2 windows-gnu link: 112 undefined rt_* symbols

READY FOR OPUS REVIEW. Severity P1. Status: open.

Repro: same native-build command as stage2_byte_len_unresolved_symbol (core-c-bootstrap bundle).
Observed: 'Build failed: 112 runtime symbol(s) referenced by generated code have no definition' e.g. rt_bytes_concat, rt_bytes_slice, rt_db_get/put/*, rt_current_time_ms, rt_linux_group_*, rt_tls13_*. Full list: C:/dev/p3new/stage2new/unresolved_s2n7.txt.
SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1 only skips the pre-check; windows-gnu ld.lld still hard-errors because the trap-stub parity retry in native_project/linker.rs was is_msvc-only.
Workaround WA-s2n8: enable retry for gnu + --error-limit=0 (uncommitted seed diff in stage2-rel). Real fix: back the symbols in core-c-bootstrap (rt_db_* via embedded SQL engine, never libsqlite3) or gate callers out of the entry closure.
