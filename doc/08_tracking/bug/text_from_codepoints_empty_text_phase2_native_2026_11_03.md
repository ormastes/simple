# text_from_codepoints returns empty text under Phase-2 native codegen

- Status: fix-implemented-verification-pending (P1). Root cause: char_from_code sliced a NUL-leading string table, yielding "" on the pinned Phase-2 producer; fixed by da22bdea07a (bytes via rt_bytes_to_text). Spec: test/01_unit/lib/common/encoding/text_codepoints_roundtrip_spec.spl. Verify after producer redeploy. Found 2026-11-03 while narrowing devhub_secured_db_key_session_open_failure_2026_10_27.
- Symptom: under Phase-2 native codegen `text_from_codepoints` returns empty text, so the row-read path
  reports SchemaNotFound, surfacing as STORAGE_PORT_CORRUPT_SOURCE on the secured messenger DB.
- Verification: needs a redeployed Phase-2 producer; the current pinned producer predates the fixes.
- Related: devhub_secured_db_key_session_open_failure_2026_10_27 (key-session part fixed by ace3ef1d00b / 93a08ab43ab).
