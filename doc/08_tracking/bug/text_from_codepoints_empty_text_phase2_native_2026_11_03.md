# text_from_codepoints returns empty text under Phase-2 native codegen

- Status: open (P1). Found 2026-11-03 while narrowing devhub_secured_db_key_session_open_failure_2026_10_27.
- Symptom: under Phase-2 native codegen `text_from_codepoints` returns empty text, so the row-read path
  reports SchemaNotFound, surfacing as STORAGE_PORT_CORRUPT_SOURCE on the secured messenger DB.
- Verification: needs a redeployed Phase-2 producer; the current pinned producer predates the fixes.
- Related: devhub_secured_db_key_session_open_failure_2026_10_27 (key-session part fixed by ace3ef1d00b / 93a08ab43ab).
