# trace query prints TRACE-LEGACY-ROW / TRACE-AUTHORITY-CONFLICT diagnostics on stdout

- **Filed:** 2026-11-06 (libbug coordinator, Astra review of PRs #7202/#7206)
- **Status:** open (P3)
- **Symptom:** `simple run src/app/traceability/query_main.spl refs ...` appends per-row
  diagnostics (8 `TRACE-LEGACY-ROW: row has N fields, expected 10` for malformed bug_db rows,
  `TRACE-AUTHORITY-CONFLICT` lines) to stdout after the table, mixing them with the result an
  agent parses.
- **Fix direction:** print diagnostics on stderr (or as one summary count line on stdout),
  and file the malformed bug_db rows themselves.
