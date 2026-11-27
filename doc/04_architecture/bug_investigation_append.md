# Bug investigation append owner boundary

The existing sync and async BugDatabase owners retain authority. New add_investigation_log(id, content) mutates only bug_investigation_logs and delegates persistence to the existing atomic CRC-backed save. No schema additions, status updates or replacement storage are introduced.

The method scans existing target rows, validates nonnegative unique line numbers within the portable integer parser range, finds max + 1, and detects identical content before committing a single row. Missing log tables use the existing three-column schema. Other table values and original log order remain unchanged. Validation completes before set_table; failure is a nonmutation result.

The codec is line-oriented and does not escape quotes or preserve unquoted boundary whitespace. The API accepts one nonempty trimmed physical line without double quotes, LF or CR. Commas and Unicode remain supported through the existing codec. Unsupported text is rejected, not normalized.

Repeated identical content is a successful no-op: callers wanting distinct events must include their event timestamp or stable receipt ID. The API does not auto-save or update a timestamp/status. An accepted batch calls save once.

Complexity: one scan of log rows, with duplicate-line membership checks proportional to target log count squared. Existing logs are small; this avoids introducing an index/schema contract. Single-writer audit updates can batch and save once; no subprocess or whole-workspace scans occur.

Limits: load still tolerates malformed source rows and duplicate table sections. The new method cannot restore data already discarded by that loader. Audit preflight must compare the raw input table/row inventory, reject malformed rows and pending WAL, and qualify full round-trip preservation on scratch before any real database save. Existing add_multiline_field and update_bug semantics remain unchanged.
