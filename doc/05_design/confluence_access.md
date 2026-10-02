# Confluence access repair design

1. Escape backslashes, then quotes in title and space CQL literals.
2. Extract parsed JSON strings with `json_to_string`; preserve existing serialization of non-string fields.
3. Require listing `results` to be an array, including the valid empty array.
4. Interpret curl output through `confluence_response_result`. Nonzero exit or missing status is a transport error; HTTP failures retain their status and redact body diagnostics. Successful content is untouched.
5. Resolve only the selected credential key through environment, command and auth document. The public path-based helper makes this policy testable without reading real credentials.

No UI change. Existing CLI and return tuple shapes remain compatible. Named target fallback removal is deliberate: configure credentials under `confluence.<target>` when selecting that target.
