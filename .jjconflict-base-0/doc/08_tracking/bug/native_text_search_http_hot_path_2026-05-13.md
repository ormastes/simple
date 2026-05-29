# Native text search blocks exact HTTP parser perf benchmark

Date: 2026-05-13
Status: Resolved

## Symptom

`test/perf/webserver/http_hot_path.spl` originally used `text.index_of("\r\n")`,
then `text.index_of("\n")`, then `text.find("\n")` to scan a request line and
headers. Interpreter mode parsed the request successfully, but native mode
returned the failure sentinel for every iteration.

## Impact

This forced an earlier fixed-slice benchmark proxy. The proxy was weaker than
the real parser path because it skipped delimiter search.

## Evidence

- Interpreter benchmark with delimiter search produced valid parse timings.
- Native benchmark with delimiter search printed `# sink=-1000`, proving every
  parse iteration hit the failure path.
- Native benchmark with fixed slices completed and reported CSV results.

## Resolution

Native method lowering now maps text `find`, `find_str`, and `index_of` to
`rt_string_find`, matching the HIR raw-`i64` contract. The Rust runtime also
exports scalar fallbacks for `rt_simd_str_search`, `rt_simd_str_last_index_of`,
`rt_simd_str_equal`, `rt_text_to_lower_ascii`, `rt_text_to_upper_ascii`, and
`rt_str_hash`.

`test/perf/webserver/http_hot_path.spl` has been restored to delimiter-based
request scanning and runs natively.

## Follow-up

A direct native import of `std.http_server.parser` still pulls broader legacy
HTTP/common modules and currently reaches an unrelated `env_get` native symbol
gap. Keep using the focused hot-path benchmark until the full parser dependency
chain is made native-clean.
