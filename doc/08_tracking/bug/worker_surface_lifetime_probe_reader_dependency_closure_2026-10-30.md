# Worker surface lifetime probe imports unrelated frontend dependencies

The admitted11 native probe at `/tmp/simple-worker-surface-lifetime-admitted11-20261030` failed before its main body. Its log has six unique failing modules: `source_reader_v1` (2 fatal errors), `module_artifacts_v1` (7), `cache_single_flight_v1` (1), async `poll` (1), async `io.buffer` (20), and sync `http.url` (1). Repeated cache/parent diagnostics produce 101 ERROR rows, not 101 independent failures.

The production worker owner imports `TldrTableV1`. That storage module imported `SourceReader` only for the free `tldr_table_fill_v1` adapter. `SourceReader` imports the full frontend and module artifact writer. The lifetime fixture never invokes that adapter, but native entry closure is module based and therefore includes those dependencies.

Move the adapter unchanged into sibling `compiler.driver.cache.reader.tldr_table_fill_v1`. Update its one production caller (`file_fiber_v1`) and unit spec. Do not re-export it through the table, which would restore the unwanted dependency edge. Table and handle imports remain stable; adapter callers explicitly import its owner. The actual Future/Poll dependency remains and its generic-owner error is not claimed fixed.

Producer: bdd4c38529e44a86b78f183f7efdbc985faf26d67eb313ed6f8411e67e9d8a60; failed target db7ca0c30ba; new source base b5b650fc231b7a46152b446976db723c5bd32899. Those revisions have no changes to the six dependency source files. HIR scalar result binding does not correct HTTP declarations explicitly returning erased `list`/`tuple`.

Validation: exact adapter body retained; all owned source/test references updated; diff whitespace check. Existing real table-fill unit assertion remains. Native lifetime positive and omission-control executions are pending build-owner admission; this dependency repair is not a lifetime PASS or a Poll fix. Frozen attempt12 inputs remain untouched.
