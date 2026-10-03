# SCV Workstream A — Implementation Notes

This note records the diagnosis from the SCV WASM executor workstream. It was
left with an unresolved revision conflict. The executable test and source at
this revision, rather than either side of that conflict, determine current
behavior.

## Recorded fixes

The earlier workstream corrected the invalid brace-form `ScvRemoteRef` struct
in `src/lib/scv/public_remote.spl` to Simple's colon/indent form. The old
syntax prevented the SCV CLI from compiling before the WASM assertions ran.
It also added `SIMPLE_MEMORY_LIMIT_MB=1024` and
`SIMPLE_SIBLING_PRELOAD_LIMIT=5` to the integration test's child compiler
invocations to make memory pressure bounded and diagnosable. Those historical
test results have not been rerun for this revision.

## AC-1e still needs a test fix

`test/02_integration/app/scv_wasm_executor_spec.spl` currently extracts
`parser_hash=` from `parse-index`. The index row emitted by
`scv_parse_index_line` is positional:
`path|language|raw|syntax_hash|semantic_hash|kind|status|metric|node`.
It has no `parser_hash=` field, so the current extraction is empty. The
existing assertions expecting `hash1=sha256_` and `hash2=sha256_` are
not established by this note.

A meaningful cache-invalidation test should register the `foo` extension
without a leading dot, map it to each installed grammar version, run
`parse-gate` after each mapping, and compare the nonempty field-4 syntax
hashes for `sample.foo`. `scv_path_extension` returns `foo`, and the
syntax hash includes parser kind, version, and locked parser artifact hash.
Comparing the `parsers` artifact hashes alone would only prove that two
installed grammar files differ. This is a proposed test repair, not a
qualified AC-1e result.
