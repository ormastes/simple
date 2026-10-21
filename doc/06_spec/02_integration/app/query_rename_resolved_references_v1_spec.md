# Configured resolved-reference query

REQ-MC-008 / selected B5 prerequisite. Authored manual mirror; execution,
SPipe generation, typecheck and performance are **UNRUN** because this lane
has no qualified engine. This manual records assertions, not observed PASS.

Executable source: `test/02_integration/app/query_rename_resolved_references_v1_spec.spl`.

The command reads a version 1 SDN identity manifest, checks every configured
source revision and source-root membership, parses actual source, resolves
imports through the compiler and lowers actual HIR. It returns a snapshot for
the explicit manifest. It does not admit source edits or redirects.

Invoke the actual query entrypoint with:

```text
query rename --resolved-references --identity-manifest /workspace/identity.sdn --file /workspace/src/fixture/a.spl --line 1 --column 4
```

Each fixture owns a fresh temporary directory. Its source root contains real
`src/fixture/*.spl` files. Manifest package identity is `example.project`,
independent of explicit compiler module paths such as `fixture.a`.

| Scenario | Action and required result |
|---|---|
| Recursive function | Parse and lower a primitive function, recursive call and ordinary caller. Require one declaration origin, three exact references, real local SymbolIds, exact declaration bytes, one parse/lowering per file and nonzero actual visited nodes. Repeated snapshot lookup keeps its digest unchanged. |
| Imported aliases | Configure two same-spelled function declarations and a consumer with two explicit aliases. Select the first origin. Require its exact import-source token and alias-use roles; exclude the other declaration and alias. |
| UTF-8 and shadows | Put Korean text before the declaration; include comments, a plain string and a parameter shadow. Require original UTF-8 byte slices for the real declaration/call and exclude lexical contamination. |
| Candidate capture | Independently collect original and renamed candidate sources. A candidate calling a shadowing local value must fail. This is precursor evidence, without rename admission. |
| Failed second file | A malformed second configured file returns parse failure and no complete snapshot. |
| Separate package/module identity | A different opaque package changes the configuration digest while the configured module key stays `fixture.a`. A configured `fixture.wrong` key for the real `/src/fixture/a.spl` file fails actual registry admission; no path-derived replacement is inserted. |
| Physical duplicate | A POSIX fixture creates a real hardlink with `ln`. Distinct paths mapping the same physical file to different modules must fail configuration admission. This test requires an admitted host with that existing fixture utility. |
| Inventory failures | Add an unlisted source, duplicate a configured row, supply an incorrect revision and remove a configured source. Each request refuses a snapshot. |
| Unsupported/capacity | An unresolved import, unsupported loop, byte-changing conditional preprocessor directive or exhausted fact budget refuses the request instead of publishing truncated facts. A valid A5 typed representation decorator also refuses through original-token coverage, even after composition moves it out of generic function attributes. |
| Sequential lifecycle | Run valid, invalid and valid requests in one process. Require unchanged content digest/work counts for the two valid requests. A declaration without call sites remains a valid fully inspected result. |
| Actual CLI route | Call public `run_query` with the flag-only command, without legacy positional arguments or `--new-name`. Require the real route to succeed. Apply, missing configuration, duplicated flags, invalid positions and unknown flags return nonzero; exact source bytes remain unchanged. Default lexical entry and an unrelated subcommand do not gain semantic authority. |
| Structured output | Serialized output identifies `resolved-reference-snapshot-v1`, includes inspected files/revisions and `complete_for_manifest`, and states that no edits or redirects were admitted. It contains neither workspace-completeness nor WorkspaceEdit claims. |

The test suite uses actual filesystem admission and compiler owners. It supplies
no mock parser, symbol map, HIR or caller completeness flag. Runtime and numeric
startup/latency/RSS measurements remain unavailable. The later B2 component
join, candidate re-resolution, edit planning and atomic source/Markdown/redirect
transaction remain open.
