# Verified semantic links in generated specifications

Authored manual; not generator output or runtime evidence. Executable spec: `test/02_integration/app/doc/semantic_document_rendering_spec.spl`. REQ-MC-008 B4. All eight scenarios UNRUN.

1. Prepare a real source file and parse its exact SHA256 revision. Render one explicit package-qualified semantic URI through the existing summary, symbol index and detail presentation; deduplicate the resolver map and retain ordinary heuristic symbols as text.
2. Reject malformed and unresolved URIs. Edit the real source file and reject the previously published revision.
3. Escape Markdown brackets, table delimiters, HTML delimiters and newlines in a link label.
4. Render ordinary symbols with an empty semantic map and preserve the existing specification/code presentation.
5. Preserve an existing Markdown output file when the source revision is stale; no verified document is written on refusal.

SPipe now accepts an explicit single-spec source authority through the existing CLI. Adapter implementation is authored; actual command execution remains UNRUN pending an admitted tools runtime.

6. Force a real atomic-provider staging failure using a valid maximum-length output filename. Verify the old document bytes remain and no staging file is retained.

## C4 authored publication counterexample — UNRUN

Resolve and render using the actual source owner, then mutate the source before
calling the production content publisher. Require RevisionChanged and exact old
output preservation. Restore source, publish successfully, and require both the
canonical link and exact source-revision artifact receipt. This tests the final
revision-snapshot guard; external check-to-rename races remain explicitly OPEN.

## SPipe command generation — authored, UNRUN

Generate semantic declaration links through SPipe docgen using one actual
`bin/simple spipe-docgen` invocation with `--source-file`, `--package`,
`--module`, and an exact `--revision` SHA256. Inspect the generated page for
its canonical declaration link and source revision receipt. A guessed symbol
must receive no generated declaration target.

Repeat with an unresolved declaration, forged module URI, and changed source
bytes. Each invocation must exit 1 and preserve the published document byte
for byte. Incomplete source authority must also fail before generation. The
scenario removes its private temporary directory afterward.

No command run, generated-manual review, or acceptance PASS is claimed here.
