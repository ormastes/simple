# Verified semantic links in generated specifications

Authored manual; not generator output or runtime evidence. Executable spec: `test/02_integration/app/doc/semantic_document_rendering_spec.spl`. REQ-MC-008 B4. All six scenarios UNRUN.

1. Prepare a real source file and parse its exact SHA256 revision. Render one explicit package-qualified semantic URI through the existing summary, symbol index and detail presentation; deduplicate the resolver map and retain ordinary heuristic symbols as text.
2. Reject malformed and unresolved URIs. Edit the real source file and reject the previously published revision.
3. Escape Markdown brackets, table delimiters, HTML delimiters and newlines in a link label.
4. Render ordinary symbols with an empty semantic map and preserve the existing specification/code presentation.
5. Preserve an existing Markdown output file when the source revision is stale; no verified document is written on refusal.

Limit: production CLI/actual SPipe callers still need an admitted package/module/revision configuration owner. This manual does not claim those adapters exist.

6. Force a real atomic-provider staging failure using a valid maximum-length output filename. Verify the old document bytes remain and no staging file is retained.

## C4 authored publication counterexample — UNRUN

Resolve and render using the actual source owner, then mutate the source before
calling the production content publisher. Require RevisionChanged and exact old
output preservation. Restore source, publish successfully, and require both the
canonical link and exact source-revision artifact receipt. This tests the final
revision-snapshot guard; external check-to-rename races remain explicitly OPEN.
