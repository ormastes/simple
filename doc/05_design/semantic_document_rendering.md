# Verified spec rendering

REQ-MC-008 B4 source-phase adapter. The existing spec renderer accepts a prevalidated semantic symbol map at its internal summary/index/detail presentation points. `generate_markdown_semantic_v1` obtains that map from the common resolver before publishing output through the existing atomic file owner. That provider stages beside the target, writes/flushes completely, preserves mode, renames, and cleans failures without unlinking the previous document. Explicit `spl:` symbols are deduplicated with an indexed set and resolved in one <=4096-element batch against a parsed document and exact revision. Ordinary extractor guesses keep their current code-text presentation.

Labels escape Markdown, HTML and table delimiters; URI delimiters are certified by the strict common URI parser. The renderer never manufactures stable identities or re-parses source per symbol. The original `generate_markdown` API continues to render its existing unbound symbol presentation. No process/env boundary or source-tree scan was added.

Status PARTIAL / ALL_UNRUN: caller ownership of package/module/source revision is explicit in the sibling API, but the current spec_gen CLI and SPipe docgen do not yet own those inputs. No metadata grammar is invented. A verified production caller and SPipe integration remain required before B4 completion. Existing tests cover the actual renderer map and file-writing boundary, including malformed/unresolved/stale refusal and preserving an existing output on stale source. No runtime or generated-manual evidence is claimed.

Revision2 adds actual atomic-provider I/O failure preservation: a real valid 255-byte output leaf makes provider temporary creation fail, and the old file plus directory membership must remain unchanged. The admitted target is Linux with a 255-byte leaf; test setup proves the old leaf can be created. Common resolver revision2 reparses actual source once per bounded batch; public snapshot metadata is untrusted, and rendering inherits only reauthenticated bindings. Runtime remains UNRUN.

Revision3 wires the existing spec-gen production caller with --source-file/--package/--module/--revision together, only for one --input. Incomplete or --all/--index authority is refused before generation. It opts into the existing **Links:** annotation and modern it extraction; ordinary parser calls retain their previous default. The common actual-source resolver gains resolve_semantic_links_file_v1 so the caller need not create then reparse a cache: one real producer parse per bounded batch, the same errors/limits/final revision check. The document-shaped API delegates after its revision consistency check. Output uses the existing atomic owner. SPipe docgen remains unwired and full B4 remains partial. Two real process CLI scenarios are authored UNRUN.

## C4 corrections and bounded publication contract

Markerless modern double-quoted `it`/`test` blocks in semantic mode use the
existing CoreLexer string-continuation and SPipe scenario-body owners. Only a
leading body docstring supplies explicit Links metadata. Actual source-line
positions merge legacy-marker metadata with modern body metadata in linear
source order; a legacy marker cannot hide modern annotations. Default parsing
keeps its previous behavior. Actual semantic CLI refuses empty extraction and
unsupported empty/inline bodies instead of verifying an empty URI batch.

After verified link-map resolution and complete rendering, the actual publisher
`publish_semantic_markdown_content_v1` performs a bounded exact source revision
read adjacent to `file_atomic_write`. Successful output records
`semantic-source-revision-sha256`. A source edit between resolution/rendering
and this final check refuses before replacing the old output. Output staging
failure still preserves the old file through the existing atomic provider.

This implements the C3 requested revision-snapshot publication contract. It is
not an atomic transaction between the source and output, and does not lock
arbitrary external source writers. External mutation between the final check
and output rename remains OPEN as a stronger concurrency guarantee; the artifact
represents its recorded revision rather than claiming perpetual source freshness.
The deterministic test uses the actual render and publish APIs with real source
mutation between them, not a mocked checker. Actual SPipe caller integration,
positive process configuration, broad declaration kinds and all runtime/perf
qualification remain OPEN. No source inspection is a runtime PASS.

## C5 leading-docstring provenance correction

Semantic modern extraction now reads the existing CoreLexer-owned
`simple_string_byte_ranges` receipt at the actual leading docstring found after
blank/comment lines. It never searches the whole scenario body for the first
textual triple quote. Skipped comments cannot open or close annotation metadata;
escaped quote spellings and trailing comments follow actual token ranges. Missing
or invalid token coverage empties the case body so the existing semantic CLI
extraction gate refuses rather than resolving an empty URI batch successfully.

String-range facts are computed once per semantic input file, alongside the
existing continuation facts; each leading docstring is copied only within its
actual token ranges. No source parse per URI/scenario, new runner, ID schema or
authority policy is introduced. Default parsing and the retained C4 publication
contract remain unchanged. All runtime/typecheck/docgen/performance results are
UNRUN; broader SPipe caller/configuration/kind and external atomicity limits stay
OPEN.
