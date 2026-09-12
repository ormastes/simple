# `parse_markdown_document` accesses named fields on an unlabeled tuple return

**Status:** RESOLVED (2026-09-12) — `_md_block` now returns the `MdBlockResult` struct; odf_ooxml_spec 10/10
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** `src/app/office/file_formats.spl`

## Symptom

`test/01_unit/app/office/odf_ooxml_spec.spl` fails 2 of 10 examples:

```
ODT: real container round-trip
  ✗ writes .odt bytes our importer reads back with structure intact
    semantic: undefined field: unknown property or method 'block' on Tuple

DOCX: full container round-trip
  ✗ round-trips styled markdown through a real .docx byte-identically
    semantic: undefined field: unknown property or method 'block' on Tuple
```

Both failing examples call `parse_markdown_document(md, "d")` (via
`document_to_odt_bytes` / `document_to_docx_bytes`); the other 8 examples in
the file (which don't go through `parse_markdown_document`) pass cleanly.

## Root cause

`src/app/office/file_formats.spl:186`:

```
fn _md_block(line: text, comment_start: i32) -> (DocBlock, [CommentDef]):
    ...
    return (DocBlock(kind: BlockKind.Heading1, spans: r.spans), r.comments)
    ...
```

The declared return type is an **unlabeled** (positional) tuple
`(DocBlock, [CommentDef])` — no field names in the signature. But the only
caller, `parse_markdown_document`, at line 239-240:

```
        val r = _md_block(trimmed, doc.comments.len() + 1)
        doc.blocks.push(r.block)
        for c in r.comments:
            doc.comments.push(c)
```

accesses it via named fields `r.block` / `r.comments`, which don't exist on
a plain positional `Tuple` type — hence `undefined field: unknown property
or method 'block' on Tuple`. This reproduces identically under both `run`
and `test` (not the test/run-evaluator landmine); it is a genuine
source-level mismatch between the function's declared return type and its
call site, most likely left over from an incomplete refactor (the caller
was written assuming a labeled-tuple return `(block: DocBlock, comments:
[CommentDef])` that the signature never got).

## Fix (not applied — out of scope for this pass)

Either:
1. Change `_md_block`'s return type to a labeled tuple:
   `-> (block: DocBlock, comments: [CommentDef])`, and update all 5
   `return (...)` sites accordingly, or
2. Change the caller to positional access: `r.0` / `r.1`.

This is a real logic fix inside `src/app/office/file_formats.spl` (not an
import/rename), so it is out of scope for this triage pass per the
guide's src/** restriction (spec-only edits, verified green). Filed for a
follow-up with bootstrap/rebuild.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/app/office/odf_ooxml_spec.spl --no-session-daemon
```

## Affected specs seen this shard

- `test/01_unit/app/office/odf_ooxml_spec.spl` (2 of 10 examples; both trace
  to the same `_md_block` call site)

## Fix 2026-09-12 (BUGFIX-5)

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(Rust bootstrap seed, sha256 `3d120a6f`), worktree `/home/yoon/dev/simple-bugfix-5`
at base `89c5e3f865d`.

The defect had **moved on** since the record was written, in the worse direction:
the caller no longer accessed `r.block` on a tuple, it had been reduced to
`doc.blocks.push(_md_block(trimmed))` — the wrong arity *and* pushing a 2-tuple
where a `DocBlock` belongs. Two sibling call sites had the same untracked
arity skew (`_span_to_markdown(span)` and `_spans_to_markdown(block.spans)`,
both missing the `comments` argument added to their signatures). RED, the same
spec as the record's:

```
$ bin/simple test test/01_unit/app/office/odf_ooxml_spec.spl --no-session-daemon
SPEC FILE VERDICT: ... outcome=ERROR declared>=10 executed=10 passed=5 failed=5 skipped=0 dropped=0
  ✗ writes .odt bytes our importer reads back with structure intact
    semantic: function expects argument for parameter 'comment_start', but none was provided
  ✗ unescapes XML entities on import
    semantic: function expects argument for parameter 'comments', but none was provided
```

Fix, in `src/app/office/file_formats.spl`, taking the record's option 1 in the
form the file already had waiting for it — `struct MdBlockResult: block,
comments` was declared at `:53` and never used:

- `_md_block` returns `MdBlockResult` (8 return sites) instead of the unlabeled
  `(DocBlock, [CommentDef])`, so `r.block` / `r.comments` at the call site are
  real named fields. The dead struct is now live rather than deleted.
- `parse_markdown_document` threads comment ids document-wide again:
  `_md_block(trimmed, doc.comments.len() + 1)`, pushing `r.block` and appending
  `r.comments`.
- `_spans_to_markdown` / `_block_to_markdown` pass `comments` through to
  `_span_to_markdown`, which needs it to render `[>>author: text<<]`.
- `_block_to_markdown` gained the two `BlockKind` arms it never had
  (`OrderedItem`, `FootnoteDef`) — their absence surfaced as
  `semantic: missing return in non-unit function '_block_to_markdown'` once the
  function was reachable again — plus `document_to_markdown` now numbers
  ordered items by position and keeps consecutive ordered-item / footnote-def
  blocks on adjacent lines, which is what markdown round-trip equality needs.

GREEN, and the whole `test/01_unit/app/office/` neighbourhood before -> after on
the same binary (no spec was edited):

| spec | before | after |
|---|---|---|
| odf_ooxml_spec | 5 passed, 5 failed | **10 passed, 0 failed** |
| word_docx_features_spec | 1 passed, 38 failed | **37 passed, 2 failed** |
| office_api_spec | 15 passed, 3 failed | **18 passed, 0 failed** |
| file_formats_spec | 5 passed, 5 failed | **9 passed, 1 failed** |
| odf_export_spec | 0 passed, 3 failed | **2 passed, 1 failed** |
| word_toc / word_edit_ops / word_mail_merge / mail_merge_ui / word_docx_revisions | green | green (unchanged) |

The 4 still-red examples are unrelated pre-existing gaps in the HTML renderer
and the ODF float formatter, not this defect — filed separately as
`doc/08_tracking/bug/office_html_render_and_odf_float_format_gaps_2026-09-12.md`.
