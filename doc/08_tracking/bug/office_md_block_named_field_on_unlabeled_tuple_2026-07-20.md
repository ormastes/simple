# `parse_markdown_document` accesses named fields on an unlabeled tuple return
## Resolved — verified 2026-11-25: `_md_block` now returns the `MdBlockResult` struct; the named-field access is valid

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** resolved (fix verified 2026-11-25, see note at the bottom)
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


## Verification note — 2026-11-25 (release/1.0.0)

**The reported defect is fixed.** `_md_block`
(`src/app/office/file_formats.spl:195`) no longer returns an unlabeled
`(DocBlock, [CommentDef])` tuple: it returns the `MdBlockResult` struct
(declared at `file_formats.spl:54` with named `block` / `comments` fields),
so the caller's `r.block` / `r.comments` accesses at lines 244-246 are valid
named-field accesses on a struct, not on a positional `Tuple`. The
`undefined field: unknown property or method 'block' on Tuple` semantic
error can no longer occur on this path.

Verified on the pinned Windows seed (interpreter, standalone probe —
`bin/simple test` is blocked repo-wide at this tip by the
`@representation_boundary` seed/source inconsistency): the spec's exact
scenario `parse_markdown_document("# Annual Report\n\nStrong growth.\n\n-
Expand team", "d")` runs with no semantic error and produces the correct
structure — 3 blocks, and `document_to_markdown(doc)` renders
`# Annual Report`, `Strong growth.`, `- Expand team` byte-correctly.

**Residual observation (separate defect, out of scope here):** the same
probe shows `document_to_odt_bytes` produces 1233 bytes but
`odt_bytes_to_document` imports 0 blocks back under the interpreter, so the
spec's ODT/DOCX *round-trip* examples may still be red for an unrelated
import-side reason. That is not this bug (this bug is the compile-time
named-field error) and was not investigated further; noted so the next
triage of `odf_ooxml_spec.spl` does not attribute it to `_md_block`.
