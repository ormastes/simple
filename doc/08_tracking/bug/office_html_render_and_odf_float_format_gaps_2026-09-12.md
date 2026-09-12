# Office: 4 pre-existing render/format gaps surfaced once the markdown path ran again

- Status: OPEN (2026-09-12)
- Found: 2026-09-12, BUGFIX-5, while fixing
  `office_md_block_named_field_on_unlabeled_tuple_2026-07-20`
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
  (Rust bootstrap seed, sha256 `3d120a6f`), base `89c5e3f865d`
- Area: `src/app/office/` (HTML renderer + ODF value formatting)

These 4 examples were already red before that fix — they were masked by the
arity errors that aborted the whole example earlier. They are genuinely
different defects and are filed rather than folded into that commit.

## Repro

```
bin/simple test test/01_unit/app/office/word_docx_features_spec.spl --no-session-daemon
bin/simple test test/01_unit/app/office/file_formats_spec.spl --no-session-daemon
bin/simple test test/01_unit/app/office/odf_export_spec.spl --no-session-daemon
```

## The four

1. `file_formats_spec` — "parses **bold**, *italic* and `code` into styled
   inline HTML": the rendered paragraph carries a monospace `font-family` on the
   whole `<div>` instead of emitting a `<code>` element; the spec asks the HTML
   to contain `>code</code>`.
2. `word_docx_features_spec` — "renders a Quote block as a real `<blockquote>`
   and a CodeBlock as `<pre><code>`": the renderer emits
   `<div class="quote">` / `<div class="code_block">` with inline styles, so
   `</pre>` never appears.
3. `word_docx_features_spec` — "renders a dotted underline and a trailing
   comments section in HTML": no comments section is emitted at all, so
   `<li>Alice: needs a citation</li>` is absent.
4. `odf_export_spec` — "types numbers and preserves formulas in ODF syntax":
   a whole number is written as `office:value="1200.0"`; ODF (and the spec)
   want `office:value="1200"`.

(1)-(3) are one theme — the HTML renderer models blocks as styled `<div>`s and
has no element vocabulary for code/quote/comments. (4) is an independent float
formatting rule.

## Not fixed here

Out of the shard scope BUGFIX-5 was working. Each needs a decision about the
renderer's element vocabulary (spec-driven semantic HTML vs. the current inline
styling), which is a design choice rather than a repair.
