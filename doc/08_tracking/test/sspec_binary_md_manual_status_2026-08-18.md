# SSpec binary evidence — Markdown manual generation status (2026-08-18)

## What was checked

Whether `bin/simple`'s spipe-docgen actually renders the binary evidence
stacked word/bit reference tables as real Markdown pipe-table syntax
(`| col | col |`) in generated docs, per
`doc/05_design/infra/sspec/binary_reference_stacked_design.md`.

## Command run and output path

```bash
bin/simple src/app/spipe_docgen/main.spl \
    test/01_unit/lib/common/spec/evidence/binary_layout_spec.spl \
    test/01_unit/lib/common/spec/evidence/manual_render_spec.spl \
    --output /tmp/docgen_out
```

Output written to:
- `/tmp/docgen_out/01_unit/lib/common/spec/evidence/binary_layout_spec.md`
- `/tmp/docgen_out/01_unit/lib/common/spec/evidence/manual_render_spec.md`
- `/tmp/docgen_out/INDEX.md`

(Real `doc/06_spec/` runs use the same generator; `--output` was pointed at
`/tmp` only to avoid touching tracked docs during this probe.)

## Real generated output (quoted)

The generator DOES produce genuine Markdown pipe tables — for its own
metadata sections:

```
| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |
```

and

```
## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
...
```

But the scenario BODY — where the binary/bit stacked reference would live —
is the raw `.spl` source re-emitted verbatim inside a fenced code block:

```
#### renders a manual table generated from the same layout, not hand-written

<details>
<summary>Executable SSpec</summary>
...
```simple
val pte: i64 = 0x8000000012345003
val rows = binary_field_table(pte, pte_layout())
assert_true(rows.len() > 1)
assert_true(rows[0].contains("Field"))
```
</details>
```

## Verdict: does a stacked word/bit reference table render as a real
Markdown table today?

**NO.** Reasoning:

1. `spipe-docgen` (`src/app/spipe_docgen/`) is a **static source-extraction**
   tool: it parses `"""..."""` doc blocks and `describe`/`it`/`step` names out
   of the `.spl` file text and re-emits the raw source as a fenced code
   block. It never **executes** the spec, so it can never capture the actual
   return value of `binary_field_table(...)`, `stacked_rows(...)`, or
   `stacked_compare_rows(...)` — those rows exist only at test-run time,
   inside the interpreter, and are only ever compared with `assert_true`,
   never captured into the generated manual.
2. Separately, `src/lib/common/spec/evidence/manual_render.spl` **is** a real
   Markdown-table renderer (`render_pipe_table`, used for
   `ManualBlockKind.table` / `byte_table` / `expected_actual` /
   `troubleshooting`) that emits genuine `| col | col |` syntax with a
   `| --- |` header-separator row — proven correct by
   `escape_cell`/`split_row` and used inside `evidence_comparator.spl`
   (`comparison_to_manual_blocks`, `ManualBlockKind.expected_actual`). This is
   the correct table-rendering primitive.
3. **The gap is that the binary/bitfield stacked reference figure never flows
   through that renderer.** `binary_field_table` (in
   `src/lib/common/spec/evidence/format/binary_layout.spl:242`) already
   builds its rows with `" | "` join syntax compatible with
   `render_pipe_table`'s `split_row` convention, so it is one step from being
   table-ready — but nothing calls
   `manual_block(ManualBlockKind.byte_table, ..., binary_field_table(...))`.
   `stacked_rows`/`stacked_compare_rows` (same file, `:406`/`:417`) are worse:
   they build **plain reference lines with no `|` at all** (by design — they
   are meant to be the "figure", not the "table", per the design doc's
   "stacked figure ... then a secondary field table" split), so even if
   captured into a `ManualBlockKind.terminal_grid`/`code_block` today, they
   would never render as a pipe table regardless of routing.

## What the design docs ask for

`doc/05_design/infra/sspec/binary_reference_stacked_design.md`:

> "Reference manual: one coherent stacked figure (bit ruler + word rows,
> proportional field widths), then a secondary field table and bad-pattern
> table" — output targets "{terminal, markdown/html, SDN/JSON}".

So the design itself distinguishes the stacked **figure** (word rows, meant
to look like a ruler — not naturally tabular) from the secondary **field
table** and **bad-pattern table** (meant to be genuine tables). Today only
`binary_field_table` is table-shaped; nothing downstream turns any of it,
figure or table, into rendered Markdown, because `spipe-docgen` never
executes the spec that would produce the rows.

## Concrete GAP list

1. `spipe-docgen` has no execute-and-capture path — it only reads source
   text. Wiring live evidence capture into the doc-generation pipeline (so a
   generated manual could ever show real `binary_field_table`/`stacked_rows`
   output instead of source) is a genuine pipeline change: it would need
   spipe-docgen to either (a) run the spec and intercept
   `manual_block(...)` calls, or (b) read manifest/evidence records the spec
   run already wrote to disk and correlate them back to the doc. Neither
   exists today. **This is NOT a small/contained fix** — it touches the
   docgen execution model, not just a rendering function — so per this task's
   scope it is documented here, not implemented.
   - Proposed API sketch (not implemented): an `EvidenceManifest`-keyed
     sidecar file per spec run (e.g.
     `doc/06_spec/<mirror-path>.evidence.sdn`) written by the test runner via
     `evidence_manifest_lines`, which `spipe-docgen` reads back and splices in
     as rendered `ManualBlock`s (via `render_manual`) alongside the existing
     source-extraction output — additive, no change to today's per-spec `.md`
     shape.
2. `stacked_rows`/`stacked_compare_rows` produce plain reference lines, never
   pipe-table syntax, even though the design explicitly wants the *word
   rows* to remain a figure (this is arguably correct behavior, not a bug —
   see design quote above). No change made to either function.
3. `binary_field_table`'s rows are table-shaped but are never passed through
   `manual_block(ManualBlockKind.byte_table, ...)` anywhere in
   `evidence_comparator.spl` or elsewhere — no caller wires it into the
   typed-evidence manual pipeline at all. Left as a gap (would require
   picking a call site and audience policy, judgment calls out of scope for
   an additive-only change).

## What was implemented (small, additive, contained)

Per the task's escape hatch: a standalone Markdown-pipe-table variant of the
existing `stacked_rows` figure was added, so a caller that DOES want the
stacked word figure as a real table (rather than the plain-line figure) has
a ready-made renderer. It does not touch `stacked_rows`, does not wire into
`spipe-docgen`, and does not change any existing exported function's
behavior.

- `src/lib/common/spec/evidence/format/binary_layout.spl` — added
  `pub fn stacked_md_table(values: [i64], word_label: text, first_word: i64) -> [text]`,
  right after `stacked_rows`. Emits a header row
  (`| Word | Value (hex) | Binary |`), a `| --- | --- | --- |` separator row,
  and one real pipe-delimited data row per word.
- `test/01_unit/lib/common/spec/evidence/format/stacked_md_table_spec.spl` —
  new spec proving `stacked_md_table` emits valid table syntax (header row,
  separator row, pipe-delimited data rows) for a 2-word layout, and that the
  encoded hex/binary values are correct.

### Test run evidence

```bash
bin/simple test test/01_unit/lib/common/spec/evidence/format/stacked_md_table_spec.spl
```

Final result line:

```
Results: 2 total, 2 passed, 0 failed
```

## Bottom line

Real Markdown tables (`| col | col |`) DO get generated by
`spipe-docgen` today — but only for its own fixed metadata sections
("At a Glance", "Tests" summary, "Scenario Summary"). The binary evidence
stacked word/bit reference tables described in the design doc are **not**
part of that output: `spipe-docgen` never executes a spec, so it can never
capture `binary_field_table`/`stacked_rows`/`stacked_compare_rows` output,
and no code path routes those functions' output through the one renderer
(`manual_render.render_pipe_table`) that does produce genuine table syntax.
Closing that gap needs a pipeline change (evidence capture + correlation),
which is out of scope for an additive-only fix and is left as GAP #1 above.
