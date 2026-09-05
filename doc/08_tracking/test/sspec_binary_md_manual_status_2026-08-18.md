# SSpec binary evidence — Markdown manual generation status (2026-08-18)

## UPDATE 2026-08-18: Gap 1 — IMPLEMENTED

The "Proposed API sketch" below is now implemented, following the sidecar
convention that `app.spipe_docgen.spipe_docgen.evidence_loader` had already
defined but nothing wrote to. Also found and fixed: an unrelated pre-existing
bug in `test/02_integration/app/spipe_docgen_evidence_wiring_spec.spl` (a
fully-qualified call to an unimported `file_read`, causing all 2 of its
pre-existing `it`s to fail on `bin/simple test`) — both now pass.

**Added:**
- `src/lib/common/spec/evidence/format/evidence_sidecar.spl` —
  `emit_evidence(spec_path, section_title, md_lines)` appends a `table`-kind
  `ManualBlock` record to `"{spec_path}.evidence.sdn"` (or, if
  `SIMPLE_SPEC_EVIDENCE_DIR` is set, mirrored under that directory instead),
  in exactly the `key=value` / `---`-delimited format
  `evidence_loader.parse_evidence_sidecar` already reads.
- `src/lib/common/spec/evidence/format/binary_layout.spl` —
  `stacked_manual_rows(values, word_label, first_word)`: same stacked word
  figure as `stacked_md_table`, but as RAW `" | "`-joined rows (no
  leading/trailing pipe, no separator row) — the shape
  `manual_render.render_pipe_table` expects as INPUT. Feeding it
  `stacked_md_table`'s already-rendered output double-wraps and
  double-escapes every pipe (`\|`); this was caught and fixed during
  end-to-end verification below, not left as a known issue.
- `app.spipe_docgen.spipe_docgen.evidence_loader.evidence_sidecar_path` now
  also honors `SIMPLE_SPEC_EVIDENCE_DIR`, kept in sync by hand with the
  writer (the writer is `src/lib`, the reader is `src/app`, so they cannot
  share one function).
- `test/01_unit/lib/common/spec/evidence/binary_protocol_domains_spec.spl` —
  the UDP/IPv4 suite named in the task now calls `emit_evidence` with real
  `stacked_manual_rows(...)` output at 3 call sites (UDP word0
  expected/actual, IPv4 5-word header), additive — all 5 existing assertions
  stay green.
- `test/02_integration/app/spipe_docgen_evidence_wiring_spec.spl` — new `it`
  "renders a real Markdown pipe table from emit_evidence's binary word rows"
  proves the writer/reader agree end to end and that no `\|`
  double-escaping survives into the generated manual.
- `doc/07_guide/infra/sspec/binary_sspec_usage.md` — new "Generating the md
  manual" section with the exact commands.

**Proof — commands run, verbatim:**

```bash
bin/simple test test/01_unit/lib/common/spec/evidence/binary_protocol_domains_spec.spl
# Results: 5 total, 5 passed, 0 failed

bin/simple src/app/spipe_docgen/main.spl \
    test/01_unit/lib/common/spec/evidence/binary_protocol_domains_spec.spl \
    --output /tmp/docgen_out --no-index
# DONE Generated 1 docs (1 complete, 0 stubs)

bin/simple test test/02_integration/app/spipe_docgen_evidence_wiring_spec.spl
# Results: 3 total, 3 passed, 0 failed
```

**Proof — real generated `.md` content (quoted verbatim from
`/tmp/docgen_out/01_unit/lib/common/spec/evidence/binary_protocol_domains_spec.md`),
a genuine Markdown pipe table with header separator row, not source:**

```
## Typed Evidence

### UDP header word0 — expected

| Word | Value (hex) | Binary |
| --- | --- | --- |
| UDP_W0 | 0x35 00 ff cf 00 00 00 00 | 0b00000000_00000000_00000000_00000000_11001111_11111111_00000000_00110101 |

### UDP header word0 — actual (dst_port corrupted)

| Word | Value (hex) | Binary |
| --- | --- | --- |
| UDP_W0 | 0x50 00 ff cf 00 00 00 00 | 0b00000000_00000000_00000000_00000000_11001111_11111111_00000000_01010000 |
```

**Known limitation, stated rather than hidden:** the test-runner path
(`bin/simple test`) executed the spec file's `it` bodies twice within one
invocation (a pre-existing runner behavior, not introduced here), so the
sidecar's append-only writer accumulates duplicate blocks per `bin/simple
test` run. The generated manual therefore shows each evidence block twice.
This does not affect correctness of the rendered table syntax or values, and
is not part of the scope of this change — filing a dedicated bug on the
double-execution behavior is separate follow-up work, not done here.

**What remains open (unchanged from the original gap list below):**
`stacked_rows`/`stacked_compare_rows` (the plain, non-table figure) still
intentionally produce non-pipe reference lines, per the design's
figure/table split — unchanged, not a gap. `binary_field_table` is still not
wired into `evidence_comparator.spl` by any caller — unchanged, left as
gap 3 below, out of scope for this additive change.

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

## UPDATE 2026-08-18 (cont.): all domain suites now emit evidence

Gaps 2 and 3 stay open (unchanged, out of scope). This update wires
`emit_evidence` + `stacked_manual_rows` into the three remaining goal-4
domain suites, following the exact pattern already landed in
`binary_protocol_domains_spec.spl` above — additive only, no existing
assertion changed. **All 4 domain suites now emit evidence into the md
manual:**

- `test/01_unit/lib/common/spec/evidence/binary_protocol_domains_spec.spl`
  (UDP/IPv4) — already wired, unchanged.
- `test/01_unit/lib/common/spec/evidence/binary_domains_spec.spl` (TCP header
  word / AES-128-OFB KAT / gzip) — 2 `emit_evidence` call sites added: TCP
  word3 expected/actual (flags-corrupted), AES-128-OFB block1 expected
  (NIST vector) / actual (bit-flipped).
- `test/01_unit/lib/common/spec/evidence/binary_algorithm_domains_spec.spl`
  (SHA-256/CRC32) — 2 call sites added: SHA-256("abc") expected digest words
  / actual (corrupted-input "abd"), CRC-32/ISO-HDLC("123456789") expected /
  actual (corrupted high half).
- `test/01_unit/lib/common/spec/evidence/binary_embedded_domains_spec.spl`
  (UART 16550 LSR/FCR registers) — 1 call site added (2 `emit_evidence`
  calls): UART LSR readback expected (idle, THR/TX empty) / actual
  (framing_error set).

**Proof — commands run, verbatim (results lines quoted, before/after count
identical since no assertion was added):**

```bash
bin/simple test test/01_unit/lib/common/spec/evidence/binary_domains_spec.spl
# Results: 6 total, 6 passed, 0 failed

bin/simple test test/01_unit/lib/common/spec/evidence/binary_algorithm_domains_spec.spl
# Results: 4 total, 4 passed, 0 failed

bin/simple test test/01_unit/lib/common/spec/evidence/binary_embedded_domains_spec.spl
# Results: 8 total, 8 passed, 0 failed

bin/simple src/app/spipe_docgen/main.spl test/01_unit/lib/common/spec/evidence/binary_domains_spec.spl --output /tmp/docgen_out --no-index
bin/simple src/app/spipe_docgen/main.spl test/01_unit/lib/common/spec/evidence/binary_algorithm_domains_spec.spl --output /tmp/docgen_out --no-index
bin/simple src/app/spipe_docgen/main.spl test/01_unit/lib/common/spec/evidence/binary_embedded_domains_spec.spl --output /tmp/docgen_out --no-index
# DONE Generated 1 docs (1 complete, 0 stubs)   [x3]
```

**Proof — real generated table rows, quoted verbatim (header separator row
included, proving genuine rendered table syntax, not source):**

`binary_algorithm_domains_spec.md`:
```
### SHA-256("abc") — expected digest words

| Word | Value (hex) | Binary |
| --- | --- | --- |
| SHA_W0 | 0xbf 16 78 ba 00 00 00 00 | 0b00000000_00000000_00000000_00000000_10111010_01111000_00010110_10111111 |
```

`binary_embedded_domains_spec.md`:
```
### UART LSR readback — actual (framing_error set)

| Word | Value (hex) | Binary |
| --- | --- | --- |
| LSR_W0 | 0x68 00 00 00 00 00 00 00 | 0b00000000_00000000_00000000_00000000_00000000_00000000_00000000_01101000 |
```

**Known-issue reproduction (do not treat as resolved):** while generating
`binary_domains_spec.md`, the sidecar
`binary_domains_spec.spl.evidence.sdn` came out with each of its 4
`emit_evidence` blocks duplicated (8 blocks total, byte-identical pairs) from
a single `bin/simple test` invocation, reproducing
`doc/08_tracking/bug/spec_runner_executes_it_bodies_twice_2026-08-18.md`
(previously marked "not currently reproducible"). The sibling
`binary_algorithm_domains_spec` and `binary_embedded_domains_spec` sidecars,
wired the same session with the identical call pattern, did **not** double.
See that bug doc's new dated entry for the verbatim duplicate content and
analysis. No code fix attempted (out of scope here, per that doc's existing
"Fix decision").

**Gate:** `sh scripts/check/check-binary-sspec-evidence.shs` was extended
with a non-emptiness check on the 4 wired suites' `.evidence.sdn` sidecars
(previously the gate only checked example counts and negative-case markers,
never that emission actually happened) and reruns green:
```
PASS — 6 spec(s) checked, 54 example(s) total, 0 vacuous, negative cases present (executed: binary_compare_spec(11) binary_domains_spec(6) binary_protocol_domains_spec(5) binary_algorithm_domains_spec(4) binary_embedded_domains_spec(8) binary_layout_schema_spec(20) skipped:)
```
The 54-example floor was already measured with these suites' current example
counts (domains=6, algorithm=4, embedded=8 — unchanged, since no assertion
was added), so no ratchet was needed.
