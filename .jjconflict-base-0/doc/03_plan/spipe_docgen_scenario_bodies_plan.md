# Plan: Render scenario code examples in generated spec docs (pure Simple)

**Date:** 2026-05-28
**Status:** In Progress
**Owner:** docgen
**Scope:** pure-Simple `spipe-docgen` only (no Rust seed changes beyond demotion)

## Problem

Generated spec docs (e.g. [doc/06_spec/feature/usage/math_blocks_spec.md](../06_spec/math_blocks_spec.md))
list scenario **titles** but never the code inside each `it` block. The source
[test/feature/usage/math_blocks_spec.spl](../../test/feature/usage/math_blocks_spec.spl)
has runnable bodies like `val result = m{ 2 + 3 }` / `expect(result).to_equal(5)`,
but they are dropped during generation. This is a generator limitation, not a
test-code problem — the specs are correct, standard BDD.

## Root cause (two generators, neither emits bodies)

| Path | Code | Emits |
|------|------|-------|
| Self-hosted CLI `simple spipe-docgen` | `src/app/spipe_docgen/spipe_docgen/{generator,parser}.spl` | `## Scenarios` titles + `## Test Structure` (describe/it tree, single-line docstrings) |
| Rust seed test-run auto-gen | `src/compiler_rust/driver/src/cli/spipe_docgen/generator.rs` (via `test_output.rs:236`) | `## At a Glance` + `## Scenario Summary` + `## Scenarios` titles; code only from `## Test:` markers |

- The on-disk `math_blocks_spec.md` is in the **Rust format** → it was last written
  by the Rust seed test path, not the pure-Simple CLI.
- Pure-Simple `extract_scenario_list` ([generator.spl:71](../../src/app/spipe_docgen/spipe_docgen/generator.spl#L71))
  and `extract_test_structure` ([parser.spl:386](../../src/app/spipe_docgen/spipe_docgen/parser.spl#L386))
  both read only the `it "..."` **title** and never the indented body.

## Decision: do it the pure-Simple way

Per CLAUDE.md ("main fixes in pure Simple; Rust seed is bootstrap-only"):

1. **Add body capture + fenced-code rendering to the pure-Simple generator.** This
   is immediately observable via the existing CLI:
   `bin/simple spipe-docgen test/feature/usage/math_blocks_spec.spl --output doc/06_spec`.
2. **Make the pure-Simple generator the source of truth for `doc/06_spec/`.** Route
   the auto-gen (test run) through it; demote the Rust `generate_spipe_documentation`
   to bootstrap-seed-only so it stops overwriting `doc/06_spec/` with the body-less
   format in self-hosted runs.

Out of scope: porting Rust's `## At a Glance` / `## Scenario Summary` tables into the
pure-Simple generator (separate format-parity follow-up, noted at the end).

## Phase A — Body extraction + rendering (core, pure Simple)

**Progress 2026-05-28:** Implemented in the pure-Simple parser and covered by
`test/unit/app/tooling/spipe_docgen_scenario_body_spec.spl`. The pure-Simple
generator now renders this rich output directly under `## Scenarios`, so the
spec document shows executable examples instead of a title-only scenario list.

**Parity progress 2026-05-28:** The Rust `spipe-docgen` command path was removed
from the driver command table and the Rust `cli/spipe_docgen` module was deleted.
The pure-Simple generator now covers the Rust-facing document features: title and
summary, `## At a Glance`, scenario counts, overview/body extraction, `## Example
Details` for `## Test:` markers, evidence summaries/tables, source-doc output
stem selection, related/dependency metadata, rich scenario examples, index
generation, and validation warnings.

**Rendering progress 2026-05-28:** Scenario bodies now detect `m{...}` math
blocks and append generated rendering examples showing the raw block, normalized
text rendering, and raw LaTeX rendering. `doc/06_spec/feature/usage/math_blocks_spec.md` has
been refreshed with 28 rendered math-block panels.

Augment the **existing** `## Test Structure` section rather than adding a parallel
section. `extract_test_structure` already walks the describe/context/it tree and
already tracks docstring state (`in_docstring`).

### A1. Parser: capture the body in `extract_test_structure`
File: [src/app/spipe_docgen/spipe_docgen/parser.spl](../../src/app/spipe_docgen/spipe_docgen/parser.spl) (`extract_test_structure`, line 386)

For each `it` / `skip it` / `pending` match (lines 451-463), after emitting the
bullet, collect and render the body:

```
indent(line) = number of leading spaces (expand a leading tab to its space width; see A3)
N = indent of the `it "...":` line
body = []
k = i + 1
while k < lines.len():
    cur = lines[k]
    if cur.trim() == "":            # keep blank lines inside the body
        body.push("")
        k = k + 1
        continue
    if indent(cur) <= N:            # dedent → body ended
        break
    body.push(cur)
    k = k + 1
# trim trailing blank lines from body
# dedent every body line by the minimum indent across non-blank body lines
# advance outer loop: i = k - 1  (so the while-i loop's i+1 resumes correctly)
```

Then emit, after the `- ok {name}` bullet:

```
``` + "simple"
<dedented body>
```        (closing fence)
```

(written as a real fenced block in markdown output, language tag `simple`).

If `body` is empty (e.g. `it "x": pass` on one line), emit no code block.

### A2. Strip the leading inline docstring from the body
If the first non-blank body line opens a `"""` block, skip through its closing `"""`
before rendering code (reuse the same `in_docstring` logic already in the function),
and optionally surface that docstring as the `_italic_` description already supported
for describe/context. Do **not** dump the `"""` lines into the ```simple block.

### A3. Indentation rules (list explicitly so impl doesn't hand-wave)
- Compute indent by counting leading spaces; treat a leading `\t` as the file's tab
  width (Simple sources are LF + spaces per `.gitattributes`; tabs are an edge case —
  normalize to 1 unit so comparison still works).
- Dedent = strip the common minimum leading whitespace of non-blank body lines.
- Blank lines inside the body are preserved (they carry no indent signal).
- A trailing `# comment` on the `it "name":` line is ignored for body detection
  (the `:` and body start on the next line regardless).

### A4. Edge cases to handle
- `it "TODO": pass` (single-line, empty multi-line body) → no code block.
- Body containing nested `if`/`for`/`match` (deeper indent) → captured wholesale by
  the `indent > N` rule; no special handling.
- `"""` docstring as first body line → A2.
- Final scenario at EOF (no trailing dedent line) → `while k < len` terminates the body.

## Phase B — Make pure-Simple the source of truth for `doc/06_spec/`

Goal: a normal test run regenerates `doc/06_spec/*.md` using the pure-Simple
generator (with Phase A bodies), not the Rust seed generator.

### B1. Self-hosted test runner calls the pure-Simple generator
Wire the self-hosted test runner to invoke `generate_feature_doc`
([generator.spl:239](../../src/app/spipe_docgen/spipe_docgen/generator.spl#L239)) in-process
for each executed `*_spec.spl`, writing to `doc/06_spec/`. (Today no `src/app` test
runner calls docgen; only `src/app/test/extract.spl` touches `06_spec`, for extraction.)

### B2. Demote the Rust auto-gen
`generate_spipe_documentation` in
[src/compiler_rust/driver/src/cli/test_output.rs](../../src/compiler_rust/driver/src/cli/test_output.rs#L210)
should no longer write `doc/06_spec/` in self-hosted runs (it is bootstrap-seed-only).
Lowest-risk: gate it behind `SIMPLE_BOOTSTRAP`/seed detection so the seed can still
self-test, but the canonical docs come from B1. No new Rust features.

## Verification

Golden file: `test/feature/usage/math_blocks_spec.spl` (contents already known).

1. `bin/simple spipe-docgen test/feature/usage/math_blocks_spec.spl --output /tmp/docgen-check`
   → confirm each scenario (e.g. "evaluates addition") is followed by a ```simple block
   containing `val result = m{ 2 + 3 }` and `expect(result).to_equal(5)`.
2. Spot-check edge cases: a spec with `skip it`, a `pending`, a `"""` docstring body,
   and a nested `if`/`for` body render correctly (no leaked `"""`, blanks preserved,
   correct dedent).
3. `bin/simple test test/feature/usage/math_blocks_spec.spl` → confirm
   `doc/06_spec/feature/usage/math_blocks_spec.md` is regenerated by the pure-Simple path and now
   contains the code blocks (validates Phase B routing).
4. `bin/simple build check` (lint/fmt/tests) stays green.

## Follow-ups (not this plan)

- Format parity: optionally port `## At a Glance` / `## Scenario Summary` tables into
  the pure-Simple generator so output matches the old Rust layout.
- Eventually delete the Rust generator once B1/B2 are proven in CI.
