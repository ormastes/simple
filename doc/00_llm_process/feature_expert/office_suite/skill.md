# Feature Expert: office_suite (Calc / Sheets)

## Role

Own process knowledge for the LibreOffice-style office suite under
`src/app/office/` — the spreadsheet model, the formula engine and its recalc
ordering, the three cursor surfaces (GUI / TUI / `SheetsApp`), and the file
format readers. Lane state: `.spipe/libreoffice-suite/state.md`.

There was no feature expert for this area before 2026-08-18; the sibling
`business_suite` (ERP, `examples/12_business/simple_erp/`) and
`enterprise_suite` entries are different products and do not cover it.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Module map (verified by reading the files, 2026-08-18)

| Module | What it owns |
|---|---|
| `src/app/office/sheets/spreadsheet.spl` | `Sheet` / `Workbook` model. `is_row_hidden(row: i64)` (`:177`) is the hidden-rows model and is **1-BASED**. `Workbook.active()` at `:245-247` is `me.sheets[me.active_sheet]` — see the known-defect section below. |
| `src/app/office/sheets/formula.spl` | Formula evaluation. `resolve_cell_value:8652` / `resolve_cell_range:8687` are thin wrappers over `_resolve_cell_value` / `_resolve_cell_range`, which carry the `depth` parameter. Hidden-row-aware aggregates (SUBTOTAL 10x) at `:2040`, `:2075`. |
| `src/app/office/file_formats.spl` | Load/save + **recalc ordering**: `_ff_dep_plan` / `FfDepPlan` (`:584`), the `#CIRC!` cycle phase (`:712`). Also `parse_inline_spans`. |
| `src/app/office/sheets/fill_series.spl` | Autofill. `FillPattern` enum (`:16`): `CopyCycle`, `Linear(start, step)`, `TextNumber(prefix, start, step, pad)`, `NameCycle(list_id, start_index, step)`. Entry points `detect_fill_pattern:26`, `fill_series_cells:144`, `fill_series_value:157`. |
| `src/app/office/sheets/named_ranges.spl` | `NameStore` (`:38`) with `define`/`redefine`/`lookup`/`target_text`/`has`/`remove`/`count`/`list_names`; free functions `name_target_range:118`, `name_target_refs:126`, `validate_name:141`, `normalize_target:162`. |
| `src/app/office/sheets/sheets_app.spl` | `SheetsApp.navigate_to:165` — hidden-row-aware cursor, scan loop at `:201`. |
| `src/app/office/interactive.spl` | Terminal Calc editor: `hide <row>` / `unhide <row>` commands (`:152-162`), `_tui_move:220` with its own hidden-row scan at `:234`. |
| `src/app/office/gui.spl` | `_sheet_gui_move_within_bounds:1770`, consumed at `:1838`. |
| `src/app/office/sheets/math_bridge.spl` | Statistics bridge into `std`. |
| `src/app/office/render_adapter.spl` | `office_render` adapter dispatch. |

## Invariants the specs now pin

- **Recalc runs in dependency order.** `12e908dd279` — `_ff_dep_plan` topologically
  orders formula cells before evaluation. Spec:
  `test/01_unit/app/office/sheets/formula_chain_order_spec.spl`.
- **Cycles yield `#CIRC!`, never a number.** `8ed78bb0bf7` — Kahn peeling; cells on
  or reaching a cycle cache `#CIRC!` *without being evaluated at all*
  (`file_formats.spl:712-718`). Spec: `formula_circular_recalc_spec.spl`.
- **All three cursor paths agree on hidden rows.** `10da1bf0f786` — `navigate_to`,
  `_tui_move`, `_sheet_gui_move_within_bounds`. Defect-CLASS spec:
  `test/01_unit/app/office/cursor_hidden_row_invariant_spec.spl` (see state
  below), plus `sheets/sheets_app_hidden_row_nav_spec.spl`.
- **Autofill never invents values.** `6ae2baad0ec` — when no pattern is detected,
  `detect_fill_pattern` falls back to `CopyCycle` (`fill_series.spl:34,42,52,84`),
  which repeats the seed verbatim.
- **Names are validated against A1 collisions and R1C1 reservations.**
  `5d26fefc65c` — `validate_name`.

## Traps

- **The `Range1` A1 collision.** `validate_name` rejects any candidate for which
  `parse_cell_ref(trimmed) != nil`. Because A1 columns are multi-letter, an
  ordinary-looking name like `Range1` parses as column `RANGE` row `1` and is
  rejected. Do not "fix" this by loosening the check — a name that is also a
  valid reference is genuinely ambiguous. `R` and `C` are separately reserved
  for R1C1.
- **`MAX_EVAL_DEPTH = 64` silently caches a plausible WRONG value.** Before
  `12e908dd279`, `_resolve_cell_value` recursed through unevaluated dependencies;
  any chain longer than ~33 hops hit the bound, and the bound value was cached as
  the cell's display. Measured symptom: 27 of 59 cells in one chain read `33` and
  looked entirely reasonable. Rationale is written in-file at
  `file_formats.spl:674-683,731`. Anything that reintroduces
  evaluate-on-demand recursion reintroduces this.
- **Hidden-row indexing is 1-based against 0-based row indices.** Every call site
  is `sheet.is_row_hidden((row + 1).to_i64())` — `sheets_app.spl:201`,
  `interactive.spl:72,234`, `formula.spl:2040,2075`. The base mismatch is
  documented at `sheets_app.spl:183`. An off-by-one here skips the wrong row and
  still "works" for most fixtures.
- **Three cursor paths, one invariant.** GUI, TUI and `SheetsApp` each implement
  their own skip loop. A hidden-row change must touch all three or the
  defect-class spec above is the only thing that will notice.

## Deliberately unwired integration point

Named ranges are **not** wired into the formula engine. `grep NameStore
src/app/office/sheets/formula.spl` returns nothing — verified 2026-08-18. The
intended seams are `resolve_cell_value` (`formula.spl:8652`) and
`resolve_cell_range` (`:8687`): a name would be resolved through
`name_target_refs` / `name_target_range` before A1 parsing. This was left out on
purpose to keep `5d26fefc65c` reviewable; whoever wires it owns the recursion
question (a name whose target is itself a formula) against the `MAX_EVAL_DEPTH`
trap above.

## KNOWN DEFECT — read this before writing any office spec

`doc/08_tracking/bug/interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`:
under the **interpreter**, binding a class-typed element out of a collection and
mutating it loses the write.

`Workbook.active()` (`sheets/spreadsheet.spl:245-247`) returns
`me.sheets[me.active_sheet]` — exactly that shape. A spec that does

```
val sh = wb.active()
sh.set_cell(...)          # write is LOST under the interpreter
```

will read back stale data and look like an office bug. It is not. Work through
the owning aggregate (index into `wb.sheets` at each mutation, or drive a `Sheet`
constructed directly) until the interpreter defect is fixed. This is the single
highest-cost trap in this area.

## Honest state (2026-08-18)

- `test/01_unit/app/office/cursor_hidden_row_invariant_spec.spl` is **RED**, for
  the `Workbook.active()` reason above — the production code is correct, the
  spec cannot express it under the interpreter. *(Red status reported by the
  session that landed it; not re-run here — this documentation task ran under a
  no-`bin/simple` constraint.)*
- `office_suite_spec` has one failure, "loads slides", `undefined field ...
  'layout' on Dict`, which regressed on 2026-08-17 and **has no owner**.
  *(Reported, not verified here.)*

## Fixes landed 2026-08-17/18

| Commit | Fix |
|---|---|
| `12e908dd279` | recalc dependency order (correctness) |
| `8ed78bb0bf7` | `#CIRC!` circular-reference detection |
| `10da1bf0f786` | `SheetsApp.navigate_to` landed the cursor on hidden rows |
| `33d242cf0e1c` | `parse_inline_spans` never returned its declared result |
| `7c7079bf63c9` | `office_render` silently rendered the suite index for an unknown adapter name |
| `675aa70a219` | `math_bridge` imported undefined `variance_sample`; correct symbol is `var_sample` |

Features: `6ae2baad0ec` (fill series), `5d26fefc65c` (named ranges),
`17aa03de98d3` (hide/unhide TUI commands).

## Affected layers

- [test_runner layer expert](../../layer_expert/test_runner/skill.md) — carries
  the spec-authoring form of the class-element-copy trap.

## Update Rule

After research, requirements, architecture, design, implementation, verification
or release work changes `src/app/office/`, refresh the module map, invariants and
traps here BEFORE committing.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
