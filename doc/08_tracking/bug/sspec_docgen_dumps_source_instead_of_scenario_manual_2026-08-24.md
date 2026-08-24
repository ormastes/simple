# sspec documentization: analyzer and generator disagree on the step form

- Filed: 2026-08-24
- Components: `src/app/sspec_maintain/source_facts.spl`,
  `src/app/spipe_docgen/spipe_docgen/parser.spl`,
  `src/app/sspec_maintain/documentize.spl`
- Status: **FIXED 2026-08-24** (see Resolution)

## Correction to two earlier diagnoses in this record

This record originally claimed the docgen "emits a raw source dump" and that
`step(...)` calls never reach the manual, with a fix sketch naming
`documentize.spl`. **Both claims were wrong**, and both were written before
reading the generator:

1. `documentize.spl` does not build the manual body at all — it wraps
   provenance and a scorecard around output produced by
   `spipe_docgen` (`main.spl:487`).
2. The generator *does* render `step("...")` calls, as `- <label>` bullets with
   `   - Expected: ...` sub-items, under `## Scenarios`.

The verified root cause is a **contract mismatch between two tools**, recorded
below. The false trail is kept visible so the next reader does not re-derive it.

## Root cause

`extract_sspec_manual_facts` counted a manual line as a visible step only when
it began with `step ` or `1. `, or contained `data-step=`
(`source_facts.spl:434-438`). The canonical generator emits none of those — it
emits `- <label>`, and that bullet form is **deliberate**:
`test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl:249-250` asserts
the ordered `1. ` form must NOT appear.

So every correctly-authored, fully-stepped manual scored `visible_step_count ==
0` and was charged `SSDOC-EVD-002` (-15) for steps that were present and
rendered. `SSDOC-MNT-008` (-20) fired alongside it because no Traceability
section was emitted at all.

Two further rendering defects surfaced while confirming this, both visible in
the generated smux manual:

- **Step labels truncated at an escaped quote.** `step_helper_label_from_source`
  delegated to `extract_quoted_name`, which returns the *first* quoted segment;
  `step("Create session \"main\" at index 0")` rendered as `- Create session \`.
- **Same-line oracle markers leaked into the rendered expected value.**
  `assertion_expected_summary` parsed the line with its trailing comment
  attached, producing
  `` Expected: s.session_index equals `0)  # oracle: index 0 is the first ...` ``.
  This is the same family of collision: `SSDOC-ORA-003` *requires* the marker on
  the same line as the assertion, and the renderer then folded it into the value.

## Resolution

- `source_facts.spl` counts the generator's actual `- <label>` bullets, scoped
  to the `## Scenarios` region so unrelated prose bullets are not counted. Same
  principle as the evidence-block matching directly below it, which already
  carries the comment "Matches what manual_render.spl actually emits". The
  analyzer was changed rather than the generator because the bullet form is
  pinned by an existing test.
- `step_helper_label_from_source` spans the first quote to the last and
  unescapes, instead of taking the first quoted segment. `extract_quoted_name`
  was left alone — it serves describe titles and other callers.
- `assertion_expected_summary` strips a trailing `# oracle:` / `# explained:`
  marker before parsing. Only those two sanctioned markers are removed; a bare
  `#` can legitimately appear inside a string literal.
- `documentize.spl` emits a `## Traceability` section listing the `REQ-` ids the
  spec declares, regenerated in place like the existing provenance block.

## Evidence

Regression examples added to
`test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl` (+ mirror): an
escaped-quote label survives intact, an assertion carrying an oracle marker
renders a clean expected value, and an assertion without one is unchanged. All
three fail before these fixes and pass after.

Measured documentization scores (caches cleared between runs):

| spec | before | after |
|---|---|---|
| `test/01_unit/os/smux_spec.spl` | 91 | **95** |
| `test/01_unit/os/smux/smux_dashboard_spec.spl` | 91 | **95** |
| `test/01_unit/app/llm_caret/multi_caret_manager_spec.spl` | 76 | **84** |

`SSDOC-EVD-002` and `SSDOC-MNT-008` no longer fire on any of them. The residual
deduction is `SSDOC-EVD-001` (visible scenario without retained capture), whose
own suppression policy admits "the assertion itself is the complete typed
evidence" — the correct disposition for pure value-model unit specs, and not
something to fake with a capture.

## Known unrelated red, untouched

`spipe_docgen_scenario_body_spec.spl` carries **16 pre-existing failures**
(45 passed / 16 failed before this change, 48 / 16 after — the 3 added examples
all pass and no existing example regressed). They belong to the capture/evidence
metadata family and are out of scope here.
