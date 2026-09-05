# details_summary_rendering_spec

> `details`/`summary` disclosure rendering through Web semantics and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# details_summary_rendering_spec

## Scenario: default authored-summary disclosure marker

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario: disclosure semantics, events, and pixels

The bounded selected profile does not synthesize the user-agent shadow
`summary` for a closed `details` that omits one; it hides that element's
children. The first authored direct `summary`, click toggle, open state, and
nested independent state are implemented.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

Executable source:
`test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl`.
The producer remains canonical HTML/Web layout to `DrawIrComposition` to the
software Engine2D compositor. This manual makes no claim for keyboard
activation, grouped disclosures, or a synthesized shadow summary.
