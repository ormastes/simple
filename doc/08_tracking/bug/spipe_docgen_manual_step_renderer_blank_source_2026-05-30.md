# Bug: spipe-docgen manual-step renderer can blank expanded scenario source

Status: Fixed

**Date:** 2026-05-30
**Area:** `spipe-docgen`, scenario manual rendering
**Status:** Fixed
**Severity:** Medium

## Summary

While continuing `sspec_scenario_manual_capture`, adding a lightweight
manual-step renderer before the folded `Executable SPipe` block caused expanded
scenario bodies to render blank source fences.

Observed output shape for an inline setup expanded by `# @prev("app is open")`:

```markdown
#### user logs in

<details>
<summary>Executable SPipe</summary>

```simple



```

</details>
```

Expected source body:

```simple
user.open_app()
user.enter_login("demo")
```

## Reproduction Sketch

Start from `test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl`, scenario
`expands prev inline setup without rendering Previous label`.

Add a renderer that iterates the metadata-stripped scenario body to derive
manual steps from call-like lines, then prepend that rendered step list before
the executable source block in `render_scenario_body_with_capture`.

## Evidence

- `SIMPLE_LIB=src bin/simple check src/app/spipe_docgen` passed while the
  failing renderer was present.
- `SIMPLE_LIB=src bin/simple test test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl --mode=interpreter`
  failed 12 scenario-body assertions while the renderer was present.
- Backing out the manual-step renderer restored the focused suite to
  `Passed: 29`, `Failed: 0`, `exit_code=0`.

## Cause

The blank source was reproducible without the manual-step renderer. Direct
probes showed `find_scenario_body_by_title` and body collection returned real
source lines, but `expand_prev_scenario_body` and `dedent_lines` produced blank
strings when copying text through `for ... in` array iteration on the
interpreter path.

## Fix

- `expand_prev_scenario_body`, `expand_include_scenario_body`, and
  `dedent_lines` now copy text with indexed loops.
- Existing `@prev`, `@include`, capture, warning, cycle, and folded executable
  assertions pass.
- `SIMPLE_LIB=src bin/simple check src/app/spipe_docgen` passes.
- `SIMPLE_LIB=src bin/simple run test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl`
  reports 29 examples / 0 failures before the known repo-level
  `compiler_driver_create` semantic finalization error.
- Direct probe confirmed the expanded source renders as:

```simple
user.open_app()
user.enter_login("demo")
```

## Related

- `doc/03_plan/sspec_scenario_manual_capture_plan.md`
- `doc/08_tracking/feature/sspec_scenario_manual_requests.md`
