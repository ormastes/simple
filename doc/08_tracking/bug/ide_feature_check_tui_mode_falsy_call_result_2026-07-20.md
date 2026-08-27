# `ide --feature-check --tui`: a call result that should be truthy returns 0

**Date:** 2026-07-20
**Component:** `src/app/ide/main.spl` (or its feature-check TUI rendering
path) — not isolated to an exact line in this pass
**Severity:** Low — 2 of 3 examples in the spec pass; the GUI-mode sibling
example (near-identical assertions, `--gui` instead of `--tui`) passes
cleanly
**Found by:** whole-suite triage campaign,
`test/02_integration/app/ide/ide_feature_check_integration_spec.spl`
(re-run at `timeout 180`, completes in well under that — not a timeout
artifact)

## Symptom

```simple
it "prints the complete TUI feature-check manual through the app entrypoint":
    step("Run the IDE feature-check command in TUI mode")
    val (out, err, code) = _run_ide(["--feature-check", "--tui"])
    expect(code).to_equal(0)

    step("Review the feature-check header and TUI mode")
    expect(out).to_start_with("Simple IDE feature check")
    expect(out).to_contain("mode: tui")
    expect(out).to_contain("capabilities: 5")
    ...
```

fails with `expected call result to be truthy, got 0` — this message text
doesn't come from a plain `to_equal(0)`/`to_contain` matcher visible in the
snippet above, so it's most likely raised inside a later `step()` in this
same example (further down the file, not reproduced here) that checks some
per-capability call result and got `0`/falsy where truthy was expected.
The parallel `--gui` example in the same file (same header/mode/capability-
count assertions, different rendering path) passes, isolating this to
something specific to the `--tui` rendering branch.

## Root-cause hypothesis

Not root-caused to the exact `step()`/assertion or the exact capability
check that returned 0 (time-boxed triage — would require reading further
into the spec body and `src/app/ide/main.spl`'s TUI feature-check renderer
than this pass covered). Flagging the GUI-vs-TUI asymmetry as the concrete
lead for follow-up.

## Note

Spec left unmodified — no evidence of a stale assertion; flagged as a
genuine TUI-path gap.
