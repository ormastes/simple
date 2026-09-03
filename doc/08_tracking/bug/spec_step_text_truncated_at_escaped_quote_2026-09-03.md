# Generated `step("...")` text is truncated at the first escaped quote, producing unparseable specs

- Date: 2026-09-03
- Status: PARTIALLY FIXED (4 devhub files repaired in `6e9e35904b3`; 6+ other files still broken)
- Platform: platform-independent (source-content defect)

## Symptom

Specs whose `it "..."` description contains an escaped quote carry a mirrored
`step(...)` line cut off at that quote, e.g.

```simple
it "bare alias -> bucket-listing target (bucket=\"\", key=\"\")":
    step("bare alias -> bucket-listing target (bucket=\")
```

The `step` argument is an unterminated string literal, so the whole file fails
to parse:

```
error: compile failed: parse: ... Unexpected token: expected expression,
       found Error("Unterminated f-string")
error: test-runner: spec executed nothing (parse-error)
```

Zero examples run, and the runner reports `1 total, 0 passed, 1 failed` —
which reads like one failing assertion rather than a whole dead file.

## Detection

```sh
grep -rn 'step(".*\\")$' test/ src/
```

## Fixed here (devhub scope only)

`test/01_unit/app/devhub/{storage_addr,adapter_jira_curl,aws_sigv4,email_translate}_spec.spl`
— 13 lines restored to the exact `it` literal. Measured after: 19/19, 32/32,
14/14, 74/74 pass (all four previously executed 0 examples).

## Still broken (out of devhub scope, unverified)

- `test/01_unit/app/cli/sound_cmd_pattern_spec.spl:124`
- `test/01_unit/app/io/run_sdn_lints_profile_spec.spl:37,47`
- `test/01_unit/app/office/sheets/formula_ref2_spec.spl:177,182,197`
- `test/01_unit/app/office/word/protection_spec.spl:122`
- `test/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.spl`
- `test/01_unit/compiler/backend/svmg_lowering_spec.spl`

## Root cause (suspected, not proven)

The spec-text generator that mirrors an `it` description into a leading
`step(...)` splits the description on `"` without honouring backslash escapes.
Fixing the generator, not just the emitted files, is required — otherwise the
next regeneration reintroduces all of these. See also
`spec_gen_flattens_output_and_silently_drops_specs_2026-08-18.md`.
