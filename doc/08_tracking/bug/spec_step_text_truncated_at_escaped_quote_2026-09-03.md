# Generated `step("...")` text is truncated at the first escaped quote, producing unparseable specs

- Date: 2026-09-03
- Status: SUPERSEDED 2026-11-11 — runner8 triage; generator escape-preservation fix + `step_literal_spec.spl` regression absorbed via merge 9e7e7a526edb, tree-wide clean, production tool verified. See addendum at end.
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

---

## Addendum 2026-11-11 — runner8 P3 triage: SUPERSEDED (fixed + regression absorbed elsewhere)

Re-triaged on release/1.0.0 tip (worktree `simple-p3-runner8-20261111`).

Absorbed by the spec_to_sspec hardening that landed with merge 9e7e7a526edb
(2026-11-07, hir-nominal-generic-owner lane):

- Generator root cause fixed: `src/app/spec_to_sspec/main.spl` `_step_label`
  (lines 60-75) now copies the scenario name as already-encoded literal
  content — the comment at lines 72-74 states the old quote-splitting
  behavior "would corrupt an existing \" escape and change the name".
  `inject_step_flow` (line 130) wraps that preserved label in `step("...")`.
- Regression spec exists: `test/01_unit/app/spec_to_sspec/step_literal_spec.spl`,
  including "preserves escaped quotes and the text after them".

Verification on the seed lane (tracked `bin/simple.exe` @ 46fe8f6b6def):

- Detection grep `step(".*\\")$` over `test/` + `src/`: ZERO matches at tip,
  including every file this doc listed as still broken
  (`sound_cmd_pattern_spec.spl:124`, `run_sdn_lints_profile_spec.spl:37,47`,
  `formula_ref2_spec.spl:177,182,197`, `protection_spec.spl:122`,
  `spec_gen_drop_and_path_spec.spl`, `svmg_lowering_spec.spl` — all now
  carry correctly terminated, escaped `step(...)` lines).
- Production behavior: `simple run src/app/spec_to_sspec/main.spl modernize
  <fixture>` on an `it "keeps \"quoted\" words intact"` scenario emits
  `step("keeps \"quoted\" words intact")` — exit 0, escapes preserved.

Residual (seed lane, separate from this row): the regression spec
`step_literal_spec.spl` itself currently errors on the seed lane with
`error[E1002]: function 'main' not found` — importing
`app.spec_to_sspec.main` flattens in that module's top-level `main()` call
and the seed compile lane rejects it in spec context. That is the known
seed import/flattening divergence family, not the escaping logic; the spec
is expected to admit under the self-hosted binary used by CI.
