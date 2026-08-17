# `bin/simple test <spec>` emits no pass/fail summary and exits 0 (silent green)

- **Date:** 2026-08-17
- **Status:** OPEN
- **Severity:** HIGH — a spec that never runs is indistinguishable from a spec
  that passes, on the command every session uses as its evidence.

## Symptom (measured)

```
$ nice -n 15 bin/simple test test/01_unit/lib/common/text_advanced_case_conversion_spec.spl
... 1897 lines, all of them warnings ...
$ echo $?
0
```

`grep -E 'Total|Passed|Failed|Suite|[Ss]cenario|assert'` over the captured
stdout+stderr returns **one** line, and it is an unrelated `export use` warning
quotation — there is no result line of any kind. Same shape for
`test/unit/lib/common/text_advanced_case_class_generalization_spec.spl`.

The output that *is* produced is entirely diagnostic noise: `export use *`
lint warnings, `compiler_cross_module_private_symbol_collision` warnings for
`dir_remove_all` / `file_read_bytes` / `shell` / `DebugConfig`, and a
`higher_layer_runtime_family` gc-warning.

## Why this matters

Exit 0 with no summary is read as GREEN by every caller — humans and scripts
alike. Any claim of the form "spec X passes" that was established by running
`bin/simple test X` and checking the exit code is unsupported until this is
fixed. Note the binary here is the Rust seed (`bin/simple` prints the
bootstrap-seed warning), so this may be a seed-only dispatch gap rather than a
defect in the pure-Simple runner.

## Expected

Either a result summary (counts of scenarios run / passed / failed) with a
non-zero exit on failure, or an explicit `ERROR — nothing was run` with a
non-zero exit. A run that executed zero assertions must never exit 0.

## Next step

Determine whether the seed's `test` subcommand actually loads and executes the
spec at all, or only type-checks it. If it only type-checks, the command should
say so.
