# Bug: app root `run src/app/main.spl` receives its own script path as an option (stage4)

Date: 2026-06-12
Status: open
Severity: medium (blocks `--dynsmf-status` evidence path; 2 integration its red)

## Symptom

```
$ SIMPLE_LIB="$PWD/src" bin/simple run "$PWD/src/app/main.spl" --dynsmf-status
error: unknown option: /home/.../src/app/main.spl
Simple app root entrypoint
USAGE: simple run src/app/main.spl [options]
```

The app root's arg parser sees the absolute script path as its first
argument and rejects it, so `--dynsmf-status` / `--no-dynsmf` never
reach `dynsmf_startup_session`. Fails identically before and after the
`ui_html` manifest addition (verified 2026-06-12), so it is a stage4
`run` dispatch regression, not a manifest issue.

## Impact

`test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`: the two
`run_app_root_dynsmf` its ("status evidence", "opt-out evidence") fail;
the five in-process its pass (manifest now 7 entries incl. `ui_html`).

## Notes

Related (fixed, inverse direction): `argv_main_spl_suffix_misroute_compiled_apps.md`
— the B7 sweep replaced suffix-skip heuristics with precise per-app
predicates. The app root (`src/app/main.spl`) arg loop likely needs the
same `arg_is_entry_script` treatment for the stage4 `run <abs-path>`
invocation form, where argv retains the script path.

## Repro

`sh -c 'REPO=$(pwd); SIMPLE_LIB="$REPO/src" bin/simple run "$REPO/src/app/main.spl" --dynsmf-status'`
Expected: `dynsmf session=app-root ... loaded=7`. Actual: usage error, exit 0.
