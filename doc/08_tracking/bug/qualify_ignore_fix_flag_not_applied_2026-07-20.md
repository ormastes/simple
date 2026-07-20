# `qualify_ignore` app CLI: `--fix` flag doesn't switch mode; JSON output stays `mode:"scan"`

**Date:** 2026-07-20
**Component:** `src/app/qualify_ignore/main.spl` CLI flag handling
**Severity:** Medium — the `--fix` flag appears to be a no-op; only 1 of 5
examples in the spec file fails, but it's the one exercising the actual fix
behavior
**Found by:** whole-suite triage campaign,
`test/02_integration/app/qualify_ignore_log_modes_spec.spl`

## Symptom

```simple
it "supports fix log-mode json":
    _setup_fixture()
    val (out, err, code) = _run_qualify_ignore(["test", "--fix", "--log-mode=json"])
    expect(code).to_equal(0)
    expect(out).to_contain("\"mode\":\"fix\"")
    expect(out).to_contain("\"fixed\":1")
```

Actual `out`:

```json
{"command":"qualify-ignore","status":"issues","mode":"scan","files":1,"issues":1}
```

`mode` is `"scan"` (not `"fix"`) and the envelope has `"issues":1` instead
of `"fixed":1` — passing `--fix` produced identical output to a plain scan.
The tool detected the issue (`"issues":1`) but did not apply the fix
(`--fix` had no observable effect on the output shape).

## Root-cause hypothesis

Not root-caused to the exact flag-parsing/dispatch code in
`src/app/qualify_ignore/main.spl` (time-boxed triage). Either `--fix` isn't
being parsed/recognized at all, or it's parsed but the fix-application
branch isn't wired to change the reported `mode`/perform the fix.

## Note

Spec left unmodified — the assertion describes the intended `--fix`
contract; this is a CLI implementation gap, not a stale test.
