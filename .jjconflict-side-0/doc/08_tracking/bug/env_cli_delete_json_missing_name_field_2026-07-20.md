# `env` app CLI: `delete --log-mode=json` output missing `"name"` field

**Date:** 2026-07-20
**Component:** `src/app/env/main.spl` (`delete` subcommand, JSON log mode)
**Severity:** Low-Medium — single isolated example, sibling `create`/
`status` JSON-mode examples in the same file pass fine
**Found by:** whole-suite triage campaign,
`test/02_integration/app/env_log_modes_spec.spl` (re-run at `timeout 180`,
completes normally, not a timeout artifact — 5 of 6 examples in this file
pass)

## Symptom

```simple
it "supports delete log-mode json":
    _setup_fixture()
    val (_create_out, _create_err, _create_code) = _run_env(["create", "--name=test-env"])
    val (out, err, code) = _run_env(["delete", "--name=test-env", "--log-mode=json"])
    expect(code).to_equal(0)
    expect(out).to_contain("\"command\":\"delete\"")
    expect(out).to_contain("\"name\":\"test-env\"")
```

fails at the `"name":"test-env"` check: `expected  to contain
"name":"test-env"`. The sibling `create`/`status` JSON-mode examples in the
same file (which assert the same `"command":"<verb>"` +
`"name":"test-env"` shape) both pass, isolating this to the `delete`
subcommand's JSON envelope specifically missing (or differently shaping)
the `name` field.

## Root-cause hypothesis

Not confirmed from source (time-boxed triage; not root-caused to the exact
line in `src/app/env/main.spl`'s delete-JSON formatting path). Given
`create`/`status` both correctly echo `"name":"<value>"` in their JSON
envelopes, this looks like a small, isolated formatting gap specific to the
`delete` verb's JSON output rather than a systemic issue.

## Note

Spec left unmodified — the assertion matches the established `create`/
`status` JSON contract in the same file; fixing this is a `src/app/env/main.spl`
change, not a test change.
