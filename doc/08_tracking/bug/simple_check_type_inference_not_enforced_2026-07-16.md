# `simple check` does not enforce type inference

**Status:** OPEN
**Severity:** P1 correctness
**Observed:** 2026-07-16

`src/app/cli/check.spl` performs parsing plus focused source-policy checks. It
does not reject general type errors. The compiler driver cannot yet be used as
a truthful replacement: `type_check_impl` is a no-op and the wired HM pass is
warn-only behind `SIMPLE_TYPECHECK_WARN=1`.

The CLI help now says “parse and validate” and no longer advertises
`--show-types` or full inference. The dead duplicate `app.io.cli_check` handler
was removed so there is one behavior owner.

Close this bug only after the driver HM pass runs by default in check mode,
returns typed diagnostics as errors, and a type-invalid fixture fails in both
interpreter and admitted native execution.
