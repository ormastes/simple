# `proton_session_plan_command_spec.spl`: `stderr == ""` fails because `bin/simple run` emits style-lint warnings to stderr

**Date:** 2026-07-20
**Component:** `bin/simple run` diagnostic-warning output (style-lint
"Avoid 'self.'" notes) leaking to stderr during ordinary execution
**Severity:** Low — single example, single trailing assertion
**Found by:** whole-suite triage campaign,
`test/02_integration/app/proton_session_plan_command_spec.spl`

## Symptom

```simple
val (stdout, stderr, code) = rt_process_run("bin/simple", ["run", "src/app/proton_session_plan/main.spl"])
...
expect(stderr).to_equal("")
```

fails: `stderr` is not empty. Actual content includes compiler style-lint
notes such as:

```
info: Common mistake detected: See error message for details
 --> src/compiler/00.common/driver_core_types.spl:19:12
   |
19 |         ...
```

(a "self." usage style note, part of the widespread deprecated-generics/
`self.`-style warning noise seen across many specs' subprocess output in
this triage pass — the same class of warning appears in nearly every
manually-reproduced subprocess call during this campaign). The command
itself succeeds (`code == 0`, all `stdout` content checks presumably pass —
only the trailing `stderr == ""` check is reported failing).

## Root-cause hypothesis

`bin/simple run` on this deployed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, a Rust-seed build) emits
lint/style diagnostics to stderr as part of ordinary compilation for
essentially any invocation touching enough of the compiler's own source
(here, `proton_session_plan/main.spl`'s dependency graph reaches
`driver_core_types.spl`, which trips a style lint). Whether this is
intended behavior (diagnostics-by-default) or should be suppressed for
plain `run` (as opposed to `lint`/`check`) wasn't determined in this pass.

## Note

Spec left unmodified — the `stderr == ""` contract is a reasonable thing to
want for a "clean" CLI plan-printing command; whether the fix is
suppressing lint noise from `run` globally, or scoping it away from this
app's dependency chain, needs product input.
