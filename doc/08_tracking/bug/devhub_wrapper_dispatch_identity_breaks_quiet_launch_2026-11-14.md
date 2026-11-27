# DevHub POSIX wrapper prints its dispatch identity on every successful launch

- **ID:** devhub_wrapper_dispatch_identity_breaks_quiet_launch_2026-11-14
- **Severity:** P3
- **Status:** fixed
- **Component:** `bin/devhub` (POSIX launcher)
- **Found by:** rerunning `test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl`
  with a stand-in runtime; the spec had been reported as "missing bin/simple".

## Symptom

`bin/devhub --version` and `bin/devhub --help` wrote
`[devhub] mode=ordinary runtime=... receipt=... version=...` to stderr on
every successful launch. The terminal UI spec requires empty stderr for a
successful default launch (`REQ-DEVHUB-TERM-001`, scenarios "should print
DevHub help through the production wrapper" and "should hide successful
launch diagnostics by default and expose them on request"). On a host with an
admitted runtime these scenarios fail. On a host without one, the
exit-127 admission failure came first and hid the problem.

## Root cause

The quiet-launch block (2026-08-11, "clean CLI diagnostics") captures runtime
stderr into a diagnostic file and replays it only on failure, or always under
`--verbose`. The dispatch identity line was added later for
`REQ-DHLM-004` ("ordinary dispatch reports mode, artifact, receipt, and
version"). It was written straight to stderr ahead of that block, so the
quiet path never saw it. The unit test
`test/00_unit/scripts/devhub_windows_launch_modes_test.shs` then pinned the
line on a default success, so the two requirements contradicted each other.

## Fix

The identity line now goes through the diagnostic channel. Under
`--verbose` it is printed before exec. In quiet mode it is written first into
the diagnostic file, so any failed launch replays it with the runtime's own
diagnostics. A successful default launch leaves stderr empty, and
`REQ-DHLM-004` is still reported on request and on every failure. The
exit-127 admission-failure report is unchanged.

## Evidence

- Red: the updated `devhub_windows_launch_modes_test.shs` asserts that a
  default success leaves stderr empty. On the old wrapper it fails with
  `FAIL default success wrote stderr`.
- Green: the same test passes. It now also checks for the identity line
  under `--verbose` and on the exit-41 failure path.
  `devhub_wrapper_runtime_selection_test.shs` still passes.
- Harness (real seed-backed `run`, fixture-admitted runtime). Before the fix,
  `--version` and `--help` each wrote 289 bytes of stderr (the identity line).
  After the fix they write 0 bytes, and `--verbose --version` still shows the
  identity line plus the compiler warnings.

## Follow-up (closed)

`bin/devhub.cmd` used to echo the identity line unconditionally. It now mirrors
`bin/devhub`: the line is echoed to stderr under `--verbose`, otherwise written to
a temp diagnostic file that is replayed to stderr only when the launch exits
non-zero. The gap is closed. Windows cannot run here, so
`test/00_unit/scripts/devhub_windows_launch_modes_test.shs` pins the `.cmd` text
(red before: `FAIL devhub.cmd echoes the identity line unconditionally`).
