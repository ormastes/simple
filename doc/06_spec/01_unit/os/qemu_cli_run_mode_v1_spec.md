# Inspect only the requested CLI mode

**Manual draft; executable results and SPipe generation TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_cli_run_mode_v1_spec.spl`.
Requirements: platform REQ-014 and REQ-016.

For default x86_64 and each of the four represented named routes, combine
`--debug-gui` with `--show-plan` and with `--print-command`. The production
option owner must return the explicit unrepresented-GUI-shape diagnostic.
Showing a normal sealed plan would misdescribe the requested mode.

The existing mutually exclusive inspection diagnostic remains unchanged.
Ordinary inspection and execution-only GUI arguments produce no option error.
These pure checks do not launch a CLI or guest. The live CLI-route suite checks
the same ten rejection cases against the actual admitted executable and
requires the specific diagnostic before any build/run output.
