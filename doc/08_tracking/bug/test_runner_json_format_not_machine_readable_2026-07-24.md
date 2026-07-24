# BUG: test runner JSON format is not machine-readable

## Reproduction

Run a pure-Simple test command with `--format json`. The option is accepted,
but the runner emits human per-file and summary output rather than one JSON
document covering spec, SPL-doctest, and sdoctest results.

## Required behavior

Stdout must contain exactly one final JSON object. Its `success` value must
cover every enabled test lane. Progress and diagnostics belong on stderr.

## Repair status

A six-file subprocess-boundary repair is preserved but not pushed. It avoids
scattered print guards by running a private worker subprocess, capturing its
output, and publishing only a validated final object. Its executable/argv
reconstruction still requires final re-audit, and the authoritative focused
run failed because the repair imported nonexistent `lib.json.parser`; the
canonical pure module is `std.common.json.parser`. No behavioral PASS is claimed.

## Next bounded cycle

Use `cli_current_exe_path`, canonical CLI dispatch, marker-relative worker
arguments, and `std.common.json.parser`; then rerun the single whole-stdout
contract once, obtain high static review, and qualify the same code through a
fresh Stage 4 CLI.
