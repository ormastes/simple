# BUG: test runner JSON format is not machine-readable

## Reproduction

Run a pure-Simple test command with `--format json`. The option is accepted,
but the runner emits human per-file and summary output rather than one JSON
document covering spec, SPL-doctest, and sdoctest results.

## Required behavior

Stdout must contain exactly one final JSON object. Its `success` value must
cover every enabled test lane. Progress and diagnostics belong on stderr.

## Repair status

A seven-file subprocess-boundary repair is preserved but not pushed. It avoids
scattered print guards by running a private worker subprocess, capturing its
output, and publishing only a validated final object. High static review
accepted its executable ownership, source/compiled argv split, marker-relative
worker args, aggregate success, diagnostic routing, and canonical
`std.common.json.parser` use.

The Rust seed's documented `SIMPLE_MODULE_LIMIT` setting was previously
orphaned from the loader's hardcoded 800-module guard. That bootstrap defect is
source-fixed with default 800, finite per-process overrides, and zero retaining
the documented unlimited meaning. Its focused Rust unit test passes, and the
incremental bootstrap-profile seed build produced SHA-256
`205a6138f63ba65e1f79ea52394bf043285fe937a77b2a41b99f6d78de02f76c`.

One strict invocation-local run with `SIMPLE_MODULE_LIMIT=1200` proved the
effective limit was honored, then stopped before wrapper behavior when the full
CLI closure exceeded 1,200 modules while loading
`src/app/test_runner_new/json_wrapper.spl`. No behavioral PASS is claimed, and
guessing a larger limit for another retry is not qualification.

## Next bounded cycle

Build one fresh incremental Stage 4 CLI containing the preserved repair, then
run the single whole-stdout contract once through that exact binary. Do not
retry the full CLI through the Rust seed or weaken the aggregate assertions.
