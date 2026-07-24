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

The final bounded Rust-seed contract reached the internal CLI owner but stopped
before wrapper behavior: the seed exceeded its 800-module transitive-import
limit while loading `src/app/cli/theme_sync.spl`. No behavioral PASS is claimed,
and another seed retry is not useful.

## Next bounded cycle

Build one fresh incremental Stage 4 CLI containing the preserved repair, then
run the single whole-stdout contract once through that exact binary. Do not
retry the full CLI through the Rust seed or weaken the aggregate assertions.
