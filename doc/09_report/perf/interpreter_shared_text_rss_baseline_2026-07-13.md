# Interpreter Shared Text RSS Baseline

Pre-migration release-seed evidence captured with `/usr/bin/time -v`,
`SIMPLE_LIB=$PWD/src`, and the repository at the current shared-text design
boundary.

| Fixture | Exit | Output | Elapsed | Max RSS |
|---|---:|---|---:|---:|
| `test/fixtures/parser_token_text_scaling/main.spl` | 3 (expected absolute perf failure) | `12869 29582` | 46.72s | 200,292 KiB |
| `test/fixtures/interpreter_shared_text_rss/main.spl` | 0 | `10000 152352` | 3.14s | 449,272 KiB |

Post-migration limits (110% rounded down to whole KiB):

- Parser: 220,321 KiB.
- Distinct short text: 494,199 KiB.

The first attempted short-text workload retained 50,000 values and exceeded
the 90-second fixture bound, so it was rejected before baseline capture. The
accepted fixture retains 10,000 distinct strings and must remain byte-for-byte
identical for the post-migration comparison.

The parser timing baseline remains the previously reviewed 27.631s for the
22 KiB timed region. This report's parser elapsed/output is RSS-run context and
does not reset that timing baseline.
