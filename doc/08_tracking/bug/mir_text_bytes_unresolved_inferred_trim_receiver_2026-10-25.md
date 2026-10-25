# Inferred text bytes method unresolved in frozen Phase3 producer

Status: OPEN — parser boundary workaround only; compiler resolution remains unqualified.

Frozen source 46772223 with canonical producer 991be8 fails standalone runner MIR at
`src/lib/common/sdn/parser.spl:67:21`: `unresolved method call: bytes`.
Evidence: `/tmp/phase3-resume-20261025-4674/canonical-admission/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/test_runner_build.log`, line 5382.

The call receiver is `val trimmed = source.trim()`. MIR already supports `.bytes()`
on proven text in `method_calls_literals.spl`; its declaration-proof gate can
suppress lowered-local text proof for inferred placeholder declarations. This
is an inference/lowering boundary, not missing UTF-8 support. Donor e7b5c93ba65
narrows authoritative declarations to Str/Named, but its regression was UNRUN;
it is not included here and needs separate compiler-owner qualification.

Parser scans use `std.common.text_bytes.text_to_utf8_bytes`, the existing
`rt_text_to_bytes` provider boundary, instead of method resolution. All seven
scan sites preserve their raw UTF-8 byte semantics; no ASCII conversion,
replacement, encoding negotiation, unchecked cast, or parser grammar change.
Previous unmerged donors eafd3c479fc/f87bf59096d used text_to_bytes; this scoped
repair uses the collision-resistant canonical semantic name and adds real tests.

Regression: `test/01_unit/common/sdn_parser_utf8_bytes_spec.spl` covers trimmed
signed integer parsing, exact Unicode scalar preservation, collection delimiter
scanning, non-ASCII numeric suffix as text, and whole/split UTF-8 byte rejection
by the integer-span owner. Runtime execution is UNRUN: admitted 991be8 is
compiler-only, full CLI timed out, standalone runner fails separate enum metadata
errors. No seed fallback or new runner was used. Removing this workaround needs
actual affected-producer method resolution evidence, not only this parser test.
