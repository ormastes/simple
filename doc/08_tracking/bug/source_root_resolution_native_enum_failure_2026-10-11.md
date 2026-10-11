# Source-root resolution native enum probe failure

Status: open; blocks native admission of the ambiguity correction in PR #2857.

The pure-Simple producer at
`/home/yoon/dev/simple-bootstrap-mir-object-20261011/build/native_probe/combined-fixes/simple`
(SHA256 `67b29c2e79ef945dcea3b07ea1cedfad99892a1e4448108382571b25f1533f4f`)
compiled `test/fixtures/compiler/source_root_resolution_probe.spl` with LLVM,
one thread, entry closure and `SIMPLE_NO_STUB_FALLBACK=1`. The two-object
executable exited 7: the second numbered candidate did not yield the expected
`AMBIGUOUS:overlay/driver` text. The first six assertions passed, including the
first candidate's `Found` payload. This receipt does not yet distinguish enum
transition, pattern matching, payload preservation or formatting as the cause.

The first attempt failed earlier at MIR construction of `Found`, with payload
type mismatch at index 0. An explicit `text` binding on the typed callback
result and returning terminal enum values unchanged allowed native generation.
That build is `build/cuda-policy/source-root-typed-probe`, with log
`build/cuda-policy/source-root-typed-build.log`. The source-level tri-state
contract must remain intact; replacing ambiguity with missing is not a fix.

The third and final bounded diagnostic build succeeded and exited 7, printing
`second-match=AMBIGUOUS:196341791234865`. Thus the `Ambiguous` pattern is selected,
but its text payload is formatted as a numeric value. Whether this originates
in payload handling or the inferred concatenation operand remains unproven.
Artifacts: `build/cuda-policy/source-root-diagnostic-probe` and
`build/cuda-policy/source-root-diagnostic-build.log`. No fourth retry was run.

Acceptance: the native fixture exits zero and prints
`SOURCE_ROOT_RESOLUTION_PASS`; then execute the filesystem resolver spec and
actual disabled bootstrap source/symbol exclusion checks. No full compiler
rebuild was launched by this lane while integration was held for this repair.

Changed producer `e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491`
builds the current eight-assertion owner fixture successfully, but execution
still exits 7 and prints `second-match=AMBIGUOUS:195728911117105`. Assertions
1–6 passed and assertion 8 was not reached. The four removed callback-API
assertions are no longer part of this fixture. Logs:
`build/cuda-policy/source-root-e9e8-{build,run}.log`. No repeat was attempted.
