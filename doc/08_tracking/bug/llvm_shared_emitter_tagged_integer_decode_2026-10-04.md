# LLVM shared emitter loses tagged scalar decoding

Status: OPEN; repair drafted, corrected-producer verification pending.

## Reproduction evidence

Windows bootstrap source `9737d1217bc44439b56bba6c2ef16faaff51bd20`,
seed SHA-256 `7a98ce791c33cc7f7091c46a9cf87bad68b40193d0c09a9332da078ced505c91`.
Both native compilations succeeded. The same nine-case Result/bool fixture
passed all nine with Cranelift (run exit 0). LLVM passed two and failed seven
(run exit 42): record args/config/environment, checked false/true and nested
false/true. Direct question-mark false/true and error propagation passed.

Retained local evidence is under the Windows restart packet
`windows-restart-20261004/result-bool-try-baseline1` and
`windows-restart-20261004/result-bool-try-llvm-baseline1`: `result.env`,
`run.stdout`, input hashes and collector receipts. These are bootstrap
diagnostics, not release admission or whole-suite results.

## Structural cause and repair boundary

The shared LLVM trait emitter's `emit_unbox_int` shifts integer bits by three.
The legacy LLVM instruction arm instead uses `rt_value_unbox_int` on 64-bit
targets. Shared instruction dispatch reaches the former. Tagged booleans and
wide heap-boxed integers therefore cannot safely use its unconditional shift.
Cranelift already calls the tag-aware runtime helper.

Extract the existing legacy decoding into one LLVM helper and call it from
both dispatch paths. Preserve target-width and coercion behavior; do not add
a MIR-only boolean special case that leaves wide integer extraction broken.
Keep the runtime's tagged-true/tagged-false contract unchanged.

## Required verification

- Compile and verify LLVM IR through actual shared instruction dispatch.
- Repeat the failing native fixture with a corrected, hash-bound producer.
- Exercise small integers, wide boxed integers, booleans and applicable
  passthrough/coercion cases across both dispatch paths.
- Rebuild affected LLVM Phase2 output and repeat its policy-handoff Hello.

The LLVM-built Phase2 compiler currently rejects its own encoded native-build
policy with `invalid-internal-argument:invalid-policy`. The scalar defect is
a candidate explanation; the connection remains unverified until the final
step succeeds. Preserve that failure and do not bypass its validator.

## Linux fresh-producer correction, 2026-10-05

The release-branch Linux seed already contained the tag-aware shared unbox
helper, but the existing nine-case native fixture still failed seven cases
with LLVM (exit 42) and passed all nine with Cranelift (exit 0). Exact producer
hash, environment, arguments, counts and preserved logs are recorded in
`build/diagnostic/result-bool-20261005/evidence.json`. This is a bootstrap-only
native diagnostic, not evidence from a general test runner.

Fresh LLVM IR in that directory's `ir/` proves a second mismatch: extracted
Result<bool> payloads call `rt_value_unbox_int`, producing raw 0/1, while both
LLVM ConstBool dispatch paths produce tagged 19/11. The generated equality
instructions therefore compare raw payloads and record fields to tagged
constants. Direct conditions and error propagation pass, explaining why the
earlier unbox-only repair did not fix aggregate and checked-value cases.

The follow-up source repair makes both LLVM ConstBool dispatch paths retain
raw runtime-width 0/1 until explicit runtime boxing, matching Cranelift scalar
semantics. A Rust regression checks false/true constants through actual shared
dispatch and the legacy path. The existing rt_value_bool boundary continues
to produce the runtime's tagged boolean representation.

Status remains OPEN: a canonically rebuilt producer must pass the nine-case
fixture, and rebuilt Phase2 must pass the original policy-handoff sanity.
Neither the failed seed nor its rejected Phase2 artifacts may be admitted.

The first canonical Linux rebuild passed the existing nine-case fixture with
both backends. A ten-case ordinary boolean fixture then exposed five remaining
LLVM failures (ordinary false/true returns, not false/true and equality);
Cranelift passed all ten. These immutable results and runtime archive hashes
are retained in `build/diagnostic/result-bool-20261005-fixed/evidence.json`.
The follow-up repair makes LLVM logical/comparison results, scalar coercion
and boolean function returns use the same raw 0/1 contract. Runtime truthiness
still recognizes tagged false, and explicit boxing still produces tagged
RuntimeValues. Inline byte-set boolean results use the native scalar contract.
`test/04_smoke/native_basic_bool_contract.spl` retains the ten-case regression.
Corrected immutable producer `0ec9d3a1f6fbfac8bf78cb19b9409608f2172cd7d0d003ca6711f1e99ddb3080` passed the Result fixture (9/9), basic boolean fixture (10/10), and runtime representation fixture (7/7) under both LLVM and Cranelift. All six native builds and executions exited 0: 52 positive checks. Producer/runtime hashes, exact argv and output are retained in `build/diagnostic/result-bool-20261005-combined/evidence.json`. The added Rust IR tests have not yet been executed. Full Stage 2 policy admission remains a separate pending gate.
