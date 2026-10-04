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
