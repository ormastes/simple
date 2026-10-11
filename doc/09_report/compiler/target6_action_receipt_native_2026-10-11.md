# Target 6 native binary action receipt admission (2026-10-11)

## Failure and repair

The first admitted Stage2 LLVM no-stub action fixture built 48 native modules but failed before creating an action receipt. Fresh-root `strace` showed the binary object was published and verified. A GDB write-syscall backtrace placed the runtime invalid-array-handle diagnostic in `rt_len`, called from `text_to_utf8_bytes` and `sha256_text(binary_object_action_encode_v1(action))`. The temporary encoded text was not accepted as a registered handle by that native path. The detailed [compiler/runtime defect](../../08_tracking/bug/target6_action_digest_temporary_text_len_abi_2026-10-11.md) remains open beyond this owner.

The action digest now binds the canonical encoded text locally and hashes `encoded.bytes()` through `sha256_u8_hex`. This keeps the SHA-256 input as the exact encoded UTF-8 bytes while avoiding the failing temporary-text conversion. The unit spec asserts equality with `sha256_text(binary_object_action_encode_v1(action))` for the interpreter lane when a full runner is available.

## Executable evidence

The final no-stub Stage2 LLVM entry-closure build linked 38 objects from a 48-module closure. Its fresh-root executable printed `PASS binary object action receipt`, exit 0. It checked CAS object publication, receipt publication and readback, identical-publisher convergence, a different object rejected as `race_conflict`, a missing CAS object rejected as `object_missing`, unchanged original receipt after both refusals, and equal shadow comparison. The executable is 115,096 bytes, SHA-256 `2bac623a238248f082a7e3086922ab73c756046348c88774c5718fcf6706e0e3`. Build log: `/tmp/simple-target6-action-receipt-conflict-build-20261012.log`. The short fresh-root run reported 2,100 KiB peak RSS; elapsed time rounded to 0.00 s and is not a performance claim.

## Limits

The Stage2 tool has no `run` or `test` command, so the authored unit SPipe case is not executed. This is a focused receipt gate. Full V3 package graph publication, ordinary CLI warm linking, realistic native p95/RSS cohorts, Item 5 provider demand loading, and release qualification remain open.
