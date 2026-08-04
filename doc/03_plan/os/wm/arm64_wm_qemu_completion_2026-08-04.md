# ARM64 WM/QEMU Completion Plan

## Objective

Produce admissible live ARM64 SimpleOS window-manager evidence in QEMU without
fabricated runtime stubs, Rust-seed artifacts, or misleading attestation PASS
results. Bootstrap improvements are out of scope unless no admitted compiler
can build the required kernel.

## Current State

- Stable owner-qualified module-global identities and strict stub-debt rejection
  are on `main` in `9f0eb1b81c`.
- Focused module-global regression passed 2/2.
- ARM64 producer receipt-classifier self-tests pass for fabricated and
  unmeasured receipt rejection, but the wrapper updates still need reconciliation
  with current `main`.
- The current canonical compiler is rejected as `rust-seed-or-debug-forbidden`.
- Earlier Phase 2/3 artifacts fail strict LLVM admission in `MirToLlvm` with a
  nil receiver.
- `clang-20`/browser-demo work is owned by a separate lane and does not block
  ARM64-first progress.
- A fresh compiler-admission session completed its three-cycle hard cap after
  the earlier owner-state lane. Each current-main Phase 2 compiler passed
  bootstrap sanity, but the canonical non-entry module-global/native admission
  exited 132 on a progressively later aggregate boundary:
  1. `6471bf9a57` routed flattened `MirBody` construction through its owner.
     Artifact `c09caca6...c13cede2a` still stopped after `function:params` with
     `field access on nil receiver`.
  2. `0e052e5f5f` replaced the flattened `MirType` crossing with scalar LLVM
     return text and unsigned metadata. Artifact `4f9a1373...c13cede2a`
     reached `function:return`, `function:scan`, and `function:started`, then
     stopped before block-label completion.
  3. `b0ea54dc52` projected the nested block ID through the `MirBlock` owner
     and added bootstrap-debug boundary markers. The final artifact reached
     `block:label-after bb0` and `block:instruction-before bb0 index=0`, then
     stopped with `field access on nil receiver` before the first instruction
     completed.
- The final artifact is retained at
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-block-owner-cycle3/stage2/aarch64-apple-darwin/simple`.
  Its full SHA-256 is
  `c5a1cbd8293a70af3b983e1b608109e1e86427e2d424490e7e08bd7350f45caf`.
- Phase 3, the ARM64 attested build, and QEMU evidence were not run because no
  Phase 2 compiler passed functional or native admission.
- A subsequent fresh bounded session also completed its three-cycle cap:
  1. `0005061fe4` changed instruction translation to indexed owner access
     (`[MirInst]` plus index), avoiding a `MirInst` method parameter. Its
     focused regression passed 11/11, but the fresh Phase 2 build stopped
     before sanity with a `SymbolTable.bind_qualified_function` field-type
     inference regression for `qualified_functions`; no candidate was admitted.
     The exact diagnostic was
     `src/compiler/20.hir/hir_types.spl: hir: Unsupported feature: cannot infer field type while lowering SymbolTable.bind_qualified_function: struct 'SymbolTable' field 'qualified_functions'`.
  2. `5687d7fc95` initialized and maintained the qualified/exact symbol indexes.
     Its focused invariant passed 3/3. The broad imported-method spec remains
     blocked before its assertions by the unrelated async-lowering error
     `Future type not found - import std.async.future` (exit 1). The resulting
     compiler passed Phase 2 sanity with SHA-256
     `c053c5c395c02c9d9f3f24b4c2fca2219fa893c0eeb64bbbc1f70666ee9d1e9c`;
     admission reached indexed `Call` dispatch, then aborted with a nil receiver
     (exit 132).
  3. `0ae43f73ac` translated bootstrap calls through indexed owner/scalar
     projections. Its focused regression passed 14/14 and Phase 2 sanity was
     stable before and after admission. Canonical admission ran once and ended
     with exit 134 immediately after `block:terminator-before bb0`; indexed
     `Call` translation and `block:instruction-after bb0 index=0` succeeded.
     The trace tail was `instruction:call` -> `call:entry` -> `call:matched` ->
     `call:dest present=true` -> `call:callee` -> `call:emit present=true` ->
     `block:instruction-after bb0 index=0` -> `block:terminator-before bb0` ->
     `panic`; there was no terminator-after marker.
- The final artifact is retained at
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-indexed-call-cycle3/stage2/aarch64-apple-darwin/simple`
  with SHA-256
  `c6bfe36029b0f9d96055b7e9b0179a9dfd3d2ccfe25f87a67601910b1e39ffd6`.
  Its exact admission log is
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-indexed-call-cycle3/admission/bootstrap_nonentry_module_global/native-build.log`.
- Phase 3, the ARM64 attested build, and QEMU evidence still were not run.
- A third fresh bounded session completed its three-cycle cap while removing
  the terminator and Ret aggregate crossings. Every cycle passed focused
  coverage and Phase 2 Cranelift sanity, then failed the canonical admission
  exactly once with exit 134:
  1. `6b7f7f634d` introduced indexed `[MirBlock]` terminator dispatch and scalar
     block targets for every terminator variant. Candidate SHA-256
     `a92746cc81f053bfcee9ff7dc8c63079dd3d94288aec402ca1ee36fc8b18bbbb`
     reached `terminator:ret index=0 present=true`, then panicked before Ret
     payload extraction or emission.
  2. `dd1dd05798` moved Ret optional unboxing into the `MirTerminator` owner and
     passed an indexed operand array to LLVM. Candidate SHA-256
     `0f91939aba20160e45d80f8c44aed85b22b6de6fab1b7604331d6647e09ed7fe`
     reached `terminator:ret-operand-kind block=0 index=0`, then panicked before
     the first operand-kind match or emission.
  3. `435855c952` replaced Ret payload transport with `MirBlock`-owned scalar
     projections for nil, Copy/Move local IDs, and every constant family.
     Candidate SHA-256
     `f96696cb80e06225abc5c14b6864f8682e370802f9527702d6678f343a0febb0`
     reached `terminator:ret-scalar-kind index=0 kind=1` and
     `terminator:ret-scalar-local index=0 local=0`, then panicked before the
     first translator-state decision or Ret emission.
- The final retained compiler is
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-ret-scalar-cycle3/stage2/aarch64-apple-darwin/simple`.
  The exact exit-134 admission log is
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-ret-scalar-cycle3/admission/bootstrap_nonentry_module_global/native-build.log`.
- Phase 3, ARM64 attestation/build, and QEMU were not run in this session because
  functional admission never passed. No fourth rebuild/admission cycle is
  permitted in the exhausted session.
- A fourth fresh bounded session exhausted another three-cycle cap while moving
  Ret translation state out of imported class-field reads. Phase 2 Cranelift
  sanity passed in all three cycles, but canonical functional admission failed
  once per cycle:
  1. `e97904af77` added `MirToLlvm` owner getters for return decisions and
     scalar text. Its focused source contract ended 19/20 after the bounded
     attempts and was committed after review without a PASS claim. Candidate
     SHA-256
     `23accc810dd10a09a7f23999b015246ea940a58e894fff621434fbb07136382d`
     regressed to exit 132 after `terminator:kind index=0`, before the first Ret
     marker; the implicit return-type getter was the new pre-marker boundary.
  2. `d907815427` removed those getters and threaded effective return type,
     `_start` status, and return-slot ID as primitives. Its focused source
     contract remained 19/20 after three bounded runs and was committed after
     review without a PASS claim. Candidate SHA-256
     `9895d925101ea283aca1361ada3c7711918dc5c7af10183b5b7fd3389ec29aea`
     exited 134 after `ret-threaded-fallback index=0 required=false`, before
     local value/type selection.
  3. `5b6089d22d` formed the return value text directly as `%l0` and inlined
     source-type selection. Its final focused evidence was 18/19 before the
     reviewed mechanical contract restoration; it was committed without a PASS
     claim or rerun. Candidate SHA-256
     `8bba8a40460ff688702eb846cfc896a4e54ea0edc2289308ef52a3cab44f8a1c`
     exited 139 after `ret-threaded-value index=0 value=%l0`, before
     `ret-threaded-source-type` or Ret emission.
- The final retained compiler is
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-inline-return-cycle3/stage2/aarch64-apple-darwin/simple`.
  The exact exit-139 admission log is
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-inline-return-cycle3/admission/bootstrap_nonentry_module_global/native-build.log`.
- Phase 3, ARM64 attestation/build, and QEMU were not run. Functional admission
  never passed, and the session's three-cycle cap is exhausted.

## Current Resume Gate

Owner: compiler-admission lane. Final reviewer: ARM64 integration owner.

1. Begin with at least 12 GiB free so the 2.6 GiB runtime authority can be
   materialized while retaining the 7 GiB safety floor.
2. Start from a clean, freshly synchronized `origin/main`; do not assume an
   older retained worktree is still current.
3. Start a fresh bounded session. The completed session exhausted its three
   rebuild/admission cycles, so no fourth cycle may be appended to it.
4. Continue at the exact `terminator:ret-threaded-value index=0 value=%l0`
   boundary. `requires_fallback=false` proves local ID 0 has both a declared
   type and a completed definition; the next unobserved operation initializes
   source type with `self.native_int()` before reading ptr/bool/local type maps.
5. Remove that initial `self.native_int()` call. Initialize source type from
   the proven `self.local_types[return_local_id]` scalar text (or thread the
   already-known local type), validate it, then apply ptr and bool scalar
   overrides. Add a marker before each individual access and after final source
   type selection. Preserve the `%l0` value, threaded return type/status, and
   existing fallback decision; do not add another owner getter or aggregate
   return.
6. Only after the focused regression passes, run one fresh Phase 2 build and
   the canonical non-entry module-global/native admission checks once. Phase 3
   or ARM64 QEMU may start only after both pass.

Retained evidence:

- Cycle 2 compact logs and hash report:
  `/private/tmp/simple-phase2-cycle2-evidence-20260804/`
- Final Cycle 3 build, progress, and admission logs:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-return-owner-cycle3/`
- Fresh-session Cycle 1 owner-constructor evidence:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-owner-constructor-cycle1/`
- Fresh-session Cycle 2 scalar-return evidence:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-scalar-return-cycle2/`
- Fresh-session final Cycle 3 block-owner evidence, including the exact
  instruction-boundary admission log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-block-owner-cycle3/`
- Indexed-instruction Cycle 1 build (stopped by the SymbolTable regression):
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-indexed-inst-cycle1/`
- Qualified-symbol Cycle 2 build and retained broad-test blocker:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-symbol-index-cycle2/`
  and
  `/private/tmp/simple-phase2-cycle2-20260804/build/test-evidence/symbol-table-qualified-cycle2/imported-method.log`
  (`imported-method.status` records exit 1).
- Final indexed-Call Cycle 3 build and exact terminator-before admission log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-indexed-call-cycle3/`
- Indexed-terminator Cycle 1 build and Ret-present boundary log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-indexed-terminator-cycle1/`
- Ret-owner Cycle 2 build and indexed operand-kind boundary log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-ret-owner-cycle2/`
- Final scalar-Ret Cycle 3 build, sanity evidence, and exact scalar-local
  admission log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-ret-scalar-cycle3/`
- Return-owner API Cycle 1 build and regressed pre-Ret admission log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-return-owner-api-cycle1/`
- Primitive-threaded Cycle 2 build and fallback-boundary admission log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-threaded-return-cycle2/`
- Final inline-Ret Cycle 3 build, sanity evidence, and exact `%l0` admission
  log:
  `/private/tmp/simple-phase2-cycle2-20260804/build/phase2-inline-return-cycle3/`

## Parallel Lanes

### Lane A — Compiler Admission

Owner: compiler lane.

1. Build or identify a pure-Simple compiler from current `main`.
2. Run the canonical module-global admission check once.
3. Require strict no-stub mode and zero `FABRICATED-NEW` entries.
4. Publish compiler SHA-256 and provenance receipt.

Exit: one compiler passes provenance, module-global, and strict-stub admission.

### Lane B — ARM64 Attestation Reconciliation

Owner: verification-wrapper lane.

1. Reapply the ARM64 wrapper changes on current `main` without overwriting newer
   logic.
2. Persist and hash build diagnostics.
3. Reject fabricated-new and unmeasured-baseline receipts before manifest
   publication.
4. Run the existing receipt-classifier self-test once.

Exit: the wrapper fails closed for every inadmissible fixture and passes the
valid fixture.

### Lane C — ARM64 Kernel and QEMU Evidence

Owner: ARM64 integration lane.

1. Freeze a clean source snapshot after Lanes A and B converge.
2. Build the ARM64 desktop kernel and FAT32 desktop/font image.
3. Verify source/compiler/artifact hashes and zero fabricated stubs.
4. Boot QEMU and capture serial, framebuffer, keyboard, pointer, and WM markers.
5. Write the final evidence report under `doc/09_report/`.

Exit: QEMU boots the admitted artifact and live WM rendering plus input delivery
are evidenced.

## Acceptance Gates

- No Rust seed or debug compiler is admitted.
- `SIMPLE_NO_STUB_FALLBACK=1` is effective; fabricated count is zero.
- Module-global identity regression passes.
- Attestation publishes no manifest for an invalid receipt.
- ARM64 kernel and filesystem image hashes are recorded.
- QEMU serial contains no panic and records production readiness.
- Framebuffer evidence shows the WM; keyboard and pointer events reach visible
  controls.
- Each gate runs at most once after its inputs stabilize; maximum three
  fix/verify cycles per lane.

## Deferred/External

- `clang-20` browser-demo completion belongs to its existing owner.
- x86_64 WM evidence resumes after that dependency lands.
- Release is prohibited until `$verify` reports `STATUS: PASS`.
