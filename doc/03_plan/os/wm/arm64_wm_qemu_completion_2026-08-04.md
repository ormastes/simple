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

## Current Resume Gate

Owner: compiler-admission lane. Final reviewer: ARM64 integration owner.

1. Begin with at least 12 GiB free so the 2.6 GiB runtime authority can be
   materialized while retaining the 7 GiB safety floor.
2. Start from a clean, freshly synchronized `origin/main`; do not assume an
   older retained worktree is still current.
3. Start a fresh bounded session. The completed session exhausted its three
   rebuild/admission cycles, so no fourth cycle may be appended to it.
4. Inspect the first instruction in block zero before editing. For the canonical
   fixture (`main -> read_initialized_value()`), it is expected to be `Call`.
   The next repair must keep instruction dispatch in place or use owner-scalar
   projections; avoid passing a `MirInst` aggregate across another method
   boundary. Do not proactively redesign terminators or hardcode the fixture.
5. Add focused owner/scalar and source-boundary coverage before any fresh
   Phase 2 build. Preserve debug-gated before/after markers so the first
   failing instruction sub-boundary is exact.
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
