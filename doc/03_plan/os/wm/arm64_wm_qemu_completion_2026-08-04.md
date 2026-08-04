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
- A current-main Phase 2 build at `7daa55e42c` reached the final allowed build
  cycle but stopped at the storage guard: materializing the 2.6 GiB frozen
  runtime authority reduced free space from 8.1 GiB to 6.8 GiB. The generated
  copy was removed and 9.4 GiB restored; no new compiler artifact was emitted.
- The preceding Phase 2 artifact (`033e16e5...7eab830`) passed bootstrap sanity
  but is inadmissible: it contains Rust provenance and its canonical
  module-global fixture exits 132 in `MirToLlvm`. The owner-mutation repair for
  that nil receiver is on `main` at `7daa55e42c`, but still needs a fresh build.

## Current Resume Gate

Owner: compiler-admission lane. Final reviewer: ARM64 integration owner.

1. Begin with at least 12 GiB free so the 2.6 GiB runtime authority can be
   materialized while retaining the 7 GiB safety floor.
2. Use the clean current-main worktree at
   `.claude/worktrees/agent-aaf2c9946eded166b`.
3. Resume with one fresh scoped session (the present session exhausted its
   three-cycle cap):

   ```sh
   sh scripts/bootstrap/bootstrap-from-scratch.sh \
     --pure-simple --backend=cranelift \
     --output=build/phase2-arm64-recovery-20260804 \
     --jobs=2 --no-mcp \
     --progress=build/phase2-arm64-recovery-20260804/progress-resume.log
   ```

4. Stop after Phase 2 sanity; retain the artifact and its runtime authority.
5. Run the canonical non-entry module-global and native compiler admission
   checks exactly once. Phase 3 or ARM64 QEMU may start only after both pass.

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
