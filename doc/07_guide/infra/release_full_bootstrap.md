# Full-Bootstrap Prerelease Guide

The canonical release coordinator is `.github/workflows/release.yml`.

This guide's full platform and release checklist remains required for stable
releases. An RC or beta may use the partial-platform policy below the producer
selection rules: qualify at least one platform binary, explicitly report each
missing or failed platform, and never pass with zero qualified artifacts or a
security/integrity failure. A partial prerelease does not waive the required
build and test evidence for each platform it claims as qualified.

## Select the release compiler

Release preparation starts from the highest **known successful** self-hosted
phase binary available for the target platform. Consult the release producer
selection rules in [the phase ladder guide](toolchain/phase_ladder_ci.md#release-producer-selection).
Do not rebuild already-proven lower phases just because a default pipeline
starts at the seed. When a known-good Phase 3 compiler is available, use that
exact Phase 3 binary to rebuild Phase 3 (P3 -> P3), then build the Phase 4
full CLI from that Phase 3 output and run its required tests. A bootstrap-only
Phase 3 link is not the full CLI or test-runner evidence.

Bind the selected producer to its actual binary digest, phase-specific source
revision/digest, toolchain and runtime identity, and immutable build receipt.
The receipt must identify the Hello source, its successful compile, the emitted
executable digest, and execution output plus exit status. A directory name,
phase banner, `--version`, or success inferred from a different binary does not
establish producer identity or success. Among candidates, select the highest
phase with this evidence, then the most recent qualifying candidate within
that phase. Do not infer current Phase 3 admission from this procedure.

If that candidate is missing or fails a required compatibility or Hello check,
record the failure and make one explicit, bounded fallback choice to the next
known-success candidate that supports the task. Do not trigger an automatic
lower-phase rebuild or Rust-seed fallback. Any new lower-phase bootstrap needs
an explicit reason and its own producer receipt. Freeze the producer bytes for
the run, use private writable outputs/cache, and keep the normal cache policy;
the release rebuild uses LLVM/LLD with 24 build jobs for P3 -> P3 and Phase 4
native builds. Follow any receipt-bound stage-resume command unchanged when it
pins its own worker count. Reuse the existing
`compiler: auto` and `compiler_release: latest` settings in `config/bootstrap.sdn`
where applicable; do not add a second selector configuration.

## Local preparation for stable/full qualification

1. Keep unrelated dirty work out of the release change and select the producer
   using the rules above.
2. Run the strict local qualification for each intended platform from that
   producer. Only when no compatible known-success candidate exists, use the
   bounded explicit fallback above. The planner-admission-v2 gate
   (doc/08_tracking/bug/bootstrap_planner_v1_unbound_authorization_2026-08-14.md)
   requires a receipt-chain flow for any explicitly authorized new stage build;
   a bare multi-stage run exits 64 (`reason-receipt-required`). For that
   fallback, first run the receipt-free Stage 2 trust-root lane, which also
   produces the Stage 3 planner receipt:

   ```bash
   SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
     --full-bootstrap --stop-after-stage2 --backend=cranelift --jobs=2 --no-mcp \
     --produce-stage3-receipt=<stage3-typed-reason>
   ```

   (`<stage3-typed-reason>` must be allow-listed for `//bootstrap:stage3`, e.g.
   `seed-missing` on a fresh checkout; see
   `bootstrap_planner_v2_reason_allowed` in
   `scripts/check/lib/bootstrap-planner-admission-bound.shs`.)

   Then execute the exact `--resume-stage3-from-admitted=... --bootstrap-receipt=...`
   command the lane prints (Stage 3/4 resume pins one thread; do not pass a
   higher `--jobs`), and follow the admitted continuation it emits into Stage 4.
   Keep producer and cache identities separate; do not rewrite or overwrite a
   selected producer while it is building.
   For a Stage 4 admission, produce a `//bootstrap:stage4` receipt with reason
   `release-trust-verification` (see
   doc/03_plan/release/release_1_0_0_rc1_handover_2026-09-07.md §4).

3. Run the stage-4 memory gates:

   ```bash
   sh scripts/check/check-stage4-memory-gate.shs
   sh scripts/check/check-stage4-selfhost-parse-memory.shs
   sh scripts/check/check-stage4-selfhost-parse-memory-multifile.shs
   ```

4. Run the x86_64, AArch64, and RISC-V64 SimpleOS scenarios named by
   `doc/03_plan/sys_test/next_beta_full_bootstrap_simpleos_multiarch.md`.
5. Run the FreeBSD QEMU full-bootstrap wrapper:

   ```bash
   sh scripts/check/check-freebsd-bootstrap-qemu.shs --full
   ```

6. Require `sh scripts/check/check-simpleos-mission-critical-release.shs` to
   print `release_blockers=none`.
7. Run the whole test suite once, then `$verify`.

Do not use the Rust seed, a stale committed runtime, source-only packaging, or
a skipped matrix row as release evidence.

## Local release

After verification PASS, update every canonical version source to the selected
version, update `CHANGELOG.md`, commit with jj, and create the annotated tag.
Do not move an existing tag.

Ask the user before pushing. Push main and tags with `GH_TOKEN` and
`GITHUB_TOKEN` unset when the stored GitHub CLI credential is intended.

## GitHub workflow

The workflow:

- requires tag `v$(cat VERSION)`;
- builds verified Linux, macOS, Windows, and FreeBSD bootstrap packages;
- builds SimpleOS x86_64, AArch64, and RISC-V64 packages;
- retains elapsed time, peak RSS, logs, receipts, and checksums;
- rejects missing or unexpected assets;
- publishes hyphenated versions with `--prerelease`;
- never moves mutable `latest` for a prerelease;
- queries the resulting GitHub Release and verifies its asset inventory.

Manual workflow dispatch runs build/verification only. Publication occurs only
for a matching tag event.

## Failure handling

Keep caches and logs, fix the root cause, and rerun the failed lane. Stop after
three verify/fix cycles for one defect and report the remaining blocker. Never
retag to hide a failed immutable release.
