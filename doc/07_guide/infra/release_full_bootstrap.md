# Full-Bootstrap Prerelease Guide

The canonical release coordinator is `.github/workflows/release.yml`.

## Local preparation

1. Keep unrelated dirty work out of the release change.
2. Run one strict local Linux bootstrap. Since the planner-admission-v2 gate
   (doc/08_tracking/bug/bootstrap_planner_v1_unbound_authorization_2026-08-14.md)
   a bare multi-stage run exits 64 (`reason-receipt-required`); use the
   receipt-chain flow. First the receipt-free Stage 2 trust-root lane, which
   also produces the Stage 3 planner receipt:

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
