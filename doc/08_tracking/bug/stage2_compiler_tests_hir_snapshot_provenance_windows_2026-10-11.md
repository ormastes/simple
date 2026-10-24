# Stage-2 compiler-tests matrix fails on Windows: cold HIR snapshot admission `snapshot-open-provenance-invalid`

Filed: 2026-10-11
Host: Windows 11 (Git Bash / MSYS2), worktree `C:\q`, `x86_64-pc-windows-msvc`,
LLVM 23.1.1 (`~/.simple/toolchains/llvm-msvc-23.1.1`).
Lane: `bootstrap-windows.sh --strategy=adhoc --incremental-unlimited
--full-bootstrap --stop-after-stage2 --output=build/bootstrap` with
`BOOTSTRAP_STAGE2_TEST_DELEGATE=0` (delegation off; the MC/DC waiver gate is
bypassed by design, see multihost_bootstrap.md).
Sources: release/1.0 @ `c4cd4530c1d` (144 commits behind `b8e4ff6eb04` at the
time; the delta does not touch `src/lib/scv/compile_snapshot.spl`,
`scripts/bootstrap/bootstrap-phase-verification.shs`, or
`src/lib/compiler/driver/`).

## Symptom

Stage 2 itself builds, passes sanity + struct-receiver proofs, and is admitted
(phase2 runtime capsule `0dcd79a5e93de…` published). The post-admission
compiler-tests matrix (phase verification, profile=slim, timeout=7200s) then
fails with `verification_status=1`:

- `module-prerequisite.log`: `compiler snapshot missing or invalid` →
  `compiler_cli_build`/`test_runner_build` rows `UNSUPPORTED
  (full-cli-artifact-not-built)`; 14,012 inventory rows `BLOCKED
  (prerequisite-unavailable)`.
- 77 `module_compile_*` rows `FAIL (worker-failed)` with empty
  per-task diagnostic dirs (workers died before writing logs).
- One row: `source-runtime-authority-changed`.
- Surviving worker stderr (matrix cache `…/module-diagnostics/stage2/0dcd79a5…/`):

  ```
  [hir-reexport-chase-unresolved] facade=lib.nogc_async_mut.io.process_ops item=Option … importer=C:/q/build/scv/snapshots/scv-revision-v1-145f062997740caeed1c75f58b2633a0e437b2d4a6b6a61a86c20798511b09f9/src/lib/nogc_async_mut/io/process_ops.spl …
  [hir-callable-dep-origin-unresolved] owner=lib.nogc_async_mut.io.process_ops dependency=Option: no declaration, re-export hop, or explicit import …
  … (hundreds of Option/Result rows across lib.nogc_async_mut.* / lib.nogc_sync_mut.* facades)
  error: cold HIR snapshot admission failed: snapshot-open-provenance-invalid
  ```

## Cause (established)

`src/lib/scv/compile_snapshot.spl` (~line 260) opens a compile snapshot only
when its `SCV_COMPILE_SNAPSHOT` provenance file has exactly 6 lines with
`lines[5]` starting `count=`; otherwise it returns
`snapshot-open-provenance-invalid`. The matrix's phase-bound builds run against
sources under `build/scv/snapshots/scv-revision-v1-<rev>/` and the candidate
rejects that snapshot's provenance shape, so every cold HIR cache open fails;
the facade `Option`/`Result` resolution cascade and the worker failures follow.
Whether the provenance writer emits a different shape under the matrix's
snapshot driver, or the matrix reuses a snapshot whose provenance belongs to a
different revision, was not isolated (single observation; each full-matrix
repro costs ~7 h).

## Not yet established / suspects

- Whether the provenance mismatch is Windows-specific (e.g. line-ending or
  atomic-rename shape) or revision-binding logic in the matrix's
  scv snapshot setup.
- Whether the Linux/CI matrix currently passes on the same sources; no
  comparison run exists.
- The `source-runtime-authority-changed` row appeared in the same matrix; its
  relation to the provenance failure (cause vs symptom) is unproven.

## Evidence retained (this host)

- `C:/q/build/bootstrap/stage2-compiler-tests/x86_64-pc-windows-msvc/rejection.env`
  (candidate `0dcd79a5e93de…`, `verification_status=1`)
- `…/verification/summary.env` (14,095 rows: 77 FAIL / 0 PASS / 3 UNSUPPORTED /
  14,012 BLOCKED)
- `…/verification/module-prerequisite.log` (`compiler snapshot missing or invalid`)
- `…/cache/module-diagnostics/stage2/0dcd79a5e93de…/*/diagnostics/native-build-stderr-*.log`
  (quoted above)
- Wrapper main log tail: `VERDICT — ABORTED: stage=stage2-compiler-tests exit=1`

These paths are ephemeral build output; the quoted lines above are the durable
record. Related prior art: PR #2884 (hir-cache envelope/typed reader) fixed the
codec shape class in 2026-09; this failure is the scv snapshot provenance
admission, a different layer.

## Suggested next step

Reproduce with the matrix's exact scv snapshot setup on a short path with
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`, dump the `SCV_COMPILE_SNAPSHOT` file that
the matrix's snapshot driver writes, and compare against
`scv_compile_snapshot_provenance_v1(revision_id, commit_id, tree_id,
inventory_digest, inventory_count)` line-by-line before touching the
admission checks. Do not relax the 6-line provenance shape check without a
versioned schema bump; the check is the integrity boundary PR #2884 hardened.
