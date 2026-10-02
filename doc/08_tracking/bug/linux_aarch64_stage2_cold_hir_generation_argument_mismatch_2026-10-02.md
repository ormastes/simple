# Linux aarch64 Stage 2: cold HIR generation call disagrees with its caller

- **Filed:** 2026-10-02
- **Status:** OPEN; Stage 2 sanity fails. The exact lowering defect is not isolated.
- **Platform:** Linux `aarch64-unknown-linux-gnu`, Cranelift Stage 2 built with 20 jobs from release/1.0 base `1ffaf797bab` plus the diagnostic and candidate fix commits in PR #2191.
- **Impact:** The Stage 2 compiler links, but the `p2_add` frontend sanity build fails before admission. No Stage 2 full CLI, test runner, or compiler/interpreter/loader test result follows.

## Measured sequence

The cold HIR caller reads `SIMPLE_SCV_INVENTORY_GENERATION`, parses it as `i64`, and decodes the immutable SCV source inventory. The inventory digest check passes before the failing generation check.

1. At the caller, bounded diagnostic output recorded `raw='2' raw_len=1 parsed=2 admitted=2`. The 11-argument `cold_hir_typed_receipts_from_lowered_sources_v1` then returned `cold-hir-inventory-generation-mismatch`.
2. A diagnostic inside that callee recorded `expected=1018926449 actual=3` while its caller recorded `raw='3' parsed=3 admitted=3` and the same source inventory digest `a7d0b369ee9fae7e479609ce872b1d959eb2d37072ff7ce97b08e13b8e4ef3d2`. The expected scalar changed across the compiled call; the inventory field survived.
3. Commit `87f5140a88a` moved the generation gate before the long receipt call and used a separate two-scalar helper. Its focused interpreter unit test passed (`Results: 3 total, 3 passed, 0 failed`), but the compiled Stage 2 sanity still failed: the caller recorded `raw='5' parsed=5 admitted=5` and the helper returned a mismatch. The helper's received values were not instrumented, so this result does not establish whether argument transport or comparison lowering failed at that shorter boundary.

The Stage 2 binary was rejected on each attempt. The last attempt rebuilt 1,118 modules with 0 reused, linked, and exited with Stage 2 sanity status 2. The bounded three-cycle verify/fix limit has been reached; no fourth build was started.

## Evidence

- Caller diagnostic run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-generation-diagnostic.log`
- Callee diagnostic run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-callee-diagnostic.log`
- Candidate fix run: `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-generation-fix-final.log`
- Focused sanity receipt and log: `/dev/shm/simple-release10-phase2-20261002/output/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env` and `stage2-sanity.env.frontend-bootstrap-0.log` (latest run; earlier versions preserved under the bootstrap attempt archive)
- Focused unit log: `/dev/shm/simple-release10-phase2-20261002/logs/cold-hir-focused-unit.log`
- Rejected executable: `/dev/shm/simple-release10-phase2-20261002/output/stage2/aarch64-unknown-linux-gnu/simple.rejected`

## Next repair session

Reduce the two-scalar generation helper to a standalone compiled Stage 2 probe that logs both arguments and its comparison result, then inspect the AArch64 call and callee machine code. Add a native regression for the demonstrated lowering defect. Keep the generation, inventory digest, and frozen snapshot checks intact. Rebuild from the current release head with separate caches and rerun the canonical Stage 2 admission; the interpreter unit PASS alone is insufficient for release.
