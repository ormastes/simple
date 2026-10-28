# Phase2 compact RTI drops imported generic Result and Optional declaration owners

- **ID:** BUG-2026-10-27-PHASE2-COMPACT-RTI-IMPORTED-OPTIONAL-RESULT
- **Status:** OPEN; workaround diagnostic only; bug DB reconciliation pending.
- **Severity:** P1 for the lockless-map native acceptance path; broader compiler impact is still being scoped.
- **Owner:** phase2 compiler RTI/import owner (parent to assign).

## Reproduction

The exact diagnostic producer is `/tmp/scv-phase2-current-rebase-20261027/phase2/simple`, SHA-256 `9d202a662186f5e478381465ca357f259a84a5910285256a0945c2577fb2f73f`. Attempt 4 bound worktree commit `2eadc5c14776b92f3d278616db368e20074a9bf6`, SCV source snapshot `scv-revision-v1-f257f9c3deb2361bd9984eca75d77bdd1b52f5480d28a2ee79ddfd5e44f2cc35`, Cranelift, and `core-c-bootstrap` runtime path `/tmp/simple-sol-phase2-sanity-20261027/runtime`; the runtime source resolver was pointed at the worktree by `SIMPLE_PROJECT_ROOT`. A native build of `test/fixtures/lockless_map_i64/native_contract.spl` reached MIR, then failed on imported generic payload bindings and AsyncRef record owners:

- `TaskPollResult<Result<i64, AsyncRefError>>` payload binders reported `E-RTI-004: no local symbol`.
- MIR then reported `field 'token' is absent from exact value layout ... AsyncSubscriptionI64` and `ring_id`, `slot`, and `generation` absent from the resolved AsyncRefI64 layout.
- Imported Result/Optional matching also reported incomplete declaration ownership.

The full native build log is `/tmp/lockless-map-native-20261027/red-build4.log`. It is a compiler/MIR failure, not a behavioral test failure. The fixture did not execute and no native output was produced. Host HIR and frontend caches for attempt 4 were directed under `/tmp/lockless-map-native-20261027/isolated-cache`; shared `~/.cache/simple` was preserved on that attempt.

The adjacent RTI investigation is `/tmp/simple-fix-retained-enum-owner-20261027/doc/08_tracking/bug/compact_declaration_rti_rows_missing_imported_optional_record_2026_10_27.md`, with evidence under `/tmp/retained-enum-owner-20261027` and additional old-producer reds under `/tmp/retained-enum-owner-tdd-red-20261027`. That report identifies a likely missing compact provider callable-signature row path. This lockless-map report records the specific imported generic `TaskPollResult` and AsyncRef record symptom; it does not claim the adjacent authored repair fixes this failure.

## Temporary workaround and recovery

`test/fixtures/lockless_map_i64/core_native_contract.spl` exercises only the real scalar arena core, without imported generic enum or AsyncRef record values. Its marker is immediately above the affected test body. It does not replace, disable, or weaken the full typed fixture or SSpec integration test. The complete typed path remains BLOCKED and unqualified.

The separate core-only diagnostic did compile/link and execute. With an intentional TDD sabotage in `core_try_start_i64` (always returning false), `/tmp/lockless-map-native-20261027/core5/fixture` printed `LOCKLESS_CORE_NATIVE_FAIL:8` and exited 8, matching the fixture's failed first-start assertion. Its binary SHA-256 is `fcf55e988ec42dc5b5a5b628022d007b44e77f29afc9039f52967a318b145f0a`; source fixture SHA-256 is `04c17fd2bba83a4cf33eea809e0f0169663585d89213656ff681312621087ce3`; runtime source `src/runtime/runtime_native.c` SHA-256 is `6c6d1d4c26f9028988ceb2ca247031e3a09cc912bdbe5c5709b196cf6fe49202`. Attempt used the exact phase2 diagnostic compiler above, its core-C bootstrap runtime resolver pointed at this worktree (`rt_dir=/home/yoon/dev/simple-lockless-map-20261027/src/runtime`), and the private core5 cache. This is a genuine RED for the scalar start claim only. It is not GREEN and says nothing about AsyncRef/SimpleRing.

Recovery requires a rebuilt phase2 producer that compiles the original `TaskPollResult.Pending(token)` and `Ready(result)` patterns and preserves the AsyncRefI64/AsyncSubscriptionI64 exact record layouts across module boundaries. Then run the full original native fixture plus the typed AsyncRef/SimpleRing SSpec against that producer, retain raw logs and output hashes, and only afterward remove the scalar-fixture workaround marker in a separate reviewed change.

**Bug DB:** no matching canonical record was found in this checkout's `doc/08_tracking/bug/bug_db.sdn`. Database registration is pending; this report and marker do not claim database coverage.
