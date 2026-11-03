# Test-runner environment subgroup — 2026-11-03

Canonical IDs (all remain OPEN):
- di_test_tag_env_not_inherited_by_subprocess_2026-07-02
- env_gated_spec_switches_are_inert_under_test_daemon_2026-08-09
- test_daemon_freezes_env_binary_override_dead_2026-08-02

Source boundary db7b22dabb591d29dd68a55083b421052d51a00c. AUTHORED_UNRUN: no admitted source-matched runner supplied, no runtime RED/GREEN, no bug closure, no compiler build or seed fallback. New work is two focused actual-child regression scenarios and two fixture specs, not a speculative production fix.

## Existing implementation retained

Generic freeze reports describe v1 requests carrying no environment. Current light_protocol.spl has v2 environment-digest/generation fields and matching checks. environment_identity.spl hashes a sorted, length-framed snapshot of every environment pair (except documented shell bookkeeping; forced interpreter mode normalized), using env_list_checked and fail-closed invalid identity. test_runner_client.spl checks caller versus live daemon identity before reuse, revalidates per request, and reroutes mismatches directly. This is a general environment solution, not just the old variable allowlist. Existing environment_identity_spec covers change/absence/order/duplicate/ambiguity and matching; existing test_daemon_env_override_passthrough_spec has real binary override subprocess cases. No duplicate hash identity or override tests added.

The source-only generic freeze repair is not proof that an admitted native process successfully uses that code. Both corresponding canonical records stay OPEN pending current runtime evidence. Old v1 descriptions in bug prose do not erase the current v2 implementation.

DI runners still set SIMPLE_SYSTEM_TEST and SIMPLE_DI_TEST before launching children. The original report hypothesizes stale/incomplete inheritance but does not identify a current source defect with a qualified producer. A replacement environment transport or process-wide mutation rewrite without reproduction would be speculative and is not made here. All existing source unchanged.

## New regression contract

REQ-TEST-ENV-DI-001: child test bodies must observe runner-owned DI flags and the actual compiler.di.di_is_system_test_locked result, irrespective of contradictory inherited caller flags.

The tagged fixture under a /feature/ directory requires system=1,di=1,locked=false. The untagged fixture requires system=1,di=0,locked=true. The latter catches leakage of an exemption. Each performs three real assertions and prints a unique marker after them. Parent requires both exit0 and that marker; --assert-ran is passed. Source/import loading alone cannot provide the marker. Fixtures contain no direct externs and do not set global environment.

The parent uses /usr/bin/env with positional arguments, no shell interpolation, launching the separately admitted full CLI from SIMPLE_TEST_ENV_RUNNER. Only the spawned process receives conflicting initial flags. Missing configured runner fails; it does not fall back. POSIX-only admission profile is explicit. --no-session-daemon, --no-db and --no-cache avoid shared daemon/database/cache state. These scenarios cover the direct runner-to-child boundary, not daemon reuse or v2 protocol handoff. Existing persistent-daemon tests remain separate. No startup or latency claim.

Spec: test/02_integration/app/test_runner/di_environment_subprocess_spec.spl. Manual mirrors under doc/06_spec and is authored, not generated; no zero-stub claim. Fixtures below test/fixtures/test_runner/feature are unique to this lane. No overlap with coverage worker's resume branch or nested-timeout worker's routing specs.

Remaining gates: qualify runner, capture actual failing baseline if present, change source only after current root cause is established, rerun focused cases at most2cycles per cause, require actual docgen zero stubs. Existing environmentidentity tests need not be rewritten. Reviewer /root/astra_enum_review; landing /root/land_source_repairs.

## Source artifact hashes (LF bytes; no execution artifacts)

- `test/02_integration/app/test_runner/di_environment_subprocess_spec.spl`: `b6bc9fcfa63a53f15bf565b869f85ab968765283a841202ffacc0f2bb80ebbd3`
- `test/fixtures/test_runner/feature/di_environment_tagged_spec.spl`: `f8702d859109b9dd5be962a95a91e17e40ca4d9923f185fdb51abc434e752537`
- `test/fixtures/test_runner/feature/di_environment_untagged_spec.spl`: `04540320579ef1b631a804536c5df8ea470638c06e990c9bd5aec5d59310e12a`
