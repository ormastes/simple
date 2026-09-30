# Positional native-build ignored explicit cache directory

Status: source fix and focused regression prepared; full compiler qualification
is separate. This is a permanent dispatch correction, not a temporary bypass.

The positional `bootstrap_main.run_native_build_bootstrap` route consumed the
value after `--cache-dir` during argument scanning but called CompilerDriver
without binding that directory into `SIMPLE_NATIVE_BUILD_CACHE_DIR`. The driver
reads its cache root from that environment variable. Therefore a copied parent
launch environment could send an explicitly isolated mini build into a sibling
phase cache.

Reported incident: a four-second performance mini, PID 689621, passed its own
`hir-owner-perf-fix-20260930/native-cache` while inheriting the scope-probe
`native-scopeprobe-attempt1/native-cache`. The shared root contained
`native_provider_identity.receipt`, `build_cache.sdn`, and reverse-reference
CURRENT/receipts with 10:18:46–49 timestamps. The manifest referenced the foreign
`hir_owner_name` and `module_path_naming` objects in scope
`s85186de9704e82a1376eb53d06b0ef7f`. The reconstructed launch plan and subsequent
observation demonstrate divergence; without a pre-launch baseline they do not
attribute every root write. The cache was retained and the foreign writer exited.

Evidence supplied by the scope-probe owner:
`D:/dev/simple-linux-early-phase3-20260930/scopeprobe-cache-provenance.md` and
`/mnt/simple-bootstrap-6b2/linux-early-phase3-908-20260930/native-scopeprobe-attempt1/foreign-plan-reconstructed.json`.

Compatibility decision: retain established explicit CLI precedence from
`focused_native_build_effective_cache_dir` and the full CLI. A conflicting
inherited value is overridden for this parent compile; it is not a new admission
error. Omitted CLI selection preserves inherited/default routing. Equivalent
path spellings remain valid without a new canonicalization or tree scan.
The worker dispatcher retains its separate, intentional cache argument contract.
No cache is deleted, migrated, shared across producers or retrospectively admitted.

The positional parent binds before driver construction and restores the exact
nullable previous state before all result-dependent returns. New host access
crosses the SOSIX environment service into existing no-GC runtime owners; app
leaf code introduces no raw runtime environment calls. Restoration also runs
after a returned compile failure. Process termination cannot restore its own
environment, but it cannot change its parent's environment either.

Regressions cover conflicting CLI/environment roots, equivalent paths, omitted
worker routing, separate phase/producer/entry siblings, and absent versus empty
restoration. Native source-projection evidence, when run, qualifies these small
owner bodies and real environment/filesystem effects; it does not qualify a
rebuilt bootstrap compiler or a complete bootstrap.

Verification on 2026-09-30: working-tree direct environment guard PASS. Tiny
native positive/negative projections used producer
`203e210012adcfb21d29571506bfa9e39cb56eb1aabbd89a68c8efd20212533b`
with separate CLI/environment-aligned caches. Three attempts stopped before
compilation at missing journal, missing Git source identity, then no inventoried
sources. The last failure was the fixture's top-level source location: SCV
inventories `src/` and `test/`. The harness now places its source under `src/`,
but the repository's three-attempt limit stopped further native verification.
No test-body execution or native PASS is claimed. Logs and source-hash plans
remain under `/mnt/simple-bootstrap-6b2/native-cache-parent-routing-20260930/`.

An explicitly renewed single validation attempt passed fixture Git inventory
preflight and lowered one HIR module with zero any-escape/enum diagnostics in
each positive/negative case. Both then failed before codegen at
`cold HIR inventory admission failed: inventory-cache-root-invalid`. The
entrypoint publishes at `cwd/build/scv`, while the cold HIR reader uses
`machine_cache_root()`; without `SIMPLE_CACHE`, that reader selects the default
host cache, which the inventory root validator rejects. Native/frontend cache
paths were private, but this additional machine-cache selector was not bound.
The harness now binds `SIMPLE_CACHE` to its own `work/build/scv` and records all
three cache selectors. That correction has not been rerun. The production
default inventory-root discrepancy remains outside this positional-routing fix;
no admission validation is weakened, and no previous cache is removed.
