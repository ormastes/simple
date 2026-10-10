# Persistent Package/Module Index Compile Optimization: Acceptance Research

## Scope and immutable inspection point

This appendix records source-level research for the full persistent package
index acceptance contract. Inspection used branch
`work/item6-acceptance-contract-20261010` at immutable base
`c7f8d22ae14327a8d3bcddef809e19503823b1e7` (2026-10-10). The isolated
worktree is `C:/dev/simple-item6-acceptance-contract-20261010`; this lane owns
only this research file and
`doc/03_plan/sys_test/persistent_smf_package_index.md`. The canonical
executable remains `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`.
No runtime/build was attempted and no production test result is claimed.

The exact 44 scenario names, requirement mapping, concrete fixture mutations,
evidence, production owners and current gaps are in the companion test plan's
Acceptance Matrix. This appendix explains the code evidence behind those
owners and gaps.

## Existing production surfaces

The package-index implementation is concentrated under
`src/compiler/80.driver/cache/`:

- `package_module_index.spl` owns immutable generation validation, encoding,
  reading, conditional publication and invalidation. Relevant functions are
  `package_module_index_read_current_v1`,
  `package_module_index_publish_v1`,
  `package_module_index_publish_if_current_v1`,
  `package_module_index_invalidate_v1`, and
  `package_module_index_invalidate_changes_v1`.
- `package_module_index_builder.spl` builds a generation from caller-supplied
  inventory/metadata through `package_module_index_build_from_inventory_v1`.
- `package_index_route.spl` admits the current generation, selects a requested
  entry closure, compares prior/current state, creates dirty records, and
  returns ordered work through `package_index_route_current_v1` and related
  route functions.
- `package_tldr_metadata.spl` owns `ConfigVariantKeyV1`, TLDR header and SMF
  validation/admission, section selection, and
  `package_tldr_early_cutoff_v1`.
- `package_archive_cache.spl` owns action/archive receipt validation, archive
  loading, and SCC publication. `package_scc_scheduler.spl` owns SCC grouping,
  dirty closure and schedule construction.
- `cache/daemon/package_daemon_session.spl` provides a session model that
  admits and holds an index generation. The model's presence alone does not
  show that all daemon request/workspace paths use it.

Production integration is in `driver_source_pipeline_loading.spl` and
`driver_pipeline_lowering.spl`. The former calls the package route and can
reject failed admission instead of source fallback on that route. It also
contains path-based source read/closure scan helpers. The latter consumes
demand dirty modules and archived MIR. Therefore the remaining requirement is
to instrument the actual source boundary and prove all production entrypoints
use the admitted route; helper-level owner reports cannot establish whole
compiler no-scan behavior.

`src/lib/scv/compile_snapshot.spl` provides `ScvCompileSnapshotV1` admission,
inventory/materialization, staged publication and open/validation functions.
Compiler callers include cold inventory/HIR publication and driver build/HIR
paths. This establishes usable snapshot primitives, not an exclusive
`ScvFrozenSourceProviderV1`: the compile path still has path-based reads and the
canonical acceptance spec requires proof that every post-admission source open
is rooted in the frozen snapshot.

## Concrete implementation and evidence gaps

The acceptance contract names `PackageCompilePlanV1` and
`PackageCompileReceiptV1` as the durable compiler evidence. A repository search
at the base found no production declarations under these exact names. This is
an evidence-binding gap: the contract has not identified an equivalent
production artifact shape and producer that proves the required fields; it is
not by itself proof that no equivalent capability exists. Similarly,
`ScvFrozenSourceProviderV1` and `ScvCompileBridgeReceiptV1` are names in spec
assertions, not names found in compiler/library declarations. Acceptance must
bind equivalent production source-read ownership and bridge evidence explicitly
before counting these capabilities as covered. The checker
`scripts/check/check-persistent-smf-package-index.shs` is a fail-closed wrapper:
it exits 2 unless `build/test-tools/package_index_acceptance` (or the override
binary) exists, then delegates to it. It contains no scenario logic. The
canonical spec calls all 44 scenario names through this boundary; a missing
binary must remain blocked/failing and must not be reported as PASS.

Generated metadata has a specific data-loss boundary: `generated_source_digest`
is carried from cold HIR package output toward TLDR metadata, while
`package_module_index_builder.spl` projects fields into
`PackageModuleIndexEntryV1`, which has no generated-source field; route
transition comparisons also lack that comparison. Thus generated-input/output
identity and undeclared-output denial cannot be accepted from current index
entries, even if producer-side checks or fixture metadata exist. The repair
needs a declared production field and independently selected fixture mutation;
acceptance must not infer the expected value from the checker itself.

The SCV inventory/snapshot implementation proves local primitives but not the
requested cross-system invariants: automatic snapshot admission for ordinary
compile calls, package-index refresh from Git/SCV events, ignored internal
write-set enforcement, lease-safe crash cleanup, diagnostic bridge evidence,
Git-state non-mutation during ordinary compile, or compiler-wide source-open
ownership. The event acceptance helper
`src/app/test/package_index_acceptance_events.spl` calls
`compiler_inventory_refresh_v1` and
`compiler_entrypoint_index_transition_v1`; its integration spec exercises a
committed source change, inventory digest change, and generation advance. It
also tests a binding-only recovery transition. This is real production-owner
coverage for inventory refresh and index binding, but it does not establish
selective package metadata/index refresh or automatic ordinary-compile wiring.
The fixture's `acceptance_event_commit_v1` intentionally commits inside an
isolated test repository, so it does not prove that ordinary automatic compile
leaves user Git state unchanged. Index and archive types carry some SCV
authority fields, but full provenance across plan, action, headers, archives,
output and receipt remains unproved.

Remote content verification also has a production helper:
`compiler.driver.cache.remote.remote_client.remote_lookup_verified`. It checks
producer read policy, namespace/schema/action identity, the locally recomputed
manifest digest, each artifact's SHA-256, and size bounds. The remote integrity
unit spec exercises authentic bytes and several mismatch/poison cases. The
helper returns verified bytes and defers target, dependency, AOP/block-root
validation and local publication to a local owner. Thus byte authentication is
implemented; package-level local admission, graph-nonmutation guarantees,
remote/local build reproducibility, and the full PSI remote scenarios remain
unproved.

Other implemented helpers must be treated as candidates for compiler-bound
acceptance, not acceptance results. Index readers/validators, metadata
admission, archive receipts, invalidation, SCC scheduling, inventory event
refresh, snapshot staging, and remote byte authentication exist. Production
fixture mutation through every owner, boundary counters, controlled crash
injection, measured dispatcher order, full compile evidence binding,
package-level remote admission, and cross-entrypoint runs remain absent or
unverified. A unit test of a helper cannot substitute for a compiled
production acceptance run.

## Design consequence

Use the existing canonical 44 scenario names and fixed requirement IDs. Each
scenario follows the shared manual flow labels:
`Prepare the frozen package fixture`,
`Execute the production compiler scenario`, and
`Verify compiler-bound evidence`. `scripts/check/check-persistent-smf-package-index.shs
--scenario NAME` is the contract entrypoint; `--scope owner` remains
diagnostic-only. The checker must invoke a compiled production owner against
mutated fixtures and validate independently emitted `PackageCompilePlanV1` and
`PackageCompileReceiptV1`. Missing owner, plan, receipt, counters, or provenance
is explicit RED/blocked evidence, never a placeholder success. Stable names and
requirement IDs remain unchanged.

## Evidence reviewed

- `test/03_system/compiler/package_index/persistent_smf_package_index_spec.spl`
  (44 names, steps, assertion fields, and PSI requirement annotations).
- `scripts/check/check-persistent-smf-package-index.shs` (10-line executable
  presence gate and delegation only).
- Compiler cache owners listed above, `driver_source_pipeline_loading.spl`,
  `driver_pipeline_lowering.spl`, and `src/lib/scv/compile_snapshot.spl`.
- Existing design/test-plan artifacts for shared types, fixtures, failure
  rules, and implementation gates; these are intended contracts, not runtime
  evidence.
