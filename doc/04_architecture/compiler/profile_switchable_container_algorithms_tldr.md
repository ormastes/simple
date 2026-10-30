# Profile-switchable containers — TLDR

Item 7 is not qualified on any host. Existing adaptive/runtime/profile and
guarded literal-membership source does not complete general typed lowering or
the two-run profile-to-execution chain. See the
[full architecture](profile_switchable_container_algorithms.md).

- Adaptive Auto/Linear/Hash/Ordered tags describe selection/storage; `.sprof`
  describes workload observations. Neither proves native concurrency or
  lockless progress.
- [One shared capability contract](collection_backend_capabilities.md) serves
  DataFrame plans, adaptive containers and resource registries. Exact operations,
  equality, lifetime, progress, target and memory constrain eligible choices.
- Report no-capture/static-only/constructor-only and directed live migration
  support explicitly. Required unsupported capability diagnoses; advisory Auto
  can retain Original. Legacy locked capture cannot enter a strict hot path.
- Prepare profiles once, with site/source/target/policy identity; no file I/O
  on ready operations. Mutations and provider/layout changes invalidate indexes
  and decisions under exact owner/generation contracts.
- Preserve API/ABI and frozen schema meaning. Native and future pure-Simple
  providers share conformance tests but qualify independently.
- [Design](../../05_design/compiler/profile_switchable_container_algorithms.md),
  [PSC tests](../../03_plan/sys_test/profile_switchable_container_algorithms.md),
  [CBC TDD additions](../../03_plan/sys_test/collection_backend_capabilities.md).
