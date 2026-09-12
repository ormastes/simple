# cooperative_namespace_host_prerequisite_v1_spec: next-missing state mismatch

- Status: OPEN (2026-09-12)
- Scope: pre-existing at `48b7465c27c`; NOT caused by the L78-P07 lane (that lane
  touches neither `cooperative_namespace_host_prerequisite_v1.spl` nor this spec).

## Symptom

    bin/simple test test/01_unit/compiler/cache/cooperative_namespace_host_prerequisite_v1_spec.spl
    ✗ keeps production admission closed while descriptor-bound durability is incomplete
      expected CacheCooperativeNamespaceHostPrerequisiteStateV1::QualifiedEvidenceUnavailable
            to equal CacheCooperativeNamespaceHostPrerequisiteStateV1::ImmutableSyncUnavailable
    SPEC FILE VERDICT: ... outcome=ERROR declared>=10 executed=10 passed=9 failed=1

## Cause (analysis, not fixed here)

`cache_cooperative_namespace_host_api_inventory_v1()` reports every
`*_api_present` field `true` and only `qualified_physical_scope: false`, so
`cache_cooperative_namespace_host_next_missing_v1` returns
`QualifiedEvidenceUnavailable`. The spec still expects the older
`ImmutableSyncUnavailable` ordering. One of the two is stale; deciding which is
the owner's call, not this lane's.

## Repro

- worktree `/home/yoon/dev/simple-l78-p07`, branch `work/l78-p07-2026-09-12`
- binary `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 prefix `3d120a6f9ab5704b`
