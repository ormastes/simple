# E2 named rule and publication guard

2026-11-06, work/r10-xtype-e2-20261106 (stacked on the route fix PR #7151).

Landed in source: `api_publication_decision_v1` (pure rule projection),
`api_publication_activation_v1` (explicit SIMPLE_EXTREME_PUBLIC_API=1),
`driver_api_publication_guard_v1`, phase-5 choke point in
`driver_orchestration`, typecheck-pass activation at every profile, refusal of
native no-op and cached-SMF admission at a denying profile.

Verified on the seed: 7/7 spec, mutation fails. Pending Phase 3: full
`compile()` denial on a self-hosted binary. Deferred: Unknown denial (needs E1
export closure), AC-EAPI-005 generated-surface recheck, E4 engine parity.
Open owner question: activation default (REQ-EAPI-003 reads fatal-at-robust
unconditionally; the stdlib is unmigrated).

2026-11-06 (work/r11-xtype-p12-design-20261106): P12 export hardening
designed (docs-only PR, base release/1.0.0, independent of the closure PRs).
AC-EAPI-005 recheck: guard precedes weave_aop(); generated-comment exports are
covered via routes; AOP/postmono-introduced exports are NOT rechecked ->
feature-sized follow-up recorded, nothing partial shipped.
