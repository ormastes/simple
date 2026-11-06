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

2026-11-06 (work/r11-xtype-closure-20261106): Unknown denial ACTIVE at a
denying profile under SIMPLE_EXTREME_PUBLIC_API=1, now that E1 collects the
effective export closure; NotExported roots are excluded (`excluded_roots`).
Every unknown root is named in diagnostics. Consequence: Nominal-typed exports
are denied until nominal members are projected. Still deferred: AC-EAPI-005
generated-surface recheck, E4 parity, routes-not-collected paths (allowed with
reason; owner question whether an active denying profile should refuse them).
