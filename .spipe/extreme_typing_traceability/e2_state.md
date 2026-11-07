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

2026-11-06 (work/r11-xtype-closure-20261106): Unknown denial ACTIVE at a
denying profile under SIMPLE_EXTREME_PUBLIC_API=1, now that E1 collects the
effective export closure; NotExported roots are excluded (`excluded_roots`).
Every unknown root is named in diagnostics. Consequence: Nominal-typed exports
are denied until nominal members are projected. Still deferred: AC-EAPI-005
generated-surface recheck, E4 parity, routes-not-collected paths (allowed with
reason; owner question whether an active denying profile should refuse them).

## 2026-11-07 temporary warn-only default
Owner decision: SIMPLE_EXTREME_PUBLIC_API unset => warn-only at every profile (never denies; cached SMF/no-op admission not refused; one summary warning per module, SIMPLE_EXTREME_PUBLIC_API_VERBOSE=1 for details). =1 keeps profile dispositions; =0 is the explicit off switch. Default flips to deny at robust once E3 stdlib migration lands.
