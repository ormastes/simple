# Target profile policy

Specs: `target_profile_spec.spl`, `target_profile_cache_spec.spl`, and updated
`compile_options_normalization_spec.spl` / `xray_policy_spec.spl`.

Bounded native production projections PASS optimization/profile independence,
managed requested-versus-unavailable policy, ordinary defaults, explicit opt-out,
release/XRay refusal, contradictory CLI selection, SHA-256 cache identity,
legacy-key invalidation, and no-op cache separation. The original normalizer
fails the optimized-development assertion.

The full-import SSpec files are UNRUN. Full CLI/manager/bootstrap and actual
observer admission remain unverified. See the canonical bug report
`doc/08_tracking/bug/compile_target_profile_optimization_coupling_2026_11_14.md`.
