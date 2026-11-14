# Startup consumer cache-model transport review

Reviewed provider checkpoint `a6ed6816207` and startup transport commit `1bb180adc54` on 2026-11-15. This review concerns cache-model alignment only.

`driver_target_profile_identity_v1` validates the startup request, then appends the enabled-only `|xray-startup-consumer-v1=on` descriptor to the normalized profile identity. `compile_options_hash_compute` length-frames that complete supplied identity as `target-profile-v1`. The full executable no-op normalization obtains the same shared helper result and rejects invalid policy results.

The existing formal scalar `opts_target_profile_identity` (field50) represents the complete descriptor passed to the compile-options hash. The startup toggle changes this scalar; it does not require an independent field51. The existing field50 visibility theorem applies under its stated unequal-descriptor premise. Empty startup suffix preserves current off keys. This reasoning does not claim that the theorem proves request normalization, producer admission, or actual execution.

`compile_options_hash_compute` has no declaration change in this transport patch. Its reviewed binding remains `4cb7d02d02f47c6741f61015ba68e6c18356df735e01f4efbfd0a84f0999d616`. No binding refresh, model regeneration, Lean build, or native rerun is justified by this hunk. Prior enabled XRay semantic-row descriptor remains inside the existing XRay scalar; profile/observer identity remains present.

This is source/model alignment, not provider admission, startup execution, whole no-op-cache verification, or Phase3 qualification. Those remain owned by the provider and bootstrap lanes.
