# Current compiler environment identity

Source: `test/01_unit/compiler/driver/source_analysis_environment_fresh_v1_spec.spl`.

In a serial test, capture the existing runtime-provider environment, create a private provider artifact, and populate the legacy identity memo. Observe the snapshot API environment, replace provider bytes at the same path, then observe it again. Restore the environment and delete the artifact before assertions. Require changed current compiler identity with unchanged environment configuration and unchanged legacy memo result. A second scenario replaces equal-length source bytes and requires a changed canonical uncached tree fingerprint.

Status: **NOT_RUN**. These are authored runtime obligations requiring an admitted compiler/ABI receipt; there is no synthetic identity fallback. No warm-latency/RSS or concurrent filesystem-snapshot guarantee is claimed.
