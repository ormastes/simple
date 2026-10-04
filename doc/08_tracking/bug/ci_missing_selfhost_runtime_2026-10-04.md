# CI consumers missing the self-hosted runtime

Main-push jobs at 89fe3b8b2776 failed before their intended work:
Path Normalization tried chmod on absent bin/release/simple (job111334570887),
and cache promotion rejected absent bin/simple (job111334570806). Both workflows
checked out source without provisioning a runtime. Neither failure was caused
by the later zero-file ancestry synchronization PR.

Only those two jobs now reuse scripts/ci/provision-cache-writer-runtime.shs and
the bootstrap object cache setup already used by cache writer workflows. The
provisioner obtains typed bootstrap admission and deploys self-hosted bin/simple;
it does not expose the Rust seed as the normal tool. Path invokes bin/simple
explicitly. Cache promotion keeps its main-only and fail-closed input checks.
No other matrix job or Docker host configuration changes.

The lightweight contract tests setup ordering, required executable checks and
cache setup, and rejects missing/reordered provisioning, stale paths and seed
fallbacks. Actual CI bootstrap/rerun qualification remains pending.

The previous normalize_path.spl fixture printed only a constant. It now calls
the production std.nogc_sync_mut.path owner and exits nonzero on six failures:
duplicate/dot/parent segments, empty paths, relative cancellation, retained
leading parents, absolute-root clamping and backslash conversion. It prints
the expected path only after those checks pass. Runtime qualification of these
assertions remains pending the actual self-hosted CI run.
Promotion request availability is a separate prerequisite and must not become
a vacuous PASS when no request exists. Neither issue is hidden by runtime setup.