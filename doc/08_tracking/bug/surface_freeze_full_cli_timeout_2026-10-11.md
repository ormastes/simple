# Full CLI Phase2 worker expires during surface freeze

## Immutable observation

Source: `a51194b96b5f5ce3fa57670bc62a15c2414388bf`, tree
`71ab4ae6145541aec992e32791b0cea58f898745`.
Producer SHA256: `e6447d0d10f2c8ae552b67da8420a7e581a22bb55f79e4d4e4d30b981f095811`.
Evidence directory:
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/release-phase3-canonical-preparation/attempt3-full-cli-hir-timeout`.
`failure.json` records retained file hashes and original artifact paths.

The full CLI entry closure contains 2479 physical files. Surface construction
completed at 476244 ms; export-origin resolution ran 488073–490238 ms; the last
progress row is surface_freeze start at 490239 ms. No freeze-complete row or HIR
inventory seal was emitted. Worker `0/1@0` returned process-wait timeout `-2`,
claimed=0, sealed=-1, finished=false; its parent killed/reaped it and blocked the
unsealed ledger. Peak observed RSS is 5129116 KiB in monitor mode. This is not
evidence of an RSS kill, memory corruption, or an independently defective freeze.

The actual verifier environment had no
`BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT` override. The canonical script defaults
to 600 seconds and passes `--timeout 600` to native-build. `run_hir_shards` waits
for the worker with that timeout; it is not a fresh 600-second freeze budget.
The final progress row leaves at most about 110 seconds of that deadline, and
less if process-wait timing begins before the build-progress clock. No timeout
owner bug is established: expiry, cleanup, and rejection of unsealed output are
required behavior and remain unchanged.

## Source-level scaling candidate

`ModuleSurfaceBuilder.finish_into` validates aligned alias rows and calls
`module_surfaces_freeze`, which validates them again. For A aliases, each
validation performs A(A−1)/2 duplicate comparisons and A² compatibility-name
comparisons, even for a valid registry. The candidate retains both checks and
all error precedence, but replaces per-row scans with construction-time hash
membership/index lookups and a local seen-name dictionary. Complexity becomes
expected O(A), with O(A) extra scratch entries; adversarial collisions can still
degrade hash lookups. Existing key/value length validation remains.

The compatibility dictionary is alive during construction. Frozen lookup paths
must continue using promoted scalar arrays because their compatibility Dict can
be reclaimed; the candidate does not change those paths, registry ownership,
promotion, lookup ordering, import probes, or persisted identity. It adds no
long-lived index or cached positive validation verdict. Same-target aliases are
valid; duplicate ordered names remain errors, including empty names. Range
errors precede duplicate errors at the same row; earlier-row conflicts precede
later-row duplicates. Missing and conflicting-index messages are preserved.

Freeze also resolves imports through linear alias lookup. This larger cost is
unchanged and may dominate. **Speedup is UNMEASURED; timeout cause is unproven.**
The existing log does not isolate validation from import resolution or other
work inside finish_into. The source change is a scaling candidate, not a claim
that canonical full CLI now meets its budget.

## Verification and bounded reproduction plan

Focused executable regressions add a 4096-alias valid registry, exact error
precedence checks, empty names/empty registry, and same-target aliases to the
existing alignment spec. Existing teardown tests preserve the rule that frozen
lookup never consults the compatibility Dict. Specs/native checks are unexecuted
during the resource hold; no production-readiness or Phase3 PASS is claimed.

After the active wrapper terminates and root assigns capacity (at least 20 GiB
free disk), run one independent full-CLI entry probe using the same immutable
producer, source/SCV/toolchain identity, affinity, worker count, backend, and
monitor-only watchdog. Copy the exact full-CLI command from the retained matrix
receipt into a separate evidence run; change only the explicit internal
`--timeout` to 1800 seconds, with an outer bound of 2100 seconds. Use the already
supported flag; do not edit the canonical default or running wrapper and do not
start a fourth complete Phase2 matrix. Preserve the original failed evidence.
Use a separately owned output/ledger and a documented cache-state recipe;
preserve admitted caches and record whether the probe is cold or warm.

This longer-deadline probe can establish whether the unchanged producer finishes
freeze and identify later phase timings. It cannot establish canonical-budget
PASS or candidate speedup. Compare a subsequently reviewed candidate against the
same fixture/cache state and host using elapsed and peak/steady RSS; p50/p95 and
the optimize skill's joint time/memory criteria require the relevant sample
cohort. Required outcomes remain real compiled objects and sealed inventory;
timeout, partial output, or a skipped phase never count as success.
