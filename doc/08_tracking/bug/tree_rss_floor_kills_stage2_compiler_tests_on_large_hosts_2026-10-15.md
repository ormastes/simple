# Tree RSS floor kills the Stage 2 compiler-test phase on large hosts (exit 88)

Date: 2026-10-15
Host: Windows 11, 64 GiB RAM (66,865,260 KiB total, ~43 GiB available at start)
Lane: stage2 trust-root bootstrap, `--full-bootstrap --stop-after-stage2`,
12 workers (`--jobs=full`, memory-clamped from 24)

## Observation

`stage2-compiler-tests` was killed by the process-tree RSS watchdog:

```
status=rss-cap-exceeded
exit_status=88
max_rss_kib=5859375      # the historical floor, 5.59 GiB
peak_rss_kib=5862512
budget_ceiling_kib=8388608
```

Only `compiler_version` had run in the phase-verification matrix; the test
phase (build-threads=8, test-workers=4) never produced a result.

## Root cause

`scripts/bootstrap/lib/tree-rss-policy.shs`:

    cap = max(FLOOR 5859375 KiB, (base 3072 MiB + jobs * 96 MiB) * 1024)
    cap = min(cap, host_total * 50%), min(cap, hard ceiling)

For jobs=12 the budget is 4224 MiB < FLOOR, so the FLOOR wins; on a 64 GiB
host the 50% host bound (32 GiB) and the jobs-scaled ceiling (15.7 GiB) are
both far above the floor, so the floor is the operative cap. The floor is a
small-host lower bound, but on large hosts it becomes the effective ceiling.

The budget formula prices a worker at 96 MiB, calibrated for *compile*
workers (measured 57-76 MiB/worker in the header comment). The compiler-test
phase runs full compiler *binaries* as workers (each several hundred MiB),
so the phase's real peak (compile tree + test binaries) exceeds 5.59 GiB on
this host while still being well within physical memory.

## Workaround used

Per-run env knob, admitted under the policy's own ceiling math:

    SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=12582912   # 12 GiB < 15.7 GiB ceiling

## Suggested direction

Distinguish the floor's roles: it should lower-bound the cap on small hosts
but not upper-bound it on hosts where both the jobs-scaled ceiling and the
host-fraction are far higher. Options: (a) apply
`cap = min(max(budget, floor), ceiling, host_fraction)` only when host RAM
is unknown or small (e.g. host_total below some threshold); (b) let the test
phase resolve its cap from its own worker model (test workers priced like
compiler binaries, not compile workers); (c) keep the floor but raise the
per-worker price for non-compile phases. Any change must keep the documented
small-host protection and the watchdog's own ceiling recompute in
process-tree-rss-watchdog.pl consistent.

## Status (2026-10-16): fixed — option (b), phase-priced cap

`bootstrap_tree_rss_phase_cap_kib` (tree-rss-policy.shs) prices the Stage 2
compiler-tests phase by the host: `host_pct` of RAM clamped to
[floor, jobs-scaled ceiling]. bootstrap-from-scratch.sh uses it for that
phase only when no explicit `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` is set.
64 GiB host, 8 build threads: cap 16 GiB (was the 5.59 GiB floor). Small
hosts keep the host fraction (16 GB host -> 8,000,000 KiB). Selftest: 31
fixtures PASS incl. both phase-cap cases.

Note: on Windows the watchdog's "RSS" is the job object's commit charge
(`peak_job_commit_kib`), not working set; sampled working set of the same
builds stayed ~1-3 GiB while commit reached 5.9 GiB.

## Recurrence (2026-10-31, Linux aarch64 121 GiB host): phase cap clamps to the 48 GiB static ceiling

The 2026-10-16 fix prices the phase at `host_pct` of RAM (default 50%), but the
result is then clamped to `bootstrap_tree_rss_ceiling_kib`, whose formula
`max(STATIC_CEILING 50331648 KiB, min(RESERVE + jobs*1 GiB, 3/4 host))` can
never rise above the 48 GiB static ceiling on hosts with ≤ ~45 effective
worker-priced jobs (20 CPUs here: 3+20 = 23 GiB < 48 GiB static). Measured on
this host: phase cap resolved to exactly 48 GiB, and the compiler-tests
campaign (build-threads=8 auto-sized from free RAM) peaked at
`max_rss_kib=50331648` — killed `status=rss-cap-exceeded`, `exit_status=88`
(campaign `M4ppmQ`, result.env). The explicit-knob escape
(`SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB`) is also closed: values above the
ceiling are refused, and the ceiling is the static 48 GiB.

**Workaround used (verified to proceed past the campaign):** explicit
`BOOTSTRAP_VERIFY_BUILD_THREADS=4` (honored as-is, bypasses the free-RAM
derivation) plus `BOOTSTRAP_VERIFY_TEST_WORKERS=2` roughly halves the phase's
parallel shard footprint; combined with `--invalidate-cache=stage2` for an
unrelated cache-reuse blocker
(`stage2_cache_reuse_hir_ledger_sealed_cache_eacces_2026-10-31.md`).

**Suggested direction:** the static ceiling was calibrated as a compile-worker
bound; the phase-priced cap should either bypass the static ceiling (keeping
only the 3/4-host bound) or the ceiling formula should price test-phase jobs
like compiler binaries (GB-scale), not compile shards. Same consistency
requirement for `process-tree-rss-watchdog.pl` as in the original fix.

**Status:** OPEN (recurrence; original floor fix remains valid for its case)

**Sixth data point (2026-10-31, campaign `efBuq7`):** with the elevated ceiling
raised to 56 GiB (request 58720256, admitted at lane start with 83 GiB
available), the CAMPAIGN-start admission then correctly refused it:
`available_bound=42571353` KiB — a concurrent session's lane
(`build/devhub-goal/runtime-authority/`, 9 processes, ~70 GB) had consumed the
host headroom. Fail-closed by design. With the other lane active, host RAM
cannot hold its ~70 GB plus this campaign's measured ~50-55 GB demand
(121 GiB host). Conclusion: on a busy shared host the phase cannot pass at any
in-policy cap; it needs (a) an idle-host window, or (b) the durable policy fix
(whole-build phases must not be priced by the compile-worker static ceiling —
see "Suggested direction" above) so the cap is not needed, or (c) the phase's
real demand reduction (the campaign builds the full CLI + test runner + LSP/MCP
tools concurrently; demand scales with build threads x ~14.5 GiB shard RSS on
this aarch64 host).

**Fourth data point (2026-10-31, campaign `DudKGG`):** even at
`BOOTSTRAP_VERIFY_BUILD_THREADS=2`, `BOOTSTRAP_VERIFY_TEST_WORKERS=1`,
serialized tool builds and `--jobs=5`, killed at the cap again. Thread-count
reduction is exhausted as a lever.

**Admitted escape hatch identified (no policy change needed):** setting the
paired env
`SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=<K>` + `SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB=<K>`
is honored by BOTH layers by design — `bootstrap_tree_rss_admit_ceiling`
(tree-rss-policy.shs:235) validates the elevated ceiling (request > previous,
≤ 3/4 total AND ≤ 3/4 available host memory, enforce mode, declared jobs, no
fixture hooks) and then admits the explicit cap against it; the campaign
watchdog forwards the ceiling via `--compiler-ceiling-kib`
(bootstrap-verification-campaign.shs:88). On the 121 GiB host, K=51200000
(48.8 GiB) requires ≥ ~65 GiB available at each admission. Retry 9 tests this.
The policy-level fix (phase cap should not clamp whole-build phases to the
compile-worker static ceiling) remains the durable direction.

**Third data point (2026-10-31, same host, campaign `6G0UBQ`):** with
`BOOTSTRAP_VERIFY_BUILD_THREADS=4`, `BOOTSTRAP_VERIFY_TEST_WORKERS=2`,
`BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1`, and the whole lane at `--jobs=5`,
the tree STILL pegged at `max_rss_kib=50331648` and was killed. Measured
campaign children include ~14.5 GiB compile shards, so the shard term
(build_threads x shard RSS) dominates, not the tool-build concurrency. The
phase cannot pass on this host at ANY thread count ≤ 8 without either raising
the static ceiling (blocked by the explicit-cap refusal) or halving threads
again (untested: 2 threads).

**Second data point (2026-10-31, same host):** retry with `BOOTSTRAP_VERIFY_BUILD_THREADS=4`
`BOOTSTRAP_VERIFY_TEST_WORKERS=2` still peaked at `peak_rss_kib=50446232` and was
killed at the same 48 GiB cap (campaign `r2e2kR`). Halving build threads does not
rescue the phase — the dominant term is the two concurrent full-closure tool
builds (measured 10.5-12.6 GiB each, see bootstrap-from-scratch.sh Stage-2 tests
comment), not the compile shards. Next lever: `BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1`.
