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

**Status:** fix implemented 2026-11-05 (see the last section), pending
verification by a real bootstrap.

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

**Fifth data point (2026-11-05, same 121 GiB aarch64 host, release/1.0.0 `0ff9a746185`, `--backend=cranelift`, default build-threads=8, test-workers=4):**
Stage 2 rebuilt 1567 modules and was ADMITTED (candidate sha256
`3d956afd7a9bea2b240d62cc580b31dbb2b339a04e9749bf2442ffee93ac2d43`); the matrix's
first build row `compiler_cli_build` started `[shard] threads=3` HIR workers
(admission estimate 9,000,000 kB each), all three finished `load_sources`
(4437 files) and the tree was killed at the cap before HIR began:
`status=rss-cap-exceeded exit_status=88 peak_rss_kib=50366440` (~15.6 GiB per
worker after source load alone, vs the 9 GB estimate). Evidence (untracked):
`build/bootstrap-opus-1/stage2-compiler-tests/aarch64-unknown-linux-gnu/rejection.env`,
`.../verification/logs/compiler_cli_build.log`. Retry: one sanctioned
`admit-built-stage2-compiler-tests.shs` re-run against the same admitted Stage 2
with `BOOTSTRAP_VERIFY_BUILD_THREADS=1 BOOTSTRAP_VERIFY_TEST_WORKERS=1
BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1` (the one thread count not yet tested
here); result recorded below.

**Sixth data point (2026-11-05, threads=1 retry of the fifth):** sanctioned
`admit-built-stage2-compiler-tests.shs` against the same admitted Stage 2 with
`BOOTSTRAP_VERIFY_BUILD_THREADS=1 BOOTSTRAP_VERIFY_TEST_WORKERS=1
BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1`. The phase cap scaled DOWN with the
thread count: `rss_limit_kib=5859375` (6.0e9 bytes; at 8 threads it was the
50331648 KiB ceiling). The single in-process `compiler_cli_build` parsed 3002
files (446 s), entered HIR and was killed at module 9/3005:
`status=rss-cap-exceeded exit_status=88 peak_rss_kib=5860212`. So the phase is
priced at ~6 GB per build thread while one full-CLI frontend needs ~15 GiB
(fifth point); no thread count can pass on this host. Thread reduction is
exhausted. The remaining levers are policy-owned: price the whole-build phase
on measured full-closure demand, or the explicit paired cap/ceiling env, which
under `.claude/rules/bootstrap.md` is a DIAGNOSTIC attempt and cannot admit.

Correction (2026-11-05, while fixing): the 5859375 KiB in this data point is
not "the phase cap scaling down with the thread count". The admit entrypoint
(`admit-built-stage2-compiler-tests.shs`) never resolved a phase cap at all --
only `bootstrap-from-scratch.sh` did -- so the campaign watchdog fell to its
literal default `bc_campaign_rss_cap=${SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB:-5859375}`
(`bootstrap-verification-campaign.shs`). The per-row owner would have priced
one thread at 8388608 KiB (`resolve(1)` budget); the campaign's 5.59 GiB was
the operative kill line. Both entrypoints now run the same whole-build plan.

## Status (2026-11-05): fix implemented -- worker-floor pricing, pending verification by a real bootstrap

Root cause, both recurrences: the phase was priced by compile-shard numbers
(96 MiB / 5120 MiB per job budget, 1 GiB per job hard ceiling, 48 GiB static
ceiling), while its WORKERS are full-CLI closure builds measured at ~15.6 GiB
each after `load_sources` alone (fifth data point). No thread count can pass a
cap that is not priced per worker at that scale; the explicit paired env is a
diagnostic attempt by rule and cannot admit.

Fix (`scripts/bootstrap/lib/tree-rss-policy.shs`,
`bootstrap_tree_rss_whole_build_plan` / `bootstrap_tree_rss_whole_build_export`):

    budget  = min(host_total x tree_rss_host_pct / 100 (default 50%),
                  3/4 x MemAvailable)
    workers = min(requested build threads, (budget - base) / (floor x margin)),  >= 1
    cap     = base + workers x floor x margin

with one named constant per term: `BOOTSTRAP_TREE_RSS_PHASE_WORKER_FLOOR_KIB`
= 16777216 (16 GiB; the measurements above are cited in its comment),
`BOOTSTRAP_TREE_RSS_PHASE_WORKER_MARGIN_PCT` = 150 (runaway margin: a tree
above `base + workers x 24 GiB` is still killed, exit 88),
`BOOTSTRAP_TREE_RSS_PHASE_BASE_KIB` = 4 GiB (coordinator 1.32 GiB measured,
verifier shell, campaign watchdog, interpreter test workers). The worker count
is REDUCED to what the budget holds (never a cap below the floor), published
as `BOOTSTRAP_VERIFY_BUILD_THREADS` so the compiler's own pool admission
(cap x 60% / 9 GB) cannot start more workers than the cap was priced for; a
host that cannot hold one worker (budget < 29360128 KiB) is refused before the
phase starts, naming the requirement; unknown host RAM is refused, not floored.
When the cap exceeds the default hard ceiling the policy publishes it as the
elevated ceiling pair, and both owners admit it through the EXISTING
elevated-ceiling admission (3/4 of real total AND available memory, enforce
mode, declared workers, no fixture hooks) -- recorded in the receipt as
`cap_source=phase-policy cap_bound=worker-floor-elevated
compiler_ceiling_admission=elevated`. Monitor mode (nothing enforced) clamps
to the default ceiling and requests no elevation. An explicit
`SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` is kept untouched.

On this host (MemTotal 127600812 KiB, 8 requested threads): budget 63800400
KiB -> 2 workers, cap 54525952 KiB (26 GiB per worker), elevated ceiling
54525952 KiB; admitted by the policy and by the real watchdog in enforce mode
(selftest + `tree-rss-cap-policy-test.shs` 2c). Requires >= 72701270 KiB
MemAvailable at each admission (campaign start and every native-build row); a
busier host reduces to 1 worker (cap 29360128 KiB), and below that refuses.

Consequence to know: because the phase now publishes the cap/ceiling PAIR,
`run-process-group-timeout.shs` unsets both for non-native-build rows, so the
interpreter test-runner rows no longer inherit the phase cap and get the
compile-priced default for the declared 2 workers, (3072 + 2 x 5120) MiB =
13631488 KiB -- a tightening (single-spec rows, 120 s spec timeout; the
2026-10-15 phase ran its tests under 5.59 GiB). Provenance: every owner's
receipt (campaign and build rows) attributes a policy-published cap as
`cap_source=phase-policy cap_bound=worker-floor[-elevated]`
(`bootstrap_tree_rss_published_attribution`); a user-set diagnostic pair
stays `explicit-env/explicit`, so the two are never confused.

Wired: `bootstrap-from-scratch.sh` stage2-compiler-tests block and
`admit-built-stage2-compiler-tests.shs` (which previously set no cap at all);
`bootstrap-verification-campaign.shs` now forwards `--cap-source/--cap-bound`.
The Stage 2 native-build phase keeps `bootstrap_tree_rss_phase_cap_kib`
(it admitted on this host). Tests: policy `--selftest` 58 fixtures (14 new
plan/export cases incl. the real host in enforce mode),
`scripts/bootstrap/tests/tree-rss-cap-policy-test.shs` 17 cases (its 2a/2b/3
expectations were stale since the 48 GiB widening and are updated; new 2c
runs the plan's pair through the real watchdog).

Verification still owed: a real `stage2-compiler-tests` pass on this host
with the fixed scripts. Note the Stage 2 admission binds `scripts/bootstrap`
and `scripts/check/lib` in its source snapshot
(`command-snapshot.shs` `bootstrap_stage3_source_snapshot_once`), so the
currently admitted Stage 2 (`3d956afd...`, old scripts) cannot be published
against the fixed tree; Stage 2 is re-admitted on the fixed tree first.

## Run 4 (2026-11-05, release/1.0.0 `13a060d644e`, Linux aarch64 121 GiB): memory fixed, time budgets not scaled

The worker-floor plan worked for memory: Stage 2 compiler tests passed every
row except `compiler_cli_build`, whose tree peaked at max_rss 23 GiB (inside
the cap). The plan reduced the requested 8 build workers to 2, but the time
budgets were still the ones calibrated for 8:

- native internal timeout 1800 s (`BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT`,
  passed as `native-build --timeout`), row timeout 3600 s ("timeout=3600s" in
  the Stage 2 banner), campaign deadline 7200 s (verifier default).
- `compiler_cli_build.log`: ~900 s of parse/HIR/MIR setup, then MIR at
  ~0.68 modules/s combined (576 done at 1748 s build-elapsed); both MIR shard
  workers killed at the internal timeout:
  `owner=1/2@0 status=BLOCKED exit=-2 claimed=317`,
  `owner=0/2@0 status=BLOCKED exit=-2 claimed=279` -> 596 of 3010 modules ->
  `blocked=worker could not be reaped` -> `MIR shard aggregate failure`.
  Phase elapsed 3171 s. 3010 modules at that rate need ~75 min of MIR alone.

Fix (`scripts/bootstrap/lib/tree-rss-policy.shs`): the whole-build plan now
also computes `bootstrap_tree_rss_plan_timeout_scale = min(ceil(requested /
fitted), BOOTSTRAP_TREE_RSS_TIMEOUT_SCALE_MAX=4)` (1 when nothing was reduced
or the cap is explicit), and `bootstrap_tree_rss_scaled_timeout VAR DEFAULT`
publishes each budget as DEFAULT x scale unless VAR was set explicitly (kept
verbatim). Both Stage 2 test owners (`bootstrap-from-scratch.sh`,
`admit-built-stage2-compiler-tests.shs`) publish the native internal, row and
campaign budgets through it after the plan; on this host that is 7200 / 14400 /
28800 s. The verifier summary records `timeout_source=` (per budget, `VAR:source` comma-joined:
`explicit` | `phase-policy` | `phase-policy-scaled`) and `timeout_scale=`.
Still fail closed: a hung worker is killed at the scaled limit, the scale is
bounded, and a malformed default is refused.

Not changed: the MIR reaper (`native_build_main.spl` ~1148) sends SIGTERM via
the generic `rt_process_kill` (`runtime_process.c` ~107) and gives up after a
5 s wait with no SIGKILL escalation ("worker could not be reaped"). Escalating
inside the shared primitive changes every caller's graceful-shutdown
semantics, and editing the `.spl` site changes compiler source (new Stage 2
needed); left as a follow-up.

Re-test note: `scripts/bootstrap` is part of the admitted source snapshot
(`command-snapshot.shs` authority list), so the run-4 admitted Stage 2 cannot
be published against the fixed tree. Without a rebuild it can be re-tested on
its own frozen source with explicit budgets, which the old scripts already
honour: `BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT=7200
BOOTSTRAP_VERIFY_CAMPAIGN_TIMEOUT_SECONDS=28800` (env) plus `--timeout-seconds=14400` (the old
admit script does not read `BOOTSTRAP_VERIFY_TIMEOUT_SECONDS`); that receipt is
a manual-budget re-test and carries no `timeout_source`.
