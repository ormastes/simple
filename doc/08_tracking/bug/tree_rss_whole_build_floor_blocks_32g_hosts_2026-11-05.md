# Tree RSS whole-build one-worker floor makes stage2-compiler-tests unstartable on 32 GiB hosts

Date: 2026-11-05
Host: Windows 11, 31.7 GiB RAM (33,195,332 KiB total, ~17.2 GiB available with normal desktop/agent load)
Lane: stage2 trust-root bootstrap, `--full-bootstrap --stop-after-stage2 --jobs=half --backend=cranelift`
Related: tree_rss_floor_kills_stage2_compiler_tests_on_large_hosts_2026-10-15.md (watchdog floor, fixed 2026-10-16)

## Observation

Stage 2 itself ADMITTED (stage2-provenance.receipt + stage2-sanity.receipt issued,
candidate 742c3d31eb99...). The post-admission `stage2-compiler-tests` phase then
refused to start, exit 1 from `admit-built-stage2-compiler-tests.shs`:

```
error: tree RSS policy: whole-build phase cannot fit one full-CLI build worker:
host budget 13530702 KiB (3/4 of available 18040936 KiB) is below the
one-worker requirement 29360128 KiB (base 4194304 KiB + worker floor
16777216 KiB x 150%); free host memory (another lane?) or raise
tree_rss_host_pct (max 75)
```

## Root cause

`scripts/bootstrap/lib/tree-rss-policy.shs` prices one whole-build worker at
`base 4 GiB + floor 16 GiB x margin 150% = 28 GiB` before the phase may start
(`bootstrap_tree_rss_whole_build_export`). On a 64 GiB host (the 2026-10-15 bug
doc's host) 3/4 of available memory can exceed that; on this 32 GiB host it
cannot — even 100% free memory (31.7 GiB < 37.3 GiB required at pct 75) cannot
satisfy the fit check. `BOOTSTRAP_TREE_RSS_PHASE_WORKER_FLOOR_KIB` is a
hardcoded constant (not a `bootstrap_tree_rss_knob`), so no sanctioned env
override exists; the refusal's own suggestion (raise host pct, max 75) is
arithmetically insufficient.

The floor is calibrated for a COLD full-CLI build (the 2026-10-15 history: a
cold build legitimately needs the headroom). With a warm content-keyed cache
the same build measured 96 s compile + 19 s link and ~2 GiB tree RSS
("Cache: reused 1567 modules; rebuilt 2" in the same run), far below the floor.

## Impact

- The stage2 trust-root admission itself is unaffected (receipts issued).
- The `--full-bootstrap` compiler-test matrix cannot complete on 32 GiB
  hosts; `--stop-after-stage2` runs end in
  `VERDICT — ABORTED: stage=stage2-compiler-tests`.
- Consumers needing a test-capable full CLI must build it from the admitted
  compiler (`native-build --entry src/app/cli/main.spl`, reusing
  stage2-native-cache), as the wave-1 verification lane does.

## Suggested direction

Extend the 2026-10-16 phase-priced-cap fix to the scheduler's fit check:
(a) make `BOOTSTRAP_TREE_RSS_PHASE_WORKER_FLOOR_KIB` a canonical knob
(`SIMPLE_BOOTSTRAP_TREE_RSS_PHASE_WORKER_FLOOR_KIB`) with the small-host
default preserved; or (b) resolve the fit check against the warm-cache
content-keyed estimate when a cache is present, keeping the cold-build floor
as the no-cache default; or (c) clamp the requirement to the host budget and
lower the worker count to 1 with the runaway margin still enforced (exit 88)
as the existing watchdog already does. Any option must keep the refusal
fail-closed when real headroom is absent and stay consistent with
process-tree-rss-watchdog.pl.

## Status

FIXED (2026-11-05): `bootstrap_tree_rss_phase_pricing_resolve` in
`scripts/bootstrap/lib/tree-rss-policy.shs` makes the phase pricing
lane-tunable via `SIMPLE_BOOTSTRAP_TREE_RSS_PHASE_WORKER_FLOOR_KIB`,
`SIMPLE_BOOTSTRAP_TREE_RSS_PHASE_WORKER_MARGIN_PCT`, and
`SIMPLE_BOOTSTRAP_TREE_RSS_PHASE_BASE_KIB` — validated canonical positive
decimals, lowering-only against the immutable shipped defaults, fail-closed
on malformed or raising values; the refusal now names the knob. Defaults are
unchanged (cold-build small-host protection preserved); the shipped
self-test (`tree-rss-policy.shs --selftest`, 64 fixtures) passes. The deeper
worker-side growth (a no-GC-runtime eviction cannot reclaim; see
mir_shard_commit_blowup_full_closure_2026-11-05.md) is unchanged — the knob
admits lanes whose measured need genuinely fits (warm cache), it does not
make an 18 GiB worker fit a small host.
