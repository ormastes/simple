# compiler_cli_build row cap stale: measured workers grew past the 60 GiB cap

Status: fix-implemented (cap raised to 63500000 KiB; lane validation pending)

## Symptom

Two consecutive stage2 lanes (v7g pin 967f9178950e with
SIMPLE_MIR_SHARD_COUNT=8/8 threads, v7h same pin with 16 shards/6 threads)
were killed in the compiler-test matrix campaign with
`primary_status=rss-cap-exceeded`:

- v7g: peak_rss_kib=62960380 vs rss_limit_kib=62914560 (~45 MB over)
- v7h: peak_rss_kib=62995924 vs rss_limit_kib=62914560 (~81 MB over)

The peak is invariant to MIR shard count (8 vs 16) and build threads (8 vs 6):
the two parallel MIR shard workers now sample ~29 GiB each plus the
coordinator, slightly above the 2026-11-06 measurement (2 x 25.2 + 1.1 GiB)
that sized BOOTSTRAP_TREE_RSS_PHASE_CLI_ROW_CAP_KIB=62914560 with "~8.5 GiB
headroom". The compiler has grown since; the headroom is gone.

## Constraint chain

The row cap must also fit the host budget (host RAM x 50% = 63800400 KiB on
the 121 GiB aarch64 reference host), so the cap cannot simply be raised to
64 GiB — the planner refuses (`compiler_cli_build row needs N KiB ... host
budget 63800400 KiB cannot hold it`). The observed peak (62995924) fits under
the budget, so the cap is set to 63500000 KiB: ~433 MB over the observed peak,
~278 MB under the budget.

## Fix

`scripts/bootstrap/lib/tree-rss-policy.shs`:
BOOTSTRAP_TREE_RSS_PHASE_CLI_ROW_CAP_KIB 62914560 -> 63500000, plan/envelope
selftest expectations updated (the explicit-env envelope fixture keeps its
own 62914560 input). `sh scripts/bootstrap/lib/tree-rss-policy.shs --selftest`
passes 123 fixtures.

## Follow-up (open)

The durable fix is re-measuring the row from live lanes and/or making the
shard-share bounded (the 2026-11-06 doc's original concern) so the row need
tracks the compiler size automatically instead of a hand-measured constant.
If a future lane's peak exceeds 63500000, re-measure and revisit the host
budget fraction rather than shrinking the workload.
