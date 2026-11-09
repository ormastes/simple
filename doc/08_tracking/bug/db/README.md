# Per-bug shards of the bug database — see doc/05_design/infra/tracking/bug_db_shards.md
# One <bug_id>.sdn (+ its .csm seal) per bug; write them with bin/simple bug-add /
# bug-resolve or scripts/check/bug-claim.shs, never by hand.
#
# Counting bugs: count open bugs ONLY via `sh scripts/check/bug-db-shard.shs merged`
# (or its tally form `sh scripts/check/bug-db-shard.shs count`); it unions both
# tables. The merged view holds TWO bug tables — `bugs_active` and the legacy
# `bugs` — and both carry open rows. Counting one table, or grepping
# bug_db.sdn without the shards applied, undercounts (2026-11-09: 31 vs 164 open P2).
