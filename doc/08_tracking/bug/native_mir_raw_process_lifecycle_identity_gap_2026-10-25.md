# Raw native MIR process lifecycle has no retained tree terminal authority

Status: OPEN; scheduler source candidate is NOT SOURCE_GO or admitted.

Independent Astra review of a4a0bafc178 identified the inherited
`run_ledger_shards` successful-wait path calling `process_is_running(pid)`
after the owned wait had already reaped the process. That PID may be reused;
a subsequent termination can target an unrelated process. The scoped Simple
repair treats an actual successful wait as terminal leader proof and performs
no later liveness probe for that PID.

Remaining: `src/runtime/platform/unix_common.h` rt_process_kill may itself reap
its child; a following process_wait=-1 cannot establish that the leader is
still alive or that termination failed. Raw PID-only spawn/kill also does not
prove llc/clang and other descendants are gone. A sampled birth identity alone
is not a retained termination capability and cannot eliminate PID-check/kill
TOCTOU. New parent launch records therefore label only leader_reaped, never
pretend tool-tree quiescence.

Reuse the existing std.nogc_sync_mut.io.group_process_owner managed broker
capability (durable terminal receipt, leader_reaped plus tree_empty) or its
already-owned process equivalent before scheduler qualification. It has no CLI
registration/caller in this source lane yet. Do not add another scheduler,
runtime fork, fabricated tree_empty flag, or source/seed fallback.

Required actual acceptance remains timeout/SIGKILL/fail-fast cancellation with
retained original child identity, terminal status preserved when kill reaps,
no post-reap PID probe/kill, and complete tool-tree quiescence. Runtime evidence
is UNRUN without a qualified CLI/provider/runtime; source helpers and sampled
birth values do not qualify those claims. Frozen campaigns stay unchanged.
