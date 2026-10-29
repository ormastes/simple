# Sub-KiB sanity reserve silently becomes a zero compiler floor

Status: shell-boundary regression PASS; real candidate sanity and Stage2 admission pending.

PR #5307 preserves positive SIMPLE_BUILD_MEMORY_RESERVE_BYTES through canonical
sanity's environment scrub. It accepted 1..1023 bytes, but
app/cli/shard_mem_clamp.spl divides the value by 1024 before applying its floor.
These positive inputs therefore unintentionally disable the floor. Reject that
range before invoking the candidate. Preserve the existing absent-variable
behavior, signed-i64 upper bound, runtime checks, worker clamps and hard caps.
Record effective reserve bytes and explicit/default provenance in the actual
sanity receipt; do not rewrite historical failed receipts.

The current Windows candidate
5C4EF0DF0F0392BF8204FBDD1582A5B3BFC6B68447571C3557AF425B51C29018
is retained under build/bootstrap/runner-sosix-stage2-current-tools as rejected.
Its original p2_add refusal was 24446 MiB free versus a 24576 MiB reserve,
exit3 before compilation, not OOM. This motivates truthful process-local policy
transport but does not justify zero reserve or fabricated admission.

A 12 GiB explicit reserve (12884901888 bytes) leaves about 5.3 GiB above the
floor at the observed 17.31 GiB available, compared with the earlier roughly
2.3 GiB owned tree RSS. This is a bounded retry policy, not a prediction of
future memory use. Re-measure min(physical RAM, commit headroom) before launch;
retain enforcing RSS/timeouts and live worker clamping. Do not kill unrelated
applications. Candidate/compiler source and runtime identities remain exact.

Focused validation: the prospective upstream-based owner passed four real
shell-wrapper/capture cases (exported/local16GiB, absent24GiB default, existing
invalid collector cap) and eleven rejected reserve cases. Invalid cases require
status125, no candidate invocation, no frontend log and no sanity receipt.
Accepted cases verify child environment and receipt bytes/provenance. The native
workload is replaced by a shell double; this is not Stage2/runner admission.
Upstream ReserveScrubTests now test 1024 as the smallest accepted byte value
and reject 1 and 1023. Its POSIX Python execution is not claimed on Windows.
