# Native-build parse shard stalls after source-closure progress

## Status

Open bootstrap blocker exposed after fixing interpreted `rt_array_free`.

## Evidence

- source revision base: `0891120f3ea566e3b2c5169b8c488fec28ab99e7`
- command mode: internal native-build worker, `--parse-shard=0/8`
- backend/profile: Cranelift, dynload, entry closure, no stub fallback
- entry: `src/app/cli/_CliMain/main_and_help.spl`
- preserved cache: `/mnt/data/worktrees/lane-amb3/build/bootstrap/native_cache`
- log: `build/native_probe/render-shard0-after-array-free.log`

The worker reports source-closure progress through item 704/1046, last naming
`src/lib/nogc_sync_mut/tooling/easy_fix/accessor_core.spl`, then emits no new
progress for more than 26 minutes while remaining at approximately 100% CPU and
3.1 GiB RSS. No cache objects are emitted during the stalled interval. The
direct shard runner has no worker watchdog, so the exact process was terminated
with SIGTERM and the cache/log were preserved.

A second bounded reproduction after the independent REXVISIT dictionary fix
reaches 704/1047 in 56.975 seconds, names the same
`src/lib/nogc_sync_mut/tooling/easy_fix/accessor_core.spl` item, then emits no
new progress before `timeout --kill-after=10s 900s` exits 124. This proves the
stall is in source-closure expansion before the HIR re-export walk and is not
caused by REXVISIT's former quadratic visited set.

## Required fix

Instrument the transition after source-closure enumeration with phase and
current-item progress, and apply the normal native-build worker timeout to
direct parse-shard mode. The owning loop must either converge or fail with a
specific source/task receipt before the pure-Simple CLI, rendering guest, and
Vulkan showcase can be admitted.
