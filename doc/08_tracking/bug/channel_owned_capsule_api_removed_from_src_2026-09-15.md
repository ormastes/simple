# Owned channel capsule API removed from src

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/channel_owned_capsule_contract_spec.spl

## Observed
src/lib/nogc_sync_mut/concurrent/channel.spl no longer declares
`rt_channel_free` / `channel_recv_by_id` / `channel_free_by_id`, and
src/runtime/runtime_native.c has no `void rt_channel_free(int64_t id)`
(only rt_channel_close). The one-word owned-capsule contract the spec pins
is gone.

## Unblock condition
Restore the owned free/recv API (or port the spec to the close-based
ownership model with a reviewed decision).
