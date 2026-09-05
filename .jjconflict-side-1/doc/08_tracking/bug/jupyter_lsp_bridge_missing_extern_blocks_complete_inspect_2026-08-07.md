# Jupyter kernel `complete_request`/`inspect_request` crash the kernel — deployed `bin/simple` rejects `rt_process_spawn_piped`

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

- **Date:** 2026-08-07
- **Area:** `src/app/jupyter_kernel/main.spl` (Task P1) LSP bridge / deployed `bin/simple` extern registry
- **Symptom:** `error: semantic: unknown extern function: rt_process_spawn_piped` — kills the whole
  Jupyter kernel subprocess as soon as it handles its first `complete_request` or `inspect_request`.

## Repro (bypasses the wrapper entirely — kernel JSON-lines protocol direct)

```bash
printf '%s\n%s\n' \
  '{"channel":"shell","msg_type":"kernel_info_request","msg_id":"k1","session":"s1","content":{}}' \
  '{"channel":"shell","msg_type":"complete_request","msg_id":"c1","session":"s1","content":{"code":"val x = 4","cursor_pos":9}}' \
  | bin/simple run src/app/jupyter_kernel/main.spl
```

Output: `kernel_info_reply` comes back fine, then
`error: semantic: unknown extern function: rt_process_spawn_piped` and the process exits without
ever emitting a `complete_reply`. Same failure for `inspect_request`.

## Cause

`handle_complete`/`handle_inspect` in `src/app/jupyter_kernel/main.spl` call
`get_or_start_lsp_bridge()`, which (via
`src/lib/nogc_sync_mut/notebook/lsp_bridge.spl` -> `src/lib/nogc_sync_mut/io/process_ops.spl`)
spawns the LSP subprocess through `rt_process_spawn_piped`. That extern IS implemented
(`src/runtime/runtime_process.c`), but the currently-deployed `bin/simple` (the Rust-built
bootstrap seed — it prints "this Rust-built Simple binary is a bootstrap seed only" on every
invocation) predates that registration, so semantic checking rejects it — the same "stale extern
registry" failure class as `deployed_binary_missing_rt_raw_i64_to_string_extern_2026-08-04.md` and
`bootstrap_blocked_unknown_extern_rt_transient_array_scope_begin_2026-07-27.md`.

## Impact

Both `complete_request` and `inspect_request` are unusable end to end against the currently
deployed kernel binary — not a wrapper defect (Task P2's `tools/jupyter/kernel_wrapper.py` relays
both correctly; verified in isolation once this crash is worked around by testing only
`interrupt_request` and `comm_open`/`comm_msg`, both of which round-trip cleanly). Verification
helper: `test/03_system/tools/jupyter/helpers/wrapper_transport_roundtrip.py` — its
`complete_request`/`inspect_request` checks are RED against this bug and isolated to their own
kernel process each so the crash doesn't cascade into the other checks.

## Ask

Rebuild/redeploy `bin/simple` (or the specific stage the Jupyter kernel launches under) from a
build that includes the current runtime extern registry, per `feedback_extern_bootstrap_rebuild.md`
— no `.spl` source change is needed, this is purely a stale-deployed-binary gap.
