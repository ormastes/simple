# SPipe Kimi adapter has no native hook events (2026-11-14)

- Where: `src/lib/nogc_async_mut/spipe_process_harness/core.spl` `provider_hook_events` (Kimi arm returns `[]`)
  and `kimi_hook_snippet` (advisory text only).
- Cause: plan section 8.2 says "extend normalization to kimi" but neither the plan nor repo docs define Kimi hook
  event names or a hook config file format. Inventing them would fabricate protocol support (plan section on provider hooks).
- Effect: Kimi sessions cannot feed the shared event log or prevention gate automatically; the hook command can only be run by hand.
- Unblock: a documented Kimi hook/config surface (event names + config location). Then fill the Kimi arm of
  `provider_hook_events`, replace `kimi_hook_snippet`, and extend the spec "lists no native hook events for the advisory Kimi adapter".
