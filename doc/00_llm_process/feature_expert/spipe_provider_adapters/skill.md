# Feature Expert: SPipe provider adapters

## Scope
`std.nogc_async_mut.spipe_process_harness` (`src/lib/nogc_async_mut/spipe_process_harness/{types,core,mod}.spl`)
and its CLI `src/app/spipe_process_harness/main.spl`. Plan: traceability/SPipe improvement plan 2026-11-14 section 8.2
(extend normalization to `kimi`, stable `unknown` fallback).

## Public API (typed)
- `enum Provider: Claude | Codex | Gemini | Kimi | Unknown` (closed set).
- `normalize_provider(text) -> Provider`: case-insensitive, trimmed substring match, precedence
  claude, codex/openai/gpt, gemini/google, kimi. Anything else, including `""`, is `Unknown` (never the raw text).
- `provider_slug(Provider) -> text` for serialization (`claude|codex|gemini|kimi|unknown`).
- `HookSessionId`, `ModelName`, `FeatureSlug` one-field wrappers; `GateVerdict: Allow | Block`.
  `GateDecision` carries `verdict` + `reason`; the CLI maps `Block` to exit status 2 (`verdict_exit_code` in main.spl).

## Kimi: advisory adapter, documented limit
Neither plan section 8 nor any repo doc defines a Kimi hook surface (only: Kimi Code auto-discovers the project `.mcp.json`).
So `provider_hook_events(Provider.Kimi)` is `[]`, and the deploy snippet `.spipe/hook-deploy/kimi-advisory.sdn`
states `mode: advisory`, `native_hooks: none` and the manual command `bin/simple spipe-process-harness hook --provider kimi`.
No Kimi config key or event name is invented. Unblock: see `doc/08_tracking/bug/spipe_kimi_native_hook_surface_undocumented_2026-11-14.md`.

## Callers updated (all)
`src/app/spipe_process_harness/main.spl`; specs: `test/01_unit/lib/spipe_process_harness/`,
`test/01_unit/app/spipe_process_harness/`, `test/03_system/app/spipe_process_harness/feature/`,
`test/system/app/spipe_process_harness/feature/`. `test/02_integration/app/spipe_process_harness_log_modes_spec.spl`
and `src/app/cli/{command_registry,_CliMain/main_and_help}.spl` only reference the command name (unchanged).

## Not retyped (existing, out of slice)
`HudSnapshot` text fields, `HookDeploySnippet.path/content`, `event`, `raw_payload`.
