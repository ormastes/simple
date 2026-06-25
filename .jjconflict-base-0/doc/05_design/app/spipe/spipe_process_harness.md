<!-- codex-design -->
# SPipe Process Harness Detail Design

## Goal

Provide one production SPipe process harness for Codex, Claude, and Gemini. The
harness owns event normalization, user-approval gates, generated hook snippets,
durable goal state, and a compact CLI HUD.

## Acceptance Criteria Trace

| AC | Requirement | Design element |
|----|-------------|----------------|
| AC-1 | REQ-001 | `normalize_provider`, `provider_hook_events`, shared CLI `hook` command |
| AC-2 | REQ-002 | `hook_jsonl`, `.spipe/<feature>/events.jsonl` |
| AC-3 | REQ-004 | `HudSnapshot`, `render_hud`, CLI `hud` command |
| AC-4 | REQ-003 | `deploy_snippets`, CLI `deploy` command |
| AC-5 | REQ-005/REQ-006 | `state_path`, `render_state`, `gate_from_state` |

## Data Structures

- `GateDecision`: allow/block result and hook exit code.
- `HudSnapshot`: model, jj worktree, commit, remaining hours/week, and goal.
- `HookDeploySnippet`: provider, target path, and generated snippet body.

## Module Layout

- `src/lib/nogc_async_mut/spipe_process_harness/types.spl` contains pure data
  contracts.
- `src/lib/nogc_async_mut/spipe_process_harness/core.spl` contains provider
  normalization, event rendering, state rendering, gate decisions, HUD rendering,
  and deploy snippet generation.
- `src/lib/nogc_async_mut/spipe_process_harness/mod.spl` exports the stable
  public API.
- `src/app/spipe_process_harness/main.spl` provides the operator and hook CLI.

## Commands

- `state`: creates durable `.spipe/<feature>/state.md`.
- `hook`: reads provider hook payload from stdin, gates, and appends JSONL.
- `gate`: verifies state and approval.
- `hud`: prints one-line status.
- `deploy`: writes provider snippets to `.spipe/hook-deploy/`.

## Command Details

### `state`

Inputs: `--feature`, `--request`, `--goal`, `--approved`.

Output: `.spipe/<feature>/state.md` with the refined goal, approval marker,
prevention mode, event log path, provider list, and acceptance criteria.

### `hook`

Inputs: stdin provider payload, `--provider`, optional `--feature`,
`--require-approval`, and environment fallbacks.

Behavior:

1. Normalize provider to `codex`, `claude`, `gemini`, or stable unknown name.
2. Read state from `.spipe/<feature>/state.md`.
3. Evaluate `gate_from_state`.
4. Append a normalized JSONL envelope to `.spipe/<feature>/events.jsonl`.
5. Return `0` for allow or `2` for block.

The hook hot path does not shell out or scan the repo.

### `gate`

Inputs: `--feature`, optional `--no-approval`.

Behavior: reads durable state and returns the same allow/block result as the hook
without appending an event. This is the explicit CI/preflight gate.

### `hud`

Inputs: `--model`, `--hr`, `--week`, `--goal` or environment equivalents.

Behavior: reads jj status/log for operator-visible VCS context and prints:

`model=<model> | jj=<worktree> | commit=<commit> | hr=<hours> | week=<week> | goal=<goal>`

### `deploy`

Behavior: writes generated provider snippets under `.spipe/hook-deploy/`:

- `claude-settings-hooks.json`
- `codex-hook.sdn`
- `gemini-settings-hooks.json`

The command intentionally writes snippets instead of mutating live client config
files directly. That keeps deployment reviewable and avoids overwriting local
provider settings.

## Error Handling

Missing state or missing approval returns exit code `2`, matching hook block semantics used by existing diagnostics comments.

## Prevention Semantics

`gate_from_state` blocks when:

- state is missing or empty
- approval is required and `User Approved: true` is absent
- the state contains `Prevent: block`
- the state contains `STATUS: FAIL`

All other states allow. This keeps live provider hooks conservative but avoids
requiring provider-specific gate implementations.

## Verification

The detailed SPipe tests live in:

- `test/03_system/app/spipe_process_harness/feature/spipe_process_harness_spec.spl`
- `test/01_unit/lib/spipe_process_harness/spipe_process_harness_spec.spl`
