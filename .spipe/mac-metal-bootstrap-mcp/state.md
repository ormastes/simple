# Feature: mac-metal-bootstrap-mcp

## Raw Request
$sp_dev sync gh. check todo and plan only can do in metal. imple them all; fix MCP handshaking failure.

## Task Type
todo

## Refined Goal
Close TODO 119 on macOS with a deployable pure-Simple CLI, verified Metal queue evidence, and a correlated MCP stdio handshake.

## Acceptance Criteria
- AC-1: A fresh full bootstrap deploys `bin/simple`, and the normal symlink path passes `-c 'print(1+1)'` plus every executable redeploy-gate check.
- AC-2: The deployed binary provenance records path, timestamp, SHA-256, architecture, and the exact bootstrap command.
- AC-3: The host GPU queue roundtrip and production GUI/web host-GPU queue wrapper pass with native Metal readback.
- AC-4: The generated MCP wrapper preserves numeric and string JSON-RPC request IDs, and the full MCP stdio integration test passes.
- AC-5: The plan, guide, report, TODO row, and normal-model review record the final evidence before TODO 119 closes.

## Scope Exclusions
Non-Metal GPU backends and unrelated fullscreen/browser worktree changes.

## Cooperative Review
Merge owner: Codex main workspace owner. Final reviewer: normal/highest-capability model. Sidecars are N/A because the remaining failures share one bootstrap/deploy boundary and require serial binary evidence.

## Runtime Boundary Decision
- runtime_need: None; the deployed CLI already supports a sibling seed delegate.
- facade_checked: `scripts/setup/setup.shs` owns the `bin/simple` release symlink layout.
- chosen_path: reuse-facade by creating the matching `bin/simple_seed` release symlink.
- rejected_shortcuts: no new `rt_*`, no shell `readlink`, no fixture-only bypass, no copied seed at `bin/simple`, and no deploy-gate relaxation.

## Phase
implementing

## Log
- dev: Refined the Metal/bootstrap/MCP closure lane into five acceptance criteria.
- implement: Reproduced deploy false-positive caused by setup omitting the sibling seed symlink; added post-setup smoke with rollback.
