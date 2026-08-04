# Feature: kimi_mcp

## Raw Request
fix kimi mcp, check spipe skill

## Task Type
bug

## Refined Goal
Configure Kimi Code to load the repository MCP servers through its project-local configuration and ensure every configured launcher exists or uses a working source fallback.

## Acceptance Criteria
- AC-1: `.kimi-code/mcp.json` is valid JSON and is discoverable from `/home/yoon/simple`.
- AC-2: Every configured stdio launcher resolves on this checkout and has the required environment.
- AC-3: The MCP integration check passes without placeholder assertions.

## Scope Exclusions
No source-code changes to the MCP servers or native artifact rebuild.

## Cooperative Review
N/A — focused configuration repair; no independent sidecar lane.

## Phase
dev-done

## Log
- dev: Created SPipe state and acceptance criteria for Kimi MCP configuration repair.
- impl: Replaced the stale `bin/simple` source launchers with checkout-local,
  stage-3-built native MCP binaries under `build/kimi_mcp/`.
- evidence: Both binaries returned a JSON-RPC `initialize` response; the LSP
  binary also returned all 11 entries from `tools/list`.
- verify: `.kimi-code/mcp.json` parsed successfully; both configured launchers
  resolved from the project root, initialized over stdio, listed their tools
  (general=3, LSP=11), and completed a real `tools/call` request.
