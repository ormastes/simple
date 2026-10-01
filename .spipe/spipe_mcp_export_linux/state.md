# Feature: SPipe MCP export and Linux path portability

## Raw Request
resync gh and rebase check spipe mcp and plugin. spipe mcp (export error + linux path). spipe plugin's mcp/servere/js shipping gap. fix them and push

## Task Type
bug

## Refined Goal
Repair the SPipe MCP package's duplicate export and Node-version-dependent Linux path resolution while preserving the existing Unix path contract.

## Acceptance Criteria
- AC-1: The two bug records are claimed before source edits, with exact pre-fix reproductions and pure-JavaScript ownership identified.
- AC-2: The duplicate `isWorkspaceRegistryV1` export no longer causes a module-load SyntaxError, and the MCP/package regression imports the owner successfully.
- AC-3: Linux/Node 18 path resolution does not depend on `import.meta.dirname`; the focused path regression resolves package fixtures and preserves POSIX separators.
- AC-4: Exact and adjacent regressions cover the duplicate-export and path-resolution root causes, with Windows path behavior kept in a separate platform assertion.
- AC-5: Focused SPipe MCP/package tests pass once after convergence; no plugin, Phase1 v3, or unrelated work is included.
- AC-6: Knowledge updates land with the fix: bug records and the SPipe feature/layer process notes are refreshed; no new workflow or SSpec manual surface is introduced.

## Scope Exclusions
Plugin packaging/shipping, Phase1 v3, PR integration, rebase, and push are owned by the parent lane or sibling lane.

## Cooperative Review
N/A: narrow two-file JavaScript bug lane; parent agent is merge owner and final reviewer.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: bug); PR #526 inspected read-only and origin/main fetched before isolated checkout.
- reproduce: On Node 18/Linux-compatible execution, package unit discovery hit the duplicate `isWorkspaceRegistryV1` export; Unicode path setup then hit `import.meta.dirname === undefined`, followed by the adjacent `Array.prototype.toSorted` Node-20-only failure.
- fix: Removed the two stale duplicate exports, derived test paths from `fileURLToPath(import.meta.url)`, and replaced `toSorted` with a copy-sort while regenerating the bound Unicode metadata artifacts.
- verify: Focused MCP/workspace/Unicode run passed 27/27 once after convergence; full package `npm test` reached 292 tests with 289 pass, 2 unrelated/pre-existing failures, and 1 platform-conditional skip. `git diff --check` passed.
