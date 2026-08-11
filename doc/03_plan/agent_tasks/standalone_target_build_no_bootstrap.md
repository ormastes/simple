# Standalone Target Build No Bootstrap

## Delivery boundary

Compiler admission and target-product construction are separate operations.
An admitted Phase 3 compiler is an input to a target wrapper; it is not a
reason to begin a fresh Stage 1/2/3 bootstrap.

## Inventory

| Surface | Owner category | Action |
|---|---|---|
| `src/app/office` | Standalone product | Implemented target-only wrapper with provenance gate |
| `src/app/devhub` | Separate application | Add a dedicated wrapper only when a native artifact is required |
| `src/app/play` | Separate application/demo | Add a dedicated wrapper only when a native artifact is required |
| `src/app/cli`, `src/compiler` | Compiler | Bootstrap/deploy policy remains applicable |
| MCP and Simple LSP servers | Toolchain-owned services | Retain their dedicated full-CLI admission gates |

## Resume commands

```bash
sh scripts/check/build-office-standalone-target.shs --self-test
SIMPLE_TARGET_PHASE3=/absolute/path/to/build/bootstrap/stage3/<triple>/simple \
  sh scripts/check/build-office-standalone-target.shs
```

If Phase 3 admission is absent, stop at the fail-closed receipt. Do not start
bootstrap as part of this wrapper; resolve compiler admission in its own lane.
