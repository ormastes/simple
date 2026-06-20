<!-- codex-research -->
# NFR Options: IDE Plugin Architecture

## Option 1: Conservative Desktop IDE Targets

Description: optimize for local desktop Office/IDE use.

Pros:
- Easy to measure in current repo workflows.
- Good enough for early Office suite hardening.

Cons:
- Remote/web host constraints may be deferred.

Effort: S.

Targets:
- Startup manifest scan under 50 ms warm for built-in plugins.
- Command activation under 20 ms warm.
- No plugin may mutate UI state without a capability token.

## Option 2: VS Code-Style Host Targets

Description: add host placement and isolation budgets for UI, workspace, and headless plugins.

Pros:
- Aligns with VS Code extension host separation.
- Prepares remote/headless Office automation.

Cons:
- Requires more instrumentation.

Effort: M.

Targets:
- Built-in manifest cache load under 25 ms warm.
- First activation under 50 ms for built-in plugins.
- Hot command dispatch overhead under 2 ms p95 excluding plugin work.
- Registry invalidation event propagation under 100 ms.

## Option 3: Full Dynamic Plugin Targets

Description: support install, update, unload, registry listeners, DI rebinding, and aspect reordering at runtime.

Pros:
- Closest to Eclipse dynamic registry behavior.
- Strong fit for external plugin ecosystem.

Cons:
- More failure modes and concurrency risks.
- Not needed for the first Office suite milestones.

Effort: L.

Targets:
- Runtime plugin install/uninstall without process restart.
- All registry objects carry generation ids and validity checks.
- Dynamic-aware plugin code must handle invalid registry objects.

## Recommendation

Use Option 2 for the architecture baseline and defer Option 3 until external plugins need live install/uninstall.

