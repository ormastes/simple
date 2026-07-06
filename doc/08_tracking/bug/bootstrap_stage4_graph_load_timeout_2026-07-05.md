---
id: bootstrap_stage4_graph_load_timeout_2026-07-05
status: OPEN
severity: high
discovered: 2026-07-05
discovered_by: Stage-4 bootstrap execution on Apple M4
related: scripts/bootstrap/bootstrap-from-scratch.sh
related: build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log
---

# Stage-4 Bootstrap: Native-build graph loading exceeds default 7200s timeout

## Summary

Stage-4 bootstrap's interpreted native-build worker exceeded the default 7200-second (2-hour) timeout on Apple M4. The module graph loading phase alone consumed approximately 97 minutes before reaching parse/compile phases, indicating a severe performance bottleneck in dependency resolution and module discovery.

## Evidence

- Platform: Apple M4 (aarch64-apple-darwin)
- Build stage: Stage 4 (pure-Simple self-hosted)
- Phase that timed out: Module graph loading
- Time spent in graph loading: ~97 minutes (before parse/compile)
- Default timeout: 7200 seconds
- Log location: `build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log`

## Impact

Stage-4 bootstrap remains incomplete and cannot produce a fresh pure-Simple binary. The long timeout blocks verification builds and prevents rapid iteration on bootstrap fixes.

## Scope

The issue is in the module graph loading phase (`compiler/99.loader/module_graph.spl` or similar), likely:
- Quadratic or worse complexity in dependency resolution
- Redundant graph traversals
- Missing memoization or caching of module metadata
- Inefficient file I/O during discovery

`bootstrap-from-scratch.sh:430` currently passes no `--timeout` argument, so the native-build worker uses a hardcoded default that is insufficient for the current graph-loading performance.

## Next Steps

1. Profile the native-build module graph loading phase to identify the bottleneck (dependency resolution, disk I/O, algorithm complexity).
2. Add memoization/caching for module metadata queries.
3. Either fix the underlying performance issue or add a configurable `--timeout` parameter to `bootstrap-from-scratch.sh` with a reasonable default for typical hardware (e.g., 14400+ seconds for interpreted stage-4).
