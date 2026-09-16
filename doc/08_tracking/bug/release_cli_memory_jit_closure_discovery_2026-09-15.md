# Release CLI memory footprint, release-app JIT closure fallback, and local consumer-discovery failure
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-09-15
**Impact:** every local `simple release …` invocation; the version authority
cannot produce a PASS locally at all (discovery fails closed), so local
version-bump evidence is impossible without CI.
**Status:** (1) JIT closure fallback **FIXED** in-commit (refactor, verified);
(2) memory footprint measured, no easy win (see below); (3) consumer-discovery
failure reproduced, root cause in the seed-runtime process boundary — runtime
follow-up required.

All numbers measured on this host (Windows, 24-core, seed `bin/simple`,
`SIMPLE_LIB=<worktree>/src`, `version-check --json` / `version-bump-plan`,
process-tracked peak working set):

| run | wall | peak RSS | JIT fallbacks |
|---|---|---|---|
| version-check, lambda (before) | 2.9 s | 186.8 MB | 1 |
| version-check, refactored (after) | 6.4 s | 252.2 MB | 0 |
| version-bump-plan, lambda (before) | 3.2 s | 185.9 MB | 1 |
| version-bump-plan, refactored (after) | 6.8 s | 252.6 MB | 0 |

## 1. JIT closure fallback (FIXED in-commit)

`record_post_integration_divergence` built a rejected-receipt via a lambda
capturing `request`. The JIT closure ABI cannot carry the boundary types
(`[TypeId(14)] -> TypeId(14)`, "ANY means no encoding is correct for both an
integer and a float"), so the whole app silently dropped to the interpreter:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT
compile: Module error: function 'record_post_integration_divergence' creates a
lambda/closure the JIT closure ABI cannot compile …
```

Fix: replace the lambda with a top-level `_post_divergence_rejected(request,
reason)` helper (13 call sites). Verified: `JIT compilation failed` count goes
to 0 in both commands above.

Measured consequence on this app's short-lived commands: JIT startup is *slower
and heavier* than the interpreter (6.4 s/252 MB vs 2.9 s/187 MB for
version-check) because codegen dominates a ~3-second run. The fallback message
is informational here, not a hot-path regression; the refactor is still right
— it removes a known JIT-ABI limitation and pays off on long-running commands
(100-1000x interpreter slowdown was the advertised risk).

## 2. Memory footprint (measured; no narrow-scope win)

Every release CLI invocation peaks at ~187-253 MB RSS. The startup warning
`[memory-guard] SIMPLE_LIB=… contains 600+ .spl files — consider narrowing
scope to avoid memory bloat` suggests narrowing the lib scope, but measured
`SIMPLE_LIB=<worktree>/src/lib` gives the same 185.7 MB — the footprint is the
transitively loaded module graph, not the scan roots. Reducing it needs
import-graph pruning or lazy module loading, not a scope tweak. Filed here so
the measurement is on record; no in-commit fix.

## 3. Consumer discovery fails locally (reproduced; runtime follow-up)

`release version-check` / `version-bump-plan` always fail locally with
`product-version consumer discovery did not complete`, so the version
authority cannot PASS on this host.

- The exact discovery scan, standalone: `rg -l -F --glob … -- 1.0.0-beta.3
  src/app src/lib src/compiler src/compiler_rust tools/mcp-registry
  tools/lsp-mcp-registry` → **0.78 s, exit 0**.
- Under the release app (seed runtime process boundary) the same scan reports
  an exit code that is neither 0 nor 1, and no timeout marker appears in
  stderr (checked all three runtime markers: `\nTIMEOUT\n`,
  `Process timed out`, `[TIMEOUT: Process killed after …]`).
- `_windows_resolve_cmd("rg")` implements cmd-style PATH×PATHEXT resolution
  and `rg.exe` is on PATH, so spawn lookup should succeed.

Suspected: the seed runtime's bounded-process spawn returns a non-conforming
exit code for this child (compare
`test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md` — known
signal/exit-code collapse residue in the runtime paths). Needs a runtime-side
probe; the version authority's fail-closed handling is working as designed.

## Related (surfaced in the same runs)

Every invocation also prints `compiler_cross_module_private_symbol_collision`
warnings for `env_get` (5 definitions, 2 signatures), `env_vars`,
`process_run_with_limits`, `process_wait`, and `shell` — JIT call sites "fall
back to the last definition when types are ambiguous … may still dispatch to
the wrong one". Collision-correctness risk adjacent to this file's concerns.

