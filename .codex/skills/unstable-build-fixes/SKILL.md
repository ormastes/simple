---
name: unstable-build-fixes
description: Use when a Simple bootstrap/native-build is unstable, slow, or failing one bug at a time and needs cache-preserving repairs, isolated parallel mini builds, independent failure collection, and bounded fix/rebuild cycles toward a working Simple executable.
---

# Unstable Build Fixes

## Bootstrap failure collection

Collect independent build and test failures before reporting. A usable compiler plus minimum sanity can start the next diagnostic phase while qualification continues; formal admission remains required for promotion. Keep phase/producer/entry caches and stop repair after at most three cycles. Follow the
[shared collection policy](../../../doc/07_guide/tooling/bootstrap_failure_collection.md) for terminal statuses, budgets,
cache preservation, and bug evidence. Host native-build/bootstrap runs default
to collecting independent failures; CI=true/1 defaults to fail fast. Use
`--keep-going` to collect CI diagnostics or `--fail-fast` for a short host run.
The last flag wins over `SIMPLE_COMPILE_FAIL_FAST=0|1`, which overrides CI/host
defaults. Preserve nonzero aggregate failure and explicit unrun SKIPPED/BLOCKED
rows; never bypass snapshot or admission failures to continue.

Goal: produce the requested Simple executable without throwing away useful cache.

Prefer Simple `.spl` for product and tool fixes. Outside bootstrap orchestration,
use `.shs` when shell glue is necessary and minimize new Python, JavaScript,
BAT, PowerShell, and plain `.sh` scripts. The bootstrap orchestration exception
does not justify moving product implementation into scripts or mass-renaming
existing files.

## Cache policy during repairs

Use cached builds until the known failures are fixed, then perform one explicit
clean rebuild as the final verification. Follow the
[bootstrap cache guide](../../../doc/07_guide/tooling/bootstrap_cache_policy.md)
for supported invalidation commands and their scope.

- Before creating a cache, locate the previous attempt's cache for the same
  platform, phase and entry. Compare its recorded producer, source/dependencies,
  build options, runtime and tool identities. A new attempt or worktree alone
  does not justify starting over.
- Resume compatible completed objects, persisted frontend/HIR records, runtime
  objects and Cargo outputs. Preserve failed caches and attempt logs. Do not
  claim that in-memory HIR can be resumed when it was never persisted.
- Keep frontend/HIR persistence enabled during repairs. A cold-cache speed or
  memory comparison alone does not justify disabling it: `SIMPLE_FRONTEND_CACHE=0`
  also disables the HIR cache. Record any demonstrated correctness blocker
  before disabling persistence for a bounded diagnostic.
- After a fix, explicitly invalidate the affected work. Use dependency-level
  invalidation when the cache owner can prove it correct; otherwise invalidate
  the affected entry and state why. Preserve other phases, entries and valid
  dependencies. Never rewrite identity stamps to make stale objects look valid.
- Before an unavoidable rebuild, name the incompatible input and affected
  scope. Record actual reuse counts, such as
  `Cache: reused 117 modules; rebuilt 2.` A directory's existence is not a hit.
- Keep live builds and their caches intact. Parallel lanes need separate writable
  caches; reuse an idle compatible lane rather than inventing a fresh directory
  for every retry. A cache donor must be idle before copying its mutable files.
- Defer the clean verification until fixes and focused checks pass, unless the
  user explicitly requests a clean build earlier. Keep the successful cached
  artifacts and evidence while qualifying the clean output separately.

## Rules

- Link temporary source workarounds to their owning bug using an immediately
  preceding `# @workaround bug=<canonical-id> [recover=<7..64hex>] [reason=<text>]`
  comment (`//` is also supported). Follow the accepted
  [workaround workflow](../../../doc/07_guide/tooling/bug_linked_workarounds.md);
  runtime qualification is pending. Ordinary
  `simple check-dbs bugs --bug=<canonical-id>` reads the derived index only;
  missing index or HEAD mismatch requires explicit
  `simple check-dbs --fullscan bugs` reconciliation. Fix the bug owner, review
  related links, then narrowly restore intended code. Recovery hashes never
  authorize automatic checkout/reset.
- Start dependent Phase 3/4 diagnostic builds when their required compiler
  binary exists, concurrently with upstream admission and independent Windows/
  Linux lanes. Use immutable producer bytes and isolated caches/outputs, with
  CPU and memory budgets. Keep results provisional until admission and lineage
  pass; binary existence is not an admission result.

- Keep one main cache-backed build as source of truth:
  `--cache-dir build/bootstrap/native_cache --mode dynload`.
- Preserve caches between retries; use explicit scoped invalidation for changed
  inputs and explicit clean rebuild only at the verification boundary above.
- Do not run parallel writers into the same cache dir. Use isolated shard caches:
  `build/mini_cache_<entry>`.
- Bind tool caches to both the producing compiler phase and the entry closure.
  A Stage 2, Stage 3, or Stage 4 compiler must never share a writable full-CLI
  or test-runner cache with another generation. Prefer:
  `build/bootstrap/tool_cache/<phase>/<compiler-sha>/<full-cli|test-runner>`.
  Record the producer binary SHA-256 and frozen source revision beside each
  cache. Reuse that exact cache for incremental retries of the same lineage.
- Build both the full CLI and test runner for each requested producer phase.
  The Stage 2/3 bootstrap CLI is compiler-only; `test --whole` becomes valid
  only on the non-vacuous full-CLI artifact. Require a `Results:` line—exit 0
  without test output is not evidence.
- If a source fix lands while a build is still before object output, prefer letting it fail or finish. Restart only when no cache/output can be lost.
- Keep every log under `build/mini_builds/` or `build/native_probe/`.
- Set `SIMPLE_NO_STUB_FALLBACK=1` for every candidate or verification build;
  a binary containing generated unresolved stubs is debug evidence only.

## Loop

1. Start or keep the main build:
   ```bash
   bin/simple native-build --backend cranelift --source src/compiler --source src/app --source src/lib \
     --entry-closure --threads 8 --cache-dir build/bootstrap/native_cache --mode dynload \
     --entry src/app/cli/main.spl -o build/native_probe/simple
   ```
2. Run parallel mini builds with separate caches for early failures:
   - `src/app/cli/bootstrap_main.spl` -> `build/mini_cache_bootstrap`
   - `src/app/cli/native_build_main.spl` -> `build/mini_cache_native_build`
   - `src/app/mcp/main.spl` -> `build/mini_cache_mcp`
   - `src/app/cli/_CliMain/main_and_help.spl` -> phase-bound `full-cli`
   - `src/app/test_runner_new/main.spl` -> phase-bound `test-runner`
3. Finish independently runnable builds and test shards after an error; a crash
   blocks only its dependent chain. Group failures by the first real error,
   retain every affected row, and attach bug IDs and exact reproductions.
4. Fix the smallest shared root cause. Add a focused regression and a similar
   scenario for the same mechanism.
5. Rerun only failed shards first, reusing their compatible caches and recording
   any explicit invalidation needed for the fix.
6. Resume the main build with its compatible cache. Respect the session's
   maximum of three verify/fix cycles; reuse green evidence for unchanged
   inputs. Report unresolved failures and resume steps when the limit is reached.
7. Once fixes and focused checks pass, perform the requested final clean build
   and sanity checks. Binary existence alone is not completion; report the
   actual requested executable behavior and any remaining verification gaps.

## Patterns

- If `--entry-closure` is CPU-bound before HIR/driver debug output, inspect the
  closure queue first. Shared imports need a queued-set as well as `seen`;
  checking only processed files can enqueue the same module many times.
- If LLVM reaches `llc` or link with an undefined runtime helper, fix the call
  name and declaration together. For example, `get_args`/`get_cli_args` should
  lower to the exported runtime symbol `rt_get_args`, and every text/lib LLVM
  declaration list must include that symbol.
- If a bootstrap fast path mirrors a normal lowering path, preserve the normal
  scope and state side effects (`push_scope`/`pop_scope`, `has` flags, call-frame
  snapshots). Fast paths may avoid fragile payload extraction, but not semantic
  state.

## Error Triage

Use:
```bash
rg -n "error:|FAILED|Failed|native-build worker|Bootstrap LLVM|llc failed|unknown extern|undefined|mismatch" <log>
find <cache-dir> -name '*.o' | wc -l
```

Ignore warning-only output unless it is the only changed behavior.
