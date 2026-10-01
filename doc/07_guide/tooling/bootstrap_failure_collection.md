# Collect bootstrap, build, and test failures

During bootstrap diagnosis, reach the end of all independently runnable build
and test work instead of ending the investigation at the first failure. This
is the shared agent policy for SPipe, bootstrap, builds, tests, and bug repair.
Native-build and the bootstrap phase matrix collect independent failures by
default on a host. CI (`CI=true` or `CI=1`) defaults to fail fast. Select the
policy with `--keep-going` or `--fail-fast`; the last explicit flag wins.
`SIMPLE_COMPILE_FAIL_FAST=0` or `1` overrides the CI/host default and is inherited
by worker processes. An empty or other environment value uses the CI/host
default. This policy does not change inventory scope (`normal` versus `full`).

The phase matrix retains its first failure and exits nonzero even if later rows
succeed. In fail-fast mode, unlaunched tasks and spec rows are `SKIPPED`; already
launched bounded workers finish. Missing prerequisites remain `BLOCKED` or
`UNSUPPORTED`, and invalid snapshots/admission remain fatal. Successful objects
and admitted cache entries survive either policy. A failed compile never gains
a successful output merely because diagnostic collection reached the end.

The regression `sh scripts/check/check-bootstrap-keep-going-policy.shs` exercises
production orchestration with failing/passing fake commands and inventory rows;
it also checks policy inheritance, ordered overrides, cache preservation, and
fatal snapshot admission. Other runners may still need their own policy wiring.

## Module diagnostics after a tool binary fails

The full phase verification profile runs `run_module_compile_inventory` after
the required full CLI, test runner, MCP and LSP binary attempts, including when
any of those binaries fails. The explicit slim Phase2 profile adds this sweep
only when its required CLI or test runner fails to become available.
The available phase producer compiles each `.spl` file under the configured
compiler, application, library and backend composition roots as a relocatable
object entry with its imports. This conservative source-root superset remains
available when binary closure discovery fails; it is not an exact failed-entry
closure. It deliberately includes platform-specific sources: compiler errors
remain visible rather than silently excluding files by filename guesses.

Phase2/3 use their supported pure-Simple positional `native-build` route with
the driver's `SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1` channel. Full phase compilers
use `--emit-object`. These are diagnostic object builds, not executable link,
runtime behavior or strict Stage4 admission evidence. The strict Stage4 profile
rejects object output and remains BLOCKED; the collector never clears that
profile to obtain a result. Missing or altered compiler/runtime authority also
blocks compilation. Successful object results cannot repair a failed binary row.

`BOOTSTRAP_VERIFY_MODULE_WORKERS` defaults to 2 (range 1–12). The scheduler caps
that count at `BOOTSTRAP_VERIFY_BUILD_THREADS` and divides the thread budget
among workers. Each bounded batch finishes before the next starts. Host policy
collects remaining independent modules; fail-fast records unlaunched modules as
SKIPPED, including the whole sweep after a prior binary failure.

Caches live under `module-diagnostics/<phase>/<producer-sha>/<input-identity>/`
with a stable hash of each relative module path. Attempts have separate logs,
object outputs, HOME and temporary directories; retries preserve module caches.
An absent, empty or symlink output cannot pass, even with exit zero. The emitted
file header must identify an ELF relocatable, COFF object or Mach-O object;
an executable accidentally written to an `.o` path fails as `invalid-object`.
This identifies the container kind without claiming complete object validation.
Coordinator failures reap already launched children and retain their caches.
Declaration
only modules and platform-incompatible modules may fail or produce no object;
those rows leave coverage incomplete. The Phase2 positional CLI currently also
rejects artifacts at or below 300 bytes, which can reject a valid tiny object.
Per-module producer receipts retain exact arguments and the existing toolchain
checks. Full source/runtime binding is revalidated before and after the sweep;
rows remain provisional until that final check succeeds. Every invocation also
checks the exact producer and frozen binding digest and uses the existing
command/toolchain guard. This avoids rescanning the entire source/runtime tree
three times per module. A global missing prerequisite is recorded once and
blocks remaining rows without repeating those checks. No cache reuse count is
claimed without producer evidence.

A bounded Windows probe on 2026-09-30 confirmed that the Phase2 positional
route needs the object environment channel: `--emit-object` alone was ignored
and attempted an executable link. With the supported environment channel, the
same no-main, no-import function fixture emitted a 566-byte AMD64 COFF object
in 5.875 seconds with the previous cache directory preserved. The log reports
HIR hits=0, misses=1 and native cached=0; this is not evidence of cache hits.
This validates command semantics, not a full module sweep. Evidence is under
`build/native_probe/module_object_probe/` (`result2.json`, `object.readobj.log`).

## Implementation language

Outside bootstrap orchestration, prefer Simple `.spl` for product code and
tools. When shell orchestration is necessary, prefer `.shs` and minimize new
Python, JavaScript, BAT, PowerShell, and plain `.sh` scripts. Bootstrap
orchestration retains its exception. Apply this choice to new work; do not
mass-rename or rewrite existing scripts merely to change their extension.

## Continue by dependency

Inventory the requested phases, entries, tool builds, and test shards before
launching them. Record dependencies and plan concurrency against available
memory and disk, with explicit per-process timeout budgets. Memory planning
controls scheduling; it does not impose an RSS cap when the user selected a
lane without memory caps. Preserve that selection. Continue independent
rows when another row fails; resource pressure queues work rather than launching
unbounded retries. Respect explicit user stop points and scope.

A produced compiler may start the next **diagnostic** phase once its immutable
bytes and producer identity are recorded and minimum sanity proves the required
operation works: launch it, compile a small representative fixture, and execute
that fixture with checked output. A version string or binary existence alone
is insufficient. Do not wait for full suite completion or formal phase admission
to start this diagnostic continuation. Label the compiler and descendants
unadmitted and retain their exact lineage. Failed qualification still blocks
admission, deployment, publication, and release.

A crash, timeout, missing artifact, or failed minimum sanity terminates that
process and blocks only descendants needing its unavailable capability. Keep
collecting from independent entries, platforms, phases with usable artifacts,
and test shards. Do not rerun a known crashing producer without a changed input
or a concrete bounded diagnostic hypothesis. If a wrapper exits early, use
supported independent entrypoints with equivalent identity and sanity checks;
record any remaining runner limitation instead of bypassing admission guards.

## Preserve truthful terminal results

Keep one terminal row per planned operation, with phase, producer hash, source
revision, entry/shard, exact command, log path, exit status, elapsed time,
dependency reason, and bug ID where applicable:

| Result | Meaning |
|--------|---------|
| PASS | Required operation and non-vacuous assertions actually succeeded. |
| FAILED | Operation ran and failed, crashed, timed out, or produced invalid evidence. |
| BLOCKED | A required artifact, capability, environment, or dependency is unavailable; name it. |
| SKIPPED | Deliberately outside the selected scope or stopped by the explicit budget; state why. |

Map runner-specific statuses such as `BLOCKED_UPSTREAM` to this report without
discarding their original values. Preserve raw output and test counters; zero
tests or exit zero without valid test evidence cannot earn PASS. Never suppress
errors with a successful fallback or turn failed assertions into skips. Aggregate
after all runnable rows finish: any FAILED or required BLOCKED/SKIPPED row keeps
the overall run unsuccessful and its orchestration exit status nonzero. If the
tool cannot express this, report its raw status and the unresolved aggregate
failure explicitly. No finite sweep proves the absence of all bugs.

## Repair without losing evidence

Group failures by the first actionable root cause, retain each affected row,
and claim or create a bug ID with an exact reproduction and artifact identity.
After fixing the owner, add a same-mechanism regression and a similar scenario;
link fixes and remaining blockers from the owning knowledge entry.

Preserve caches by phase, producer identity, and entry. Invalidate only proven
affected dependencies, or the affected entry if narrower correctness cannot be
established. Keep successful objects, logs, and unrelated caches; never share
writable caches between lanes or alter stamps to admit stale data. See the
[cache policy](bootstrap_cache_policy.md) for supported commands.

Run only the checks needed to resolve changed or failed evidence. Reuse recorded
green results for unchanged identities; changed producer/source inputs make
affected evidence stale and require explicit explanation before rechecking.
Stop repairs after at most three verify/fix cycles per feature, report remaining
failures and exact resume steps, and finish independent collection within the
declared budget. Collection is bounded work, not an endless repair loop.
