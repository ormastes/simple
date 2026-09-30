# Collect bootstrap, build, and test failures

During bootstrap diagnosis, reach the end of all independently runnable build
and test work instead of ending the investigation at the first failure. This
is the shared agent policy for SPipe, bootstrap, builds, tests, and bug repair.
It does not assert that every runner already implements this scheduling.

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
