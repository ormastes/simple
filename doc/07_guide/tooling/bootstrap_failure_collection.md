# Collect bootstrap, build, and test failures

During bootstrap diagnosis, reach the end of all independently runnable build
and test work instead of ending the investigation at the first failure. This
is the shared agent policy for SPipe, bootstrap, builds, tests, and bug repair.
Full bootstrap and its phase matrix collect independent failures by default on
hosts and CI (`CI=true` or `CI=1`). Compatible caches are reused by default.
Select the
policy with `--keep-going` or `--fail-fast`; the last explicit flag wins.
`SIMPLE_COMPILE_FAIL_FAST=0` or `1` overrides that default and is inherited
by worker processes. An empty or other environment value uses the go-to-end
default. This policy does not change inventory scope (`normal` versus `full`).

The phase matrix retains its first failure and exits nonzero even if later rows
succeed. In fail-fast mode, unlaunched tasks and spec rows are `SKIPPED`; already
launched bounded workers finish. Missing prerequisites remain `BLOCKED` or
`UNSUPPORTED`. Invalid snapshots/admission remain fatal to the canonical
admitted result, not to separately identified diagnostic work. Successful objects
and admitted cache entries survive either policy. A failed compile never gains
a successful output merely because diagnostic collection reached the end.

The regression `sh scripts/check/check-bootstrap-keep-going-policy.shs` exercises
production orchestration with failing/passing fake commands and inventory rows;
it also checks policy inheritance, ordered overrides, cache preservation, and
fatal snapshot admission. Other runners may still need their own policy wiring.

## Agent continuation and explicit diagnostic exceptions

Always finish the finite inventory of independently runnable modules, binary
builds and tests. A failed row is a result to collect, not a reason to stop the
whole pipeline. Let healthy sibling jobs finish; after collecting failures,
group them by cause and delegate independent repairs to parallel agents with
separate writable source/cache ownership. A repair already understood may run
while collection continues. Distinguish logic defects, performance defects,
resource-policy exits and unavailable prerequisites.

When a bug appears during an active diagnostic bootstrap, register it in the
bug database and repair it in parallel. Prefer a scoped, semantics-preserving
workaround with the current compiler over returning to an earlier compiler or
rebuilding the producer immediately. Keep the failed attempt and workaround
identity separate. Apply changed inputs only to a new isolated attempt after
the relevant owner has finished; do not patch a running source snapshot.
Continue remaining independent cases to the end of Phase 4 where prerequisites
permit. After that collection run ends, rebuild the full chain with accumulated
fixes and required checks restored. A workaround is not proof that the underlying
bug is fixed, and cannot turn a failed assertion or missing output into a pass.

For every performance fix, check memory behavior as well as elapsed time. For
every memory fix, check performance as well as lifetime and peak usage. Run
relevant correctness regressions in both cases. Record comparable inputs and
producer identities; measurements without a comparable baseline are evidence,
not a claimed improvement. Preserve valid caches while making these comparisons.

When the user authorizes continuation past a time, memory or other policy
failure, record that authorization and the exact disabled check in a separate
**DIAGNOSTIC** attempt. Continue eligible work with elapsed-time, memory/RSS,
process-tree, progress and exit-status monitoring. Monitoring must not silently
re-enable the disabled kill threshold. Keep any other selected limits explicit;
do not claim a watchdog was disabled when an enclosing job still enforces it.
Use supported per-attempt settings, or a reviewed isolated diagnostic source
change when no setting exists. Preserve the original failed receipt and cache.
Do not repeatedly request permission already granted for that scoped exception.

An exception changes diagnostic execution policy, not facts: retain actual
source/producer/runtime/tool hashes, label altered inputs and descendants, and
never forge PASS, admission, test counts or cache compatibility. Do not turn
invalid inputs, missing binaries, empty payloads or failed assertions into
successful results. A disabled policy check does not authorize unsafe memory
access or a false provenance claim. Restore normal checks and obtain the
required verification before formal admission, deployment or release promotion.

Before a dependent provisional phase starts, the exact produced compiler must
compile a real Hello World fixture **and its output executable must run with
the expected output and exit status**. Record both commands and artifacts.
This gate permits diagnostic continuation before full qualification; it does
not grant admission. If Hello fails, record its failing boundary and continue
independent builds/tests or an explicitly authorized diagnostic repair of that
boundary. Do not label the dependent phase runnable from binary existence alone.

At the next actual restart, fetch the requested release branch and integrate
reviewed, applicable unmerged fixes in an isolated source owner. Coordinate with
their owners; preserve unrelated work and do not take over active drafts. Freeze
the resulting revision/patch identities before launching. Never mutate a live
producer or source snapshot. Reuse compatible persisted frontend/HIR/native
caches; changed inputs invalidate only the scope the cache contract requires.

The Windows LLVM/Cranelift repair request recorded on 2026-10-03 selects 40
backend jobs per lane, parallel failure collection, monitored diagnostic policy
exceptions, and Hello-gated provisional continuation. This is the active repair
profile, not a universal worker count: later explicit user choices supersede
it. Frontend process fanout must account for shared host and enclosing process
budgets; backend thread count is not permission to spawn that many large HIR
processes. Keep performance and correctness fixes separate when requested.

## Canonical managed Phase 3 and Phase 4

The grouped canonical wrapper schedules fourteen binary tasks, six three-case
compiler/loader/interpreter suites, and four index/module pairs across both
phases and LLVM/Cranelift. A verified compiler
`ERROR` with exit 1 continues independent tasks; a failed index blocks only its
own module group. The task-outcomes TSV is scheduling evidence, not an admission
receipt. Any failed or blocked task prevents the canonical PASS receipt.

Canonical admitted continuation requires the updated compiled manager: exit 1 is reserved for an
identity-checked compiler failure with actual tree reap and a retained matching
result. Launch rejection, timeout, cancellation, unknown crash, capacity,
integrity, and cleanup errors abort with exit 2. Retained failures are admitted
again on resume. The owner stop and systemic stop paths are
`SIMPLE_MODULE_COLLECTION_STOP_REQUEST_FILE` and
`SIMPLE_MODULE_SYSTEMIC_STOP_FILE`; they stop the next scheduling boundary.
They do not replace process-owner cancellation of an already active task.

The canonical resource policy defaults to one attempt. Deterministic compiler
`ERROR/1` is terminal even with a larger explicit attempt budget; unrelated
groups continue. The shell regression is
`scripts/bootstrap/tests/managed-task-schedule-test.shs`. Native policy and
manager tests remain required before qualification. These are current canonical
runner semantics. A user-authorized diagnostic exception uses a separate,
explicitly labeled attempt or independent entrypoint; it does not rewrite an
exit-2 receipt or stop unrelated runnable work.

The aggregate phase owner queues two isolated phase tasks, reserving their
full memory caps, disk growth and CPU demand before staging/spawn. Each phase
runs only one native module group at a time, leaving space for its managers.
Unknown cleanup retains its reservation and blocks recovery. Phase journals,
scratch snapshots and hash files are private; the parent merges after both
owned trees are reaped. Source and native enforcement are still unqualified
until the rebuilt manager passes actual overlap, cancellation and recovery
tests. Shell spy tests do not prove native enforcement.

The aggregate lifetime covers both execution and resource waiting. The default
six-hour parent lease is the effective upper bound for a phase started under
it, even though generic task manifests permit up to twenty-four hours. A late
phase receives only the remaining parent lifetime. Parent expiry cancels and
reaps the owned trees; it does not promise twenty-four hours or authorize a
fresh attempt. Timeout recovery needs preserved, validated checkpoint progress
and a presealed attempt budget; absent that proof the run remains aborted.

Do not deploy the new shell around old manager images. The canonical image
preparer compares its full source snapshot to the admitted Stage 2 snapshot;
there is no independent tool-source closure authority. Rebuild and admit a
candidate containing the manager changes, then prepare all eight manager
images from that same authority. Do not rewrite an older admission receipt.

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

### Full bootstrap execution graph

For the full profile, plan the following work for both LLVM and Cranelift.
The user's selected Windows build/test budget is 80 jobs; divide available
capacity among concurrent lanes and retain memory-aware admission. Eighty
code-generation jobs do not imply eighty independent frontend processes.

| Producer ready | Work to collect | Diagnostic continuation |
|---|---|---|
| Phase 1 | Whole Phase 1 test inventory | Build Phase 2 after the Phase 1 collection reaches its terminal summary. Record failures without discarding a usable, sanity-tested producer. |
| Phase 2 plus compile-and-run sanity | Build, enumerate and execute compiler, interpreter and loader test binaries for each backend | Start Phase 3 and early Phase 4 using Phase 2 concurrently with tests. |
| Phase 3 plus compile-and-run sanity | Whole Phase 3 inventory, including binary tools and library tests | Build Phase 4 using Phase 3 concurrently with tests. |
| Either Phase 4 product cohort | Product sanity and the whole Phase 4 test inventory | Retain separate Phase-2-produced and Phase-3-produced results; neither substitutes for the other. |

Each backend has three Phase 2 subsystem binaries, six across both backends.
Use Simple's existing aggregate test generation and registry, enumerate the
actual cases first, then execute every runnable case. Record discovered,
executed, passed, failed and blocked counts separately; do not assume a target
count or substitute tests of a third-party framework. A compiler-only CLI
cannot stand in for the generated test binary or the full CLI's whole suite.

These are execution requirements, not a claim that every platform wrapper
already implements this graph. A runner lacking an edge must report that gap
and use an identity-checked independent diagnostic lane until it is wired.
Formal qualification, lineage admission and publication still require all
their evidence; early descendants remain quarantined.

### Bind newly built producers between waves

A fresh bootstrap cannot validate the hashes of compilers it has not built.
Construct each next wave after the preceding producer and its compile-and-run
sanity task have retained terminal evidence. The managed task owner must bind
the actual compiler output path and digest into that wave's commands and cache
identity. A static inventory that accepts only pre-existing compilers does not
implement the fresh bootstrap graph above.

The implementation lane adds `managed-tasks-next-producer` to the existing
managed owner and `managed-next-producer-launch.shs` as argument transport.
Its native factory checks remain pending until exercised with a built compiler;
passing shell transport fixtures does not qualify the factory. Keep the whole
test inventory and early build waves independent after producer sanity, and
retain failed test summaries as failures.

`--full-bootstrap --stop-after-seed` prepares the canonical seed generation and
writes `phase1-seed.env`. It records whole tests as `NOT_RUN`, Stage 2 as
unadmitted and backend dynload as unqualified. Combining seed-stop with receipt
validation, resume, deployment or later-phase stop options is an error before
dispatch; no alternate exit may be mistaken for seed preparation success.

### Windows RC1 completion scope

For the current release, one successful host qualifies the RC: Windows is the
RC1 host. Complete its requested bootstrap graph, required test inventories
and local deployment before creating the release tag or publishing. Linux,
macOS and BSD are RC2 targets; record them as unverified for RC1 rather than
requiring their success or claiming cross-platform validation. Stop GitHub
synchronization during the local repair/build cycle. After local success,
inspect current remote state before the requested branch update, landing and
tag publication, and check the remote release result. A Windows-only scope
does not waive failed Windows tests or missing Windows artifacts.

Inventory the requested phases, entries, tool builds, and test shards before
launching them. Record dependencies and plan concurrency against available
memory and disk, with explicit per-process timeout budgets. Memory planning
controls scheduling; it does not impose an RSS cap when the user selected a
lane without memory caps. Preserve that selection. Continue independent
rows when another row fails; resource pressure queues work rather than launching
unbounded retries. Respect explicit user stop points and scope.

A produced compiler may start the next **diagnostic** phase once its immutable
bytes and producer identity are recorded and minimum sanity proves the required
operation works: launch it, compile Hello World, and execute its output with
checked output and exit status. Add another representative fixture when the
next phase requires a capability that Hello does not exercise. Binary existence
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
record any remaining runner limitation. Apply a user-authorized diagnostic
policy exception in its own attempt; never bypass guards to publish admission.

## Preserve truthful terminal results

When using the Rust seed for bootstrap with `--runtime-bundle core-c-bootstrap`,
the runtime source checkout takes precedence over a prebuilt `--runtime-path`.
The current source resolver searches the working directory's ancestors, then
the seed's build-time manifest ancestors. `SIMPLE_PROJECT_ROOT` alone does not
select this C runtime source. Run from the intended frozen checkout and retain
the actual C compiler input paths/hashes in the receipt. An explicit runtime
path is not evidence that a provider source fix was compiled. This rule is
specific to that seed runtime lane; inspect the actual command owner for other
producers instead of assuming identical selection behavior.

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

### Windows log observers and collector failures

Open an active temporary log with read, write **and delete** sharing. A reader
that denies delete sharing can prevent the collector's final rename or cleanup:
a controlled Windows test reproduced collector exit 126 and a missing receipt
even though the child had already returned its ordinary failure. Avoid plain
`Get-Content` for active temporary logs; use an explicit shared file handle or
wait for the published terminal log.

Capture the collector's own stdout and stderr separately from its bounded child
log. A missing collector receipt is a process-owner failure, not a successful
or ordinary failed compiler receipt. Preserve the raw child evidence and the
reservation until closure is proved or explicitly recovered under the shared
admission lock. External recovery must retain its own evidence and must never
fabricate the missing native completion receipt.

## Repair without losing evidence

Group failures by the first actionable root cause, retain each affected row,
and claim or create a bug ID with an exact reproduction and artifact identity.
Assign independent root causes to parallel repair agents with explicit file and
cache ownership. After fixing the owner, add a same-mechanism regression and a similar scenario;
link fixes and remaining blockers from the owning knowledge entry.

Preserve caches by phase, producer identity, and entry. Invalidate only proven
affected dependencies, or the affected entry if narrower correctness cannot be
established. Keep successful objects, logs, and unrelated caches; never share
writable caches between lanes or alter stamps to admit stale data. See the
[cache policy](bootstrap_cache_policy.md) for supported commands.

Run only the checks needed to resolve changed or failed evidence. Reuse recorded
green results for unchanged identities; changed producer/source inputs make
affected evidence stale and require explicit explanation before rechecking.
Use at most three verify/fix cycles per scoped cause by default. On exhaustion,
report that cause and its resume steps while finishing other independent rows.
Record an explicit user-directed exception before additional finite repair
cycles; do not infer unlimited retries. Never repeat an identical failing
command without a changed input or concrete diagnostic hypothesis, or replay
green checks for unchanged identities. Stop at convergence. Completing a finite
work graph is different from repeatedly restarting the same failed operation.

At the third unresolved cycle, enter or update the canonical bug database with
the failure group, affected rows, producer/source identities, three attempt
receipts and reproduction. Record a narrow workaround with its bug link,
scope, original behavior and removal/retest condition. A workaround may route
independent diagnostic work around the unavailable operation; it cannot turn
a failed assertion into PASS, fabricate an artifact, or admit a stale cache.
If no valid workaround exists, leave that dependency BLOCKED and continue
other work. Preserve progress rather than rebuilding from Phase 1. A later
rebuild must revisit the owning bug and verify the intended path before
removing the workaround; restarting a process does not reset the repair count.
