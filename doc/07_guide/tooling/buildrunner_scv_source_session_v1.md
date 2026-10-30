# BuildRunner opt-in frozen SCV source sessions

Status: production source and real assertion specs authored; native acceptance **not_run**. Phase 3 execution was explicitly deferred. This adds a source-only gate to the current BuildRunner, preserving its scheduler, task/run/result formats, task identities, environment context, process/reap proof and output verification.

Select `--scv-session FILE` with `run`, `verify`, `verify-settled`, `retire` or `abort-capture`, alongside the existing `--manifest`, `--state`, explicit `--source-root` and separate private `--output-root`. Other commands reject the option. Legacy invocations retain their existing transport defaults. A state directory containing an SCV binding requires the mode on later invocations.

The bounded, strict native SDN sidecar has this shape. Every declared task input needs exactly one row; these example paths must match the real task manifest. The manifest retains the input digests.

```sdn
schema_version: 1
source_scopes = ["src"]
cold_init: false
inputs |task, path, role|
    "compile", "src/main.spl", "source"
    "compile", "task-context/compile.sdn", "ordinary"
```

Unknown/duplicate fields, unsupported versions, missing/duplicate/extra role rows, source-scope mismatches and generated/external source scopes reject. Scopes are explicit portable subtrees of `src`, `test` or `examples/10_tooling`; filename suffixes do not establish roles. `cold_init` controls the existing compiler inventory owner only and never starts a native builder.

The first supported task shape is local `native-build` with relative `--source DIRECTORY`, `--entry FILE`, `--output FILE`, explicit `--backend llvm|cranelift` matching the task context, and optional `--entry-closure`/`--strip`. Each task must have one declared output matching `--output`. Unknown options, absolute source/entry/output paths, links/aliases and unrepresented configuration/source-root requests reject. This is deliberately a closed initial mode; other compilation forms use the legacy route until their inputs can be represented.

Set `SIMPLE_LIB` explicitly to a declared relative source scope before preparing the task context. The actual normalized worker environment must match that context. Both explicit source directories and the implicit library domain require complete frozen membership in the task's staged inputs. This prevents an application-only input list from silently using an unwitnessed library namespace. Empty/default installation library search and inherited SCV/source/external-root overrides are unsupported; production code does not mutate process-global snapshot bindings.

Under the existing manager lock, the session acquires the actual compiler source authority once, reads its exact immutable inventory pointer and adapts the actual V1 snapshot. It persists `state/scv-session.sdn`, binding the sidecar bytes, checkout/cache owners, snapshot metadata, raw inventory pointer, scopes and task admission digests. Reopening uses that saved pointer and snapshot; it never refreshes or reads CURRENT. A missing binding cannot adopt an existing journal, and a changed plan/task/snapshot binding refuses recovery. The tagged logical inventory identity and raw pointer are distinct.

Every startup resume, retained-output restoration, RUNNING recovery, failure re-admission, ready-task cache/dispatch, execution acceptance, `verify` and `verify-settled` uses the same additional source gate. Existing producer/declared-input/link/result/reap/output checks remain. The original live declared-input rehash is intentionally conservative: a concurrent checkout edit refuses admission even though dispatch always copies the selected source bytes from the frozen root. The unchanged transport copies ordinary inputs and relative producer bytes from their existing owner and verifies every staged digest; no second materializer or scheduler exists. Scheduler retries obtain an exact new attempt binding only after all other task fields match the saved request.

`source_only: true` and `full_artifact_authorized: false` are explicit. V1 still discloses unsupported editor overlays, generated/external/configuration semantics, filesystem event coverage, physical modes and aliases. These checks do not introduce semantic or cross-commit artifact reuse authority. The later Phase 3 fixture must supply the admitted runtime/toolchain and any required archives/configuration as existing digest-bound ordinary inputs/environment at their actual worker read paths. No native builder, new compiler workaround or fabricated cache-hit evidence is part of this change.

## Optional exact declared-input managed bridge

Authenticated task contexts may use `SIMPLE-BUILD-TASK-CONTEXT-2` with the V1
backend/runtime/policy/environment lines followed by exact target-layout and
configuration SHA-256 lines. Both new fields are required together; a backend
name or toolchain digest is not a target-layout digest. Existing V1 contexts
retain source-only behavior and record managed target/configuration unavailable.
No preparation command currently invents or upgrades these subjects.

For V2, the parent freezes the finite declared regular input set using actual
compiler frozen-inventory source bytes and no-follow digest-checked ordinary
input bytes. Exact file scopes describe the logical managed universe. Mode 420
describes normalized private staging, not observed physical source metadata.
The existing transport copies every task input from this private frozen tree
and rechecks each digest. Live checkout/producer checks remain conservative.

`state/scv-managed-session.sdn` binds managed snapshot IDs and graph bookkeeping
roots to the exact source-session record. The same additional gate covers
resume, cached results, dispatch, task acceptance and both verification commands.
This initial profile supports only its fixed sequence-zero set. Capture unknown
reasons, retired epochs/history digests and feed floor/event IDs are retained;
unknown or advanced histories refuse and cannot be reconstructed as complete.
Recovery requires a new owned run/state until actual producer reconciliation
and durable replay are integrated.

Editor overlays, generated/external producer receipts, filesystem event coverage,
physical modes/aliases and compiler semantic producers remain unavailable.
An empty graph does not publish any outgoing-use manifest or semantic receipt.
Artifact authorization and physical-filesystem completeness remain false.
The bridge performs no implicit physical eviction/GC. The manager now owns the
shared retention admission and reader lifecycle described below.
Feature execution remains NOT_RUN without an admitted general-purpose runtime.

## Retention ownership and pressure

Under the existing manager lock, BuildRunner hashes canonical state and checkout
roots plus the exact plan SHA-256 into one retention session ID. Before fresh
source acquisition **or** retained snapshot opening, it publishes a durable
capture reservation through the shared retention authority. Acquisition runs
after that authority's OS lock has been released. Every managed collector sees
the reservation; no expiry silently clears it.

After acquisition, the exact physical snapshot is admitted before inventory,
adapter, task-binding or staging readers. Admission binds both
`active_builds/<session>` and `snapshot_dependents/<session>`, plus an explicit
reader lease. This also covers the V1 source-only context profile. A capture or
admission error preserves whichever reservation or reader protection exists.

Fresh acquisition first requests accounting-only collection under its reservation
with `max_remove: 0`. Pressure refuses additional capture; retained sessions may
reopen under pressure to recover existing work. Initial fixed admission budgets
are 4,096 metadata nodes, 65,536 edges, 16,777,216 work units, 1 GiB of tracked
snapshot bytes and four retained units. These are unmeasured starting defaults,
not an optimum or a whole-store space bound. Shared chunks, immutable source
inventory history and private staging have separate owners. There is no new SDN
budget configuration or automatic deletion authorization in this profile.

Normal `run` code 0/1 releases only the active pin and reader lease, after actual
worker closure and successful task-database finalization. The durable dependent
pin remains for later resume and verification. Infrastructure failure,
cancellation and crashes retain reader protection. Verification releases active
protection only after successful existing verification **and** an independent
whole-journal settlement check over all retained retry slots. A verify failure
cannot erase a shared execution owner's unresolved reader lease.

## Explicit retirement and unattached capture abort

Use the same manifest, state, checkout, private output and source-session plan:

```text
buildrunner retire --manifest run.sdn --state /private/state --source-root /checkout --output-root /private/output --scv-session source-plan.sdn
buildrunner abort-capture --manifest run.sdn --state /private/state --source-root /checkout --output-root /private/output --scv-session source-plan.sdn
```

`retire` holds the manager lock and does not acquire, reopen or stage a snapshot.
It requires exact `SUCCEEDED`/`FAILED` journal rows, matching published receipts,
ordinary terminal results, and genuine transport tree-reap/capacity proof for
every retained retry attempt. Unknown task/attempt/host directories, incomplete
inventories, cancellation requests and unreaped or unresolved work refuse. This
first contract conservatively refuses dependency-`BLOCKED` rows: it has no
independent no-dispatch proof for them. Retirement therefore does not qualify
every possible terminal dependency graph.

Before unpinning, retirement atomically writes and reads back
`state/scv-retired.sdn`, binding the session, revision and exact source-record and
settled-journal digests. All later open/run/verify paths reject that marker,
including attempts to omit `--scv-session`. A matching retirement retry rechecks
the real proof and completes the idempotent store transaction; a store-lock
failure after the marker write cannot reopen the session or remove its pin.
Retirement removes only its own active/durable pins, lease and capture
reservation. It does not delete source data or other owners' roots.

`abort-capture` is for an explicitly abandoned capture that never attached a
snapshot or dispatched work, including a fresh preflight pressure refusal. The
same manager lock and canonical session subject apply. An error-aware bounded
directory listing must prove that the exact canonical state directory contains
only its regular `manager.lock`; source records, journals, attempts, retirement
markers, symlinks, unknown entries or an unreadable/missing inventory refuse.
The store independently refuses any own pin or lease even if app records were
removed. Only this session's unattached reservation is removed; no data is
deleted. Repeated explicit abort repeats the proof and is idempotent. Capture's
snapshot readers are synchronous parent work; detached snapshot-reading jobs
would require an additional real join proof before this profile could apply.

If pin admission succeeds and inventory or task binding fails before the source
record is written, attached protection may exist without a source record or
journal. Exact initialization replay is the current recovery path; abort refuses
the attached pin and retirement lacks settlement evidence. This is not general
abandoned-session or complete crash reclamation. No TTL, file flag, arbitrary
`BLOCKED` label or absence of a receipt authorizes cleanup.

## Sourceful regression scope

The source-session system spec covers real temporary Git checkouts, capture and
reopen failures, exact retry identity, source-only pins, cancellation before
dispatch, pressure refusal, explicit unattached abort, manager-lock contention,
attached-reader refusal and unavailable state inventories. Its permission test
requires a non-root POSIX user. The separately gated
`scv_retention_lifecycle_v2_spec.spl` uses an admitted native manager and Linux
cgroup-v2 worker with a compiled pure-Simple fixture child. That child writes
known test bytes, signals itself once, or waits for cancellation; its result is
**not real compilation qualification**. All process, capacity and reap evidence
comes from the actual worker. The integration covers normal reader release,
retry-history proof removal, actual cancellation, marker-before-unpin lock
failure, successful retirement and repeated retirement after success.

Both spec/manual pairs remain authored and **NOT_RUN**. Native compilation,
SPipe/docgen/manual-maintenance execution, performance and full release gates
remain pending an admitted general-purpose runtime; static review is not PASS.
