# BuildRunner opt-in frozen SCV source sessions

Status: production source and real assertion specs authored; native acceptance **not_run**. Phase 3 execution was explicitly deferred. This adds a source-only gate to the current BuildRunner, preserving its scheduler, task/run/result formats, task identities, environment context, process/reap proof and output verification.

Select `--scv-session FILE` with `run`, `verify` or `verify-settled`, alongside the existing `--manifest`, `--state`, explicit `--source-root` and separate private `--output-root`. Other commands reject the option. Legacy invocations retain their existing transport defaults. A state directory containing an SCV binding requires the mode on later invocations.

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
The bridge performs no eviction/GC: shared retention admission, active pins and
worker-reap lease release are required before enabling managed eviction.
Feature execution remains NOT_RUN without an admitted general-purpose runtime.
