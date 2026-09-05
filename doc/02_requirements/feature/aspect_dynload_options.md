<!-- codex-research -->
# Aspect Dynamic Loading: Feature Requirement Options

**Status:** awaiting user selection; this is not a final requirements document.  
**Date:** 2026-08-20  
**Provenance:** synthesized by the highest-capability Codex audit session
`/root/audit_aspect_plan_completion`; lower-model sidecars: **N/A**.  
**Constraint:** do not implement a choice merely because it appears first.

Selections may mix compatible options across sections. A final
`doc/02_requirements/feature/aspect_dynload.md` must be created only after the
user chooses.

## F1 — Facet acquisition semantics

### F1-A: Static binding only

`receiver.try_facet<F>()` remains a compile-time-resolved optional conversion.
No expression is allowed to load an aspect. Dynamic packs may be activated only
by an explicit loader/startup API; calls see only already-published bindings.

**Pros:** smallest language surface; deterministic call behavior; easiest
resident/no-I/O proof; builds on current HIR/MIR.  
**Cons:** no transparent first-use loading; callers must coordinate activation;
does not fulfill designs that promise `facet<F>()` acquisition.  
**Effort:** **M**, approximately 6–10 source/test/doc files, mainly contract
cleanup, runtime execution tests, and product wiring.

### F1-B: Split probe and mandatory acquisition

Define `try_facet<F>()` as a non-loading resident probe returning an option.
Define `facet<F>()` as mandatory acquisition: before operational seal it may
verify/load and wait; after seal it succeeds only from a resident generation or
returns a phase-specific error. Static binding is an optimization preserving
those results.

**Pros:** clear optional versus mandatory behavior; permits ergonomic first
use; phase guard makes no-I/O behavior testable.  
**Cons:** a call can have high first-use latency before seal; requires catalog,
loader, error, and concurrency integration through compiler and runtime.  
**Effort:** **L**, approximately 15–25 source/test/doc files.

### F1-C: Explicit asynchronous dynamic acquisition

Keep `try_facet<F>()` resident-only. Add an explicit loader operation such as
`load_facet<F>() -> Future<Result<FacetHandle<F>>>`; a handle pins a named pack
generation. `facet<F>()`, if retained, is only a handle/local resident lookup
and never blocks.

**Pros:** latency and blocking are visible in types; natural cancellation and
timeout surface; suitable for GUI/server startup.  
**Cons:** largest API change; requires task/future semantics and native
concurrency evidence; more verbose for simple programs.  
**Effort:** **XL**, approximately 25–40 source/test/doc files.

## F2 — Resident and no-I/O policy

### F2-A: One fail-closed operational policy

Treat `@resident`, `@no_io`, realtime/interrupt/noalloc contexts, and
post-`seal_operational_state` acquisition as a union: every possible path must
already be mapped/pinned and must not invoke filesystem, decompression,
relocation, allocation, or blocking waits. Enforce with compiler call-graph
diagnostics plus runtime phase assertions at indirect boundaries.

**Pros:** strongest and simplest safety promise; one diagnostic model; fail
closed when evidence is incomplete.  
**Cons:** conservative false positives; prevents useful resident-but-allocating
or nonblocking-but-not-realtime code.  
**Effort:** **L**, approximately 12–20 files plus driver and runtime integration.

### F2-B: Composed capability policies

Specify separate guarantees: `@no_io` prohibits I/O; `@resident` requires mapped
code/data and pins its generation; realtime additionally prohibits allocation,
locks, and blocking. Operational seal controls dynamic loader transitions but
does not silently imply every annotation.

**Pros:** precise and reusable; supports more workloads; diagnostics can name
the violated capability.  
**Cons:** more states and test combinations; indirect calls need capability
summaries and conservative joins.  
**Effort:** **XL**, approximately 20–35 files including summary IR.

### F2-C: Preload-list policy without source annotations

Applications declare a closed startup preload list. Successful seal proves all
listed facets are authenticated, decoded, mapped, relocated, and pinned. After
seal all loader I/O APIs reject calls. Static annotations are deferred.

**Pros:** implementable without whole-program effect analysis; easily audited
at startup; strong temporal boundary.  
**Cons:** coarser developer feedback; misses indirect user I/O unrelated to the
loader; preload manifests can become operationally burdensome.  
**Effort:** **M–L**, approximately 10–18 files.

## F3 — Pack authentication and compression profile

### F3-A: Unsigned, uncompressed baseline

Require exact content digests and format bounds, but prohibit signed and zstd
flags in production until their profiles are complete. Packs come only from an
already trusted local installation boundary.

**Pros:** honest current security claim; smallest attack surface; enables the
loader cutover without fake key custody.  
**Cons:** no publisher authentication; larger packs; insufficient for remote or
untrusted distribution.  
**Effort:** **S–M**, approximately 5–9 files for fail-closed policy and evidence.

### F3-B: Pinned release root plus optional zstd

Ship one versioned public verification root with the runtime; the release
pipeline signs canonical pack bytes using externally held private material.
Allow zstd frames with no dictionary or with a repository-defined dictionary
ID/profile. Verify signature and compressed length before bounded decode; reject
unknown roots/dictionaries.

**Pros:** practical publisher authentication and compression; bounded
compatibility surface.  
**Cons:** single-root recovery/rotation remains operationally delicate; needs
release-pipeline ownership and reproducible canonicalization.  
**Effort:** **L**, approximately 15–25 files plus CI/secure-key integration.

### F3-C: Rotatable threshold roots and profiled dictionaries

Adopt a TUF-like signed-root model with key IDs, threshold signatures, version,
expiry, rotation/revocation, rollback protection, and separately versioned zstd
dictionaries. Authenticate the manifest and compressed payload before bounded
decode; publish a generation only after every member verifies.

**Pros:** strongest update and compromise recovery; explicit long-lived format
governance; supports remote distribution.  
**Cons:** substantial metadata, client state, clock/expiry, release operations,
and recovery complexity.  
**Effort:** **XL**, approximately 30–50 files plus operational infrastructure.

## F4 — Lifecycle, concurrency, and update model

### F4-A: Load once and pin for process lifetime

Each `(pack_id, generation, facet_id)` has a once-cell. One caller activates;
others wait and observe the same success or failure through a happens-before
edge. Successful generations remain pinned until process exit. No retry after a
terminal integrity failure; transient acquisition failures may be retried only
through an explicit administration API.

**Pros:** smallest correct concurrent state machine; no use-after-unload;
straightforward resident guarantee.  
**Cons:** RSS cannot be reclaimed; updates require process restart; failure
classification is required.  
**Effort:** **M–L**, approximately 10–18 files and native contention tests.

### F4-B: Immutable generations with handle-scoped pinning

Activation publishes an immutable generation. Typed facet handles increment a
generation pin; unload removes it from discovery and waits for all handles and
indirect-slot references to quiesce before unmapping. New acquisitions may bind
to a newer generation; old handles remain stable.

**Pros:** safe rolling update and eventual reclamation; explicit ownership;
stable behavior for existing callers.  
**Cons:** requires handle propagation, epoch/refcount correctness, patchpoint
accounting, and difficult race testing.  
**Effort:** **XL**, approximately 25–45 files.

### F4-C: Serialized loader service with no public unload

All catalog, activation, and publication transitions run through one bounded
loader actor/service; concurrent callers receive futures. Generations can be
superseded for new calls, but old code stays mapped until exit. Dispatch slots
publish only after a full generation succeeds.

**Pros:** simple state ownership and failure fan-out; avoids lock/CAS state
explosion; permits update without unsafe unmap.  
**Cons:** service/queue is a potential bottleneck; depends on trustworthy task
runtime; still retains old-generation RSS.  
**Effort:** **L**, approximately 18–30 files.

## F5 — Compiler/loader binding ownership

### F5-A: Loader-owned numeric IDs from a compiler-emitted manifest

The compiler emits stable symbolic joinpoint/facet keys. The pack builder
assigns generation-local numeric IDs and writes an immutable binding manifest;
the loader validates and resolves it before publication.

**Pros:** keeps dynamic packaging policy out of the front end; permits compact
runtime tables.  
**Cons:** IDs are not stable across builds; debugging needs symbol maps; all
references must be resolved before publish.  
**Effort:** **L**, approximately 15–25 files.

### F5-B: Compiler-owned stable content-derived IDs

The compiler derives IDs from canonical module/type/member identities with a
specified collision check. Pack and loader consume the same IDs; binding
summaries record required and provided IDs.

**Pros:** reproducible cross-pack linking and diagnostics; fewer relocation
names at runtime.  
**Cons:** canonical-name/version rules become ABI; collision and rename policy
are permanent compatibility concerns.  
**Effort:** **L–XL**, approximately 20–35 files plus ABI documentation.

### F5-C: Symbolic binding through publication, numeric cache afterward

Packs carry canonical symbolic keys. The loader validates all keys, allocates
process-local dense IDs, then publishes immutable lookup/slot tables. Numeric
IDs never cross the process boundary.

**Pros:** avoids permanent numeric ABI; dense hot tables; easy collision
diagnostics.  
**Cons:** greater startup work and metadata; stable cache persistence is harder;
resident seal must complete the entire resolution pass.  
**Effort:** **L**, approximately 18–30 files.

## User selection requested

Choose one option from each of F1–F5, or explicitly defer a section. Also state
whether remote/untrusted pack distribution is in scope for the first release;
that answer materially affects F3. No final feature requirements should be
written until these choices are confirmed.

