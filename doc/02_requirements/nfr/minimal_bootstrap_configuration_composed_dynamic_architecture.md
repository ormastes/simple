<!-- codex-design -->

# NFR Requirements: Minimal-Bootstrap Configuration-Composed Dynamic Architecture

## Status

Selected with the feature direction. Initial acceptance uses structural work
counters. Timing and RSS are observational and host-labeled until representative
baselines justify portable thresholds.

### NFR-001 — Determinism

Equivalent normalized composition inputs shall produce byte-identical SCI output, including stable section order, indices, digests, and provenance encoding.

### NFR-002 — Integrity and memory safety

Readers shall validate all arithmetic before slicing or allocation, reject integer overflow and overlap, authenticate each referenced section/artifact, and execute no constructors while reading configuration.

### NFR-003 — Least authority

Providers receive only SCI-declared host interfaces and capabilities. Ambient directory discovery, undeclared host APIs, path escape, and capability elevation are prohibited.

### NFR-004 — Startup work

Warm `simple-core --help` shall read indexed SCI command summaries without loading ordinary providers, scanning source trees/directories, invoking a compiler, or spawning a subprocess.

### NFR-005 — Startup structural work

Startup evidence shall report modules parsed/typed/lowered, objects generated,
providers packaged, links performed, SCI sections regenerated, and cache
hits/misses. CLI-0 performs no compilation, packaging, or linking. Timing may
be reported only with host, fixture, producer, and warm/cold labels.

### NFR-006 — Dispatch and rebuild structural work

Every dispatch/build receipt shall expose the structural counters and prove the
selected P0/P1/P2 boundary. Configuration-only mutation has zero code-work
counters. Timing is observational and not an initial PASS/FAIL gate.

### NFR-007 — Resident memory

Warm core plus mapped SCI shall report mapped bytes and max RSS with host, OS,
CPU, available memory, producer identity/stage, fixture, and sample count. RSS is
observational initially; provider-attributable RSS is reported separately.

### NFR-008 — Rebuild containment

App-metadata mutation shall compile zero Simple source files and invoke zero bootstrap targets. A provider-private mutation shall rebuild one provider plus at most its locked SCI projection and invoke zero core/compiler/bootstrap targets.

### NFR-009 — Cache reuse

Build receipts shall report action reuse and rebuilt counts. Unchanged edge-relevant identities shall retain downstream cache eligibility; cache-format evolution shall not delete prior namespaces during the build.

### NFR-010 — Diagnostics and observability

Composition compile/read, provider query, compatibility, and build-explain paths shall expose stable error codes plus human diagnostics. Timings, selected identities, closure counts, and bootstrap decisions shall be inspectable without logging credentials or configuration secrets.

### NFR-011 — Compatibility conservatism

Only proven `Exact` or `Compatible` evidence permits reuse/activation. `Unknown` rebuilds or fails closed according to context; it is never silently upgraded to compatible.

### NFR-012 — Verification convergence

Each acceptance criterion is verified at most once after it passes, with no more than three fix/verify cycles for the feature. Executable specs contain no placeholder passes and generated manuals contain no executable `.spl` files.
