# Counterpart Conformance — developer guide

Status as of 2026-08-09: **Wave 0 complete, Wave 1 partial.** Read the "What works
today" table before you rely on anything here. Nothing in this guide claims a
capability is reachable from the binary you run unless the table says so.

- Design: `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`
- Plan: `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`
- ADR (frozen contracts): `doc/04_architecture/infra/adr/adr_counterpart_conformance_contract_freeze_2026-08-09.md`

## What it is

One conformance pipeline under Modern SSpec for every differential and oracle
comparison — web against Chrome, shaping against HarfBuzz, Vulkan against
SwiftShader/Venus, crypto against NIST vectors and OpenSSL, compression against
zlib/zstd, and Simple's own CPU mode against its GPU mode.

```
Modern SSpec scenario → CounterpartEvidenceProvider → adapter → raw artifacts
  → converter graph → canonical artifacts → relation engine → CanonicalEvidence
  → Modern SSpec comparator → EvidenceManifest + ManualBlock[] → spipe_docgen
```

If you are about to write a second differential framework, don't — absorb it into
this one.

## What works today

| Capability | State | Evidence |
|---|---|---|
| Frozen contracts (plans, receipts, relations, gates) | **Working** | `bin/simple run test/01_unit/infra/counterpart/contract_model_spec.spl` → 18 examples, 0 failures, exit 0; two sabotage probes confirmed RED→GREEN |
| Adapter C ABI + mock adapter | **C layer working, unreachable from Simple** | Verified through a C driver; the Simple-side externs are unresolved — see the blocker below |
| Converter graph, relation engine, evidence projection | In flight | — |
| Package/build resolver (F2) | Not written | Lockfile records are declarations, not enforced |
| Isolated worker (F3), provider registry (F4) | Not written | — |
| Any real upstream provider (zlib, HarfBuzz, OpenSSL, Chrome, Venus) | Not started | — |

**Blocker:** `rt_counterpart_*` is not linked into the runtime, so
`src/lib/nogc_sync_mut/sffi/counterpart_abi.spl` cannot be called from Simple.
Details and the unblock steps:
`doc/08_tracking/bug/counterpart_abi_shim_not_linked_into_runtime_2026-08-09.md`.

## Declaring a plan

A plan names a boundary, an input, the sources to run, and the comparisons
between them. It is validated before any provider is loaded:

```simple
use std.common.spec.evidence.counterpart.model.{
    CounterpartRelation, OracleAuthority,
    counterpart_plan, counterpart_plan_rejections, plan_comparison, plan_source
}

val plan = counterpart_plan(
    "counterpart.web.style.v1",
    "web.resolve.computed_style@1",
    "web-pinned-deterministic",
    "test/fixtures/web/retained_panel.html",
    [
        plan_source("simple_cpu", "simple-web", "simple.web.cpu.style",
            OracleAuthority.self_execution_mode, true),
        plan_source("chrome", "chromium-cft-151", "chrome.computed_style",
            OracleAuthority.independent_reference, true)
    ],
    [plan_comparison("simple_cpu", "chrome", CounterpartRelation.canonical_exact)]
)

val rejections = counterpart_plan_rejections(plan)   # empty == admissible
```

An empty rejection list means the plan is *admissible*, not that the run passed.

## What the framework refuses, and why

These are the mistakes that make a conformance suite look green while proving
nothing. Each is a hard refusal, not a warning:

| Refusal | Reason |
|---|---|
| Boundary ID with no `@version` | A defaulted schema version silently compares two different schemas |
| Sources that are all `diagnostic_only` | Nothing present can serve as an oracle |
| Zero comparisons | An empty matrix reads as a pass |
| Tolerance with no stated reason | An unexplained tolerance is a fabricated expected value |
| A source compared with itself | Always agrees; proves nothing |
| All executed sources in one `independence_group` | Two wrappers over one engine are one reference |
| An artifact with zero items | Nothing was compared |
| A provider that did not run | UNAVAILABLE is never PASS, and `crashed` is not `unavailable` |
| Exact relation through a lossy converter | The route already discarded what "exact" was claiming |
| GPU source without submission / fence / device readback, or with `fallback_used` | The lane silently ran on CPU |

## Adding a provider

1. Write the adapter against `tools/counterpart/sdk/c/simple_counterpart_abi.h`.
   It links the upstream library or drives a process; it is always
   `libsimple_counterpart_<id>.so`. Never dlopen an upstream project directly —
   Chrome is process-driven, Vulkan dispatches through loader/layer/ICD, and
   SPIRV-Cross has no stable C++ ABI.
2. Add `config/counterpart/providers/<id>.sdn` — component IDs mapped onto
   boundary IDs, `independence_group`, supported relations and execution modes.
   Do not edit a central registry; the registry is generated from descriptors.
3. Add a lock record to `config/counterpart/counterpart.lock.sdn` pinning the
   upstream revision and every hash. Tests never fetch "latest" at run time.
4. Put every normalization rule in a **named, versioned converter**, never in the
   comparator, so it appears in the generated manual with its declared loss class.
5. Ship a sabotage that turns your lane green→red. "The adapter ran" is not an
   acceptance criterion.

## Running and verifying

```bash
bin/simple run test/01_unit/infra/counterpart/<spec>.spl   # NOT `bin/simple test`
```

`bin/simple test` routes typed-evidence specs through the daemon, which trips the
800-module transitive-import cap during load.

Two traps that will waste your afternoon:

- **`bin/simple lint` is fail-open on parse errors.** It printed
  `Lint passed: all files clean`, exit 0, for a module that could not parse. A
  green lint is not evidence the file compiles — always also run something that
  loads it. See
  `doc/08_tracking/bug/lint_reports_clean_on_module_that_fails_to_parse_2026-08-09.md`.
- **`@allow(primitive_api)` is the working suppression form; `#![allow(...)]` is a
  no-op** (the lint only matches lines beginning with `@`). But `@allow` is an
  outer attribute and binds to the next item, and `pub val` is not attributable —
  so the first item in the file must be a `fn`/`struct`/`enum`. The counterpart
  contracts put their two module constants below the first struct for exactly
  this reason.

## Extending the evidence, not the enum

Complex relations (`cross_decode`, `round_trip`, metamorphic invariants) live in
the counterpart relation engine and project *counts* into CanonicalEvidence:

```
counterpart.cross_decode.executed=16
counterpart.cross_decode.failed=0
counterpart.round_trip.failed=0
```

Do not widen the Modern SSpec `OracleMode` enum for them. `simple.sspec.evidence.v1`
stays stable; counterpart data rides in the opaque `simple.sspec.counterpart.v1`
extension, which carries refs only.
