# Facet Registry / AspectCatalog Specification

> Vertical slice of the aspect-facet dynload design

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Facet Registry / AspectCatalog Specification

Vertical slice of the aspect-facet dynload design

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/facet_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Vertical slice of the aspect-facet dynload design
(doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md).

Proves the non-negotiable invariant: an optional aspect that is absent (not
loaded) leaves the core path fully working — a facet request answers with a
TYPED absence reason (never a crash, never a silent default), and a present
aspect actually resolves (positive control: the feature cannot pass by always
answering "absent").

## Scenarios

### AspectCatalog facet binding and routing

#### routes a bound facet on a loaded aspect to its implementation (present case)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes a bound facet on a loaded aspect to its implementation (present case)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes a bound facet on a loaded aspect to its implementation (present case)")
val cat = catalog_new()
expect catalog_register_aspect(cat, "debug", "packs/debug.smf") == true
expect catalog_bind_facet(cat, "debug", "Debuggable", "storage.cache.LruCache", "implements(Cache) & type(storage.cache.**)", "CacheDebug", false) == true
expect catalog_load_aspect(cat, "debug") == true
expect try_facet(cat, "storage.cache.LruCache", "debug", "Debuggable") == true
expect facet_absence(cat, "storage.cache.LruCache", "debug", "Debuggable") == FACET_PRESENT
expect facet_witness_impl(cat, "storage.cache.LruCache", "debug", "Debuggable") == "CacheDebug"
```

</details>

#### defect-class: routing is exact-key, not always-present — an unrelated base type stays absent while the bound one resolves

- defect-class: routing is exact-key, not always-present — an unrelated base type stays absent while the bound one resolves


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: routing is exact-key, not always-present — an unrelated base type stays absent while the bound one resolves")
val cat = catalog_new()
catalog_register_aspect(cat, "debug", "packs/debug.smf")
catalog_bind_facet(cat, "debug", "Debuggable", "storage.cache.LruCache", "type(storage.cache.**)", "CacheDebug", false)
catalog_load_aspect(cat, "debug")
# positive control: bound target resolves
expect try_facet(cat, "storage.cache.LruCache", "debug", "Debuggable") == true
# unrelated base type: typed absence, not a match and not a crash
expect try_facet(cat, "net.http.Server", "debug", "Debuggable") == false
expect facet_absence(cat, "net.http.Server", "debug", "Debuggable") == FACET_NOT_BOUND
expect facet_witness_impl(cat, "net.http.Server", "debug", "Debuggable") == ""
```

</details>

### Optional acquisition — typed absence, never a crash

#### answers a dormant (registered but unloaded) aspect with aspect_dormant

- answers a dormant (registered but unloaded) aspect with aspect_dormant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers a dormant (registered but unloaded) aspect with aspect_dormant")
val cat = catalog_new()
catalog_register_aspect(cat, "profile", "packs/profile.smf")
catalog_bind_facet(cat, "profile", "Profiled", "core.Order", "implements(Entity)", "OrderProfile", false)
expect try_facet(cat, "core.Order", "profile", "Profiled") == false
expect facet_absence(cat, "core.Order", "profile", "Profiled") == FACET_ASPECT_DORMANT
expect facet_witness_impl(cat, "core.Order", "profile", "Profiled") == ""
```

</details>

#### defect-class: absence is not the hardwired answer — loading the aspect flips the SAME query to present, unloading flips it back

- defect-class: absence is not the hardwired answer — loading the aspect flips the SAME query to present, unloading flips it back


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: absence is not the hardwired answer — loading the aspect flips the SAME query to present, unloading flips it back")
val cat = catalog_new()
catalog_register_aspect(cat, "profile", "packs/profile.smf")
catalog_bind_facet(cat, "profile", "Profiled", "core.Order", "implements(Entity)", "OrderProfile", false)
expect facet_absence(cat, "core.Order", "profile", "Profiled") == FACET_ASPECT_DORMANT
catalog_load_aspect(cat, "profile")
expect try_facet(cat, "core.Order", "profile", "Profiled") == true
expect facet_witness_impl(cat, "core.Order", "profile", "Profiled") == "OrderProfile"
catalog_unload_aspect(cat, "profile")
expect try_facet(cat, "core.Order", "profile", "Profiled") == false
expect facet_absence(cat, "core.Order", "profile", "Profiled") == FACET_ASPECT_DORMANT
```

</details>

### Binding uniqueness (invariant 5.5)

#### rejects a second default provider for the same (base type, facet) pair

- rejects a second default provider for the same (base type, facet) pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a second default provider for the same (base type, facet) pair")
val cat = catalog_new()
catalog_register_aspect(cat, "debug", "packs/debug.smf")
# positive control: first default binding is accepted
expect catalog_bind_facet(cat, "debug", "Debuggable", "core.Order", "type(core.**)", "OrderDebugA", false) == true
expect catalog_bind_facet(cat, "debug", "Debuggable", "core.Order", "type(core.**)", "OrderDebugB", false) == false
expect catalog_last_error(cat).contains("duplicate default binding") == true
```

</details>

#### defect-class: uniqueness is scoped, not a blanket refusal — multi bindings and distinct targets are accepted

- defect-class: uniqueness is scoped, not a blanket refusal — multi bindings and distinct targets are accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: uniqueness is scoped, not a blanket refusal — multi bindings and distinct targets are accepted")
val cat = catalog_new()
catalog_register_aspect(cat, "debug", "packs/debug.smf")
expect catalog_bind_facet(cat, "debug", "Debuggable", "core.Order", "type(core.**)", "OrderDebug", false) == true
# different target type: fine
expect catalog_bind_facet(cat, "debug", "Debuggable", "core.Invoice", "type(core.**)", "InvoiceDebug", false) == true
# same target but declared multi: fine
expect catalog_bind_facet(cat, "debug", "Debuggable", "core.Order", "type(core.**)", "OrderDebugExtra", true) == true
```

</details>

### Core independence (invariant 5.1/5.2 slice)

#### an absent aspect leaves the core value and its behaviour untouched (sidecar witness, no base mutation)

- an absent aspect leaves the core value and its behaviour untouched (sidecar witness, no base mutation)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an absent aspect leaves the core value and its behaviour untouched (sidecar witness, no base mutation)")
val cat = catalog_new()
catalog_register_aspect(cat, "debug", "packs/debug.smf")
catalog_bind_facet(cat, "debug", "Debuggable", "core.Order", "type(core.**)", "OrderDebug", false)
# core computation independent of aspect state
val core_value = 40 + 2
expect core_value == 42
# facet absent: typed absence, core path above already ran fine
expect try_facet(cat, "core.Order", "debug", "Debuggable") == false
catalog_load_aspect(cat, "debug")
# loading grants an external witness; the core value is untouched
expect try_facet(cat, "core.Order", "debug", "Debuggable") == true
expect core_value == 42
```

</details>

#### defect-class: binding against an unregistered aspect fails closed with a typed error, not a crash

- defect-class: binding against an unregistered aspect fails closed with a typed error, not a crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: binding against an unregistered aspect fails closed with a typed error, not a crash")
val cat = catalog_new()
expect catalog_bind_facet(cat, "ghost", "Phantom", "core.Order", "type(core.**)", "PhantomImpl", false) == false
expect catalog_last_error(cat).contains("unknown aspect") == true
# positive control: a registered aspect binds fine in the same catalog
catalog_register_aspect(cat, "real", "packs/real.smf")
expect catalog_bind_facet(cat, "real", "Live", "core.Order", "type(core.**)", "LiveImpl", false) == true
```

</details>

### Catalog isolation and witness generation

#### a second catalog does not see the first catalog's aspects or bindings

- a second catalog does not see the first catalog's aspects or bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a second catalog does not see the first catalog's aspects or bindings")
val a = catalog_new()
val b = catalog_new()
catalog_register_aspect(a, "debug", "packs/debug.smf")
catalog_bind_facet(a, "debug", "Debuggable", "core.Order", "type(core.**)", "OrderDebug", false)
catalog_load_aspect(a, "debug")
# positive control: catalog a resolves
expect try_facet(a, "core.Order", "debug", "Debuggable") == true
# catalog b: same query is a typed not_bound absence
expect try_facet(b, "core.Order", "debug", "Debuggable") == false
expect facet_absence(b, "core.Order", "debug", "Debuggable") == FACET_NOT_BOUND
```

</details>

#### defect-class: generation moves on load AND unload, so a held witness is detectably stale — and re-registering in a fresh catalog works

- defect-class: generation moves on load AND unload, so a held witness is detectably stale — and re-registering in a fresh catalog works


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: generation moves on load AND unload, so a held witness is detectably stale — and re-registering in a fresh catalog works")
val cat = catalog_new()
catalog_register_aspect(cat, "debug", "packs/debug.smf")
catalog_bind_facet(cat, "debug", "Debuggable", "core.Order", "type(core.**)", "OrderDebug", false)
val g0 = facet_witness_generation(cat)
catalog_load_aspect(cat, "debug")
val g1 = facet_witness_generation(cat)
expect (g1 > g0) == true
catalog_unload_aspect(cat, "debug")
val g2 = facet_witness_generation(cat)
expect (g2 > g1) == true
# duplicate registration fails closed; a fresh catalog accepts the same aspect
expect catalog_register_aspect(cat, "debug", "packs/debug.smf") == false
expect catalog_last_error(cat).contains("already registered") == true
val fresh = catalog_new()
expect catalog_register_aspect(fresh, "debug", "packs/debug.smf") == true
expect catalog_aspect_loaded(fresh, "debug") == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2df970f2b1c7b7b1f0a44825c03462cdfcbc04fce5bd3081b9037166b7abf4e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2df970f2b1c7b7b1f0a44825c03462cdfcbc04fce5bd3081b9037166b7abf4e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2df970f2b1c7b7b1f0a44825c03462cdfcbc04fce5bd3081b9037166b7abf4e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/facet_registry_spec.spl
mirror: doc/06_spec/01_unit/lib/facet_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/facet_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/facet_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/facet_registry_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a bound facet on a loaded aspect to its implementation (present case)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/facet_registry_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defect-class: routing is exact-key, not always-present — an unrelated base type stays absent while the bound one resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/facet_registry_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers a dormant (registered but unloaded) aspect with aspect_dormant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
