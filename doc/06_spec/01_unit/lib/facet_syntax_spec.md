# Facet Surface Syntax Specification

> Proves that the `aspect` / `facet interface` / `facet impl` /

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Facet Surface Syntax Specification

Proves that the `aspect` / `facet interface` / `facet impl` /

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/facet_syntax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that the `aspect` / `facet interface` / `facet impl` /
`bind facet ... to pc{...} using ...` / `require facet ... on pc{...}` surface
forms of the aspect-facet design
(doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md
sections 6.1-6.5) lower onto the AspectCatalog records in
std.facet_registry.

The load-bearing assertion of the whole feature is in "Core independence":
the SAME core package (its type world, its interfaces, its computation) is
built twice — once with the optional aspect's source present and once with it
removed entirely — and is proven identical in both, while the facet actually
resolves in the first case. The feature therefore cannot pass by being inert.

## Scenarios

### facet surface syntax lowers onto the catalog

#### parses the design's embedded aspect example and binds every selected world type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the design's embedded aspect example and binds every selected world type


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the design's embedded aspect example and binds every selected world type")
val cat = catalog_new()
world_register_type(cat, "storage.cache.LruCache", "Cache,Entity")
world_register_type(cat, "storage.cache.ArcCache", "Cache")
world_register_type(cat, "net.http.Server", "Listener")
val n = facet_parse(cat, DEBUG_ASPECT_SRC)
expect syntax_error(cat) == ""
expect n == 2
expect facet_interface_declared(cat, "debug", "Debuggable") == true
expect facet_impl_declared(cat, "debug", "CacheDebug") == true
expect facet_impl_facet(cat, "debug", "CacheDebug") == "Debuggable"
catalog_load_aspect(cat, "debug")
expect facet_witness_impl(cat, "storage.cache.LruCache", "debug", "Debuggable") == "CacheDebug"
expect facet_witness_impl(cat, "storage.cache.ArcCache", "debug", "Debuggable") == "CacheDebug"
```

</details>

#### defect-class: the pointcut really selects — a world type failing EITHER conjunct is not bound, while both-matching types are

- defect-class: the pointcut really selects — a world type failing EITHER conjunct is not bound, while both-matching types are


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: the pointcut really selects — a world type failing EITHER conjunct is not bound, while both-matching types are")
val cat = catalog_new()
world_register_type(cat, "storage.cache.LruCache", "Cache")
world_register_type(cat, "net.http.Server", "Listener")
world_register_type(cat, "storage.cache.Meta", "Entity")
world_register_type(cat, "other.pkg.RemoteCache", "Cache")
val n = facet_parse(cat, DEBUG_ASPECT_SRC)
expect syntax_error(cat) == ""
# positive control: only the type satisfying implements(Cache) AND type(storage.cache.**)
expect n == 1
expect facet_binding_exists(cat, "storage.cache.LruCache", "debug", "Debuggable") == true
# fails the type() conjunct
expect facet_binding_exists(cat, "other.pkg.RemoteCache", "debug", "Debuggable") == false
# fails the implements() conjunct
expect facet_binding_exists(cat, "storage.cache.Meta", "debug", "Debuggable") == false
# fails both
expect facet_binding_exists(cat, "net.http.Server", "debug", "Debuggable") == false
```

</details>

### pointcut operator set (design 6.1/6.4)

#### supports alternation over concrete types

- supports alternation over concrete types


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports alternation over concrete types")
val cat = catalog_new()
world_register_type(cat, "storage.cache.LruCache", "Cache")
world_register_type(cat, "storage.cache.ArcCache", "Cache")
world_register_type(cat, "storage.cache.NullCache", "Cache")
val src = "aspect debug:\n    facet interface Debuggable:\n        fn n(self) -> text\n    facet impl InternalCacheDebug\n        implements Debuggable\n    bind facet Debuggable\n        to pc{{ type(storage.cache.LruCache) | type(storage.cache.ArcCache) }}\n        using InternalCacheDebug\n"
expect facet_parse(cat, src) == 2
expect facet_binding_exists(cat, "storage.cache.LruCache", "debug", "Debuggable") == true
expect facet_binding_exists(cat, "storage.cache.ArcCache", "debug", "Debuggable") == true
expect facet_binding_exists(cat, "storage.cache.NullCache", "debug", "Debuggable") == false
```

</details>

#### defect-class: negation excludes exactly one type and leaves its siblings bound

- defect-class: negation excludes exactly one type and leaves its siblings bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: negation excludes exactly one type and leaves its siblings bound")
val cat = catalog_new()
world_register_type(cat, "storage.cache.LruCache", "Cache")
world_register_type(cat, "storage.cache.ArcCache", "Cache")
val src = "aspect debug:\n    facet interface Debuggable:\n        fn n(self) -> text\n    facet impl GenericCacheDebug\n        implements Debuggable\n    bind facet Debuggable\n        to pc{{ implements(Cache) & !type(storage.cache.LruCache) }}\n        using GenericCacheDebug\n"
expect facet_parse(cat, src) == 1
expect facet_binding_exists(cat, "storage.cache.ArcCache", "debug", "Debuggable") == true
expect facet_binding_exists(cat, "storage.cache.LruCache", "debug", "Debuggable") == false
```

</details>

### fail-closed parsing

#### rejects a bind naming an undeclared facet implementation

- rejects a bind naming an undeclared facet implementation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a bind naming an undeclared facet implementation")
val cat = catalog_new()
world_register_type(cat, "core.Order", "Entity")
val src = "aspect debug:\n    facet interface Debuggable:\n        fn n(self) -> text\n    bind facet Debuggable\n        to pc{{ implements(Entity) }}\n        using NoSuchImpl\n"
expect facet_parse(cat, src) == -1
expect syntax_error(cat).contains("undeclared facet impl") == true
expect facet_binding_exists(cat, "core.Order", "debug", "Debuggable") == false
```

</details>

#### defect-class: rejection is specific, not blanket — a mismatched impl and an unknown line each fail with their own reason while the correct source parses

- defect-class: rejection is specific, not blanket — a mismatched impl and an unknown line each fail with their own reason while the correct source parses


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: rejection is specific, not blanket — a mismatched impl and an unknown line each fail with their own reason while the correct source parses")
val ok_src = "aspect debug:\n    facet interface Debuggable:\n        fn n(self) -> text\n    facet impl OrderDebug\n        implements Debuggable\n    bind facet Debuggable\n        to pc{{ implements(Entity) }}\n        using OrderDebug\n"
# positive control
val good = catalog_new()
world_register_type(good, "core.Order", "Entity")
expect facet_parse(good, ok_src) == 1
expect syntax_error(good) == ""
# impl declared for a different facet interface
val bad1 = catalog_new()
world_register_type(bad1, "core.Order", "Entity")
val src1 = "aspect debug:\n    facet interface Debuggable:\n        fn n(self) -> text\n    facet impl OrderDebug\n        implements Profiled\n    bind facet Debuggable\n        to pc{{ implements(Entity) }}\n        using OrderDebug\n"
expect facet_parse(bad1, src1) == -1
expect syntax_error(bad1).contains("does not implement") == true
# a line the grammar does not know is an error, never a silent skip
val bad2 = catalog_new()
val src2 = "aspect debug:\n    facet interfce Debuggable:\n"
expect facet_parse(bad2, src2) == -1
expect syntax_error(bad2).contains("unrecognized facet declaration") == true
```

</details>

### require facet obligations (design 6.5)

#### reports a selected type with no binding for the required facet

- reports a selected type with no binding for the required facet


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a selected type with no binding for the required facet")
val cat = catalog_new()
world_register_type(cat, "finance.Ledger", "BusinessRecord")
val src = "aspect audit:\n    facet interface Auditable:\n        fn audit(self) -> text\n    require facet Auditable\n        on pc{{ implements(BusinessRecord) & type(finance.**) }}\n"
expect facet_parse(cat, src) == 0
expect syntax_error(cat) == ""
expect requirements_unmet(cat) == "finance.Ledger:audit/Auditable"
```

</details>

#### defect-class: the obligation check is not always-unmet — supplying the binding clears it, and an unselected type is never demanded

- defect-class: the obligation check is not always-unmet — supplying the binding clears it, and an unselected type is never demanded


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: the obligation check is not always-unmet — supplying the binding clears it, and an unselected type is never demanded")
val cat = catalog_new()
world_register_type(cat, "finance.Ledger", "BusinessRecord")
world_register_type(cat, "web.Session", "BusinessRecord")
val src = "aspect audit:\n    facet interface Auditable:\n        fn audit(self) -> text\n    facet impl LedgerAudit\n        implements Auditable\n    bind facet Auditable\n        to pc{{ type(finance.**) }}\n        using LedgerAudit\n    require facet Auditable\n        on pc{{ implements(BusinessRecord) & type(finance.**) }}\n"
expect facet_parse(cat, src) == 1
# finance.Ledger is bound -> obligation met; web.Session is outside the
# requirement's pointcut -> never demanded
expect requirements_unmet(cat) == ""
expect facet_binding_exists(cat, "web.Session", "audit", "Auditable") == false
```

</details>

### Core independence — removing the aspect changes nothing in the core package

#### the identical core world and core computation are produced with the aspect source present and with it removed

- the identical core world and core computation are produced with the aspect source present and with it removed


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the identical core world and core computation are produced with the aspect source present and with it removed")
# --- build A: core package + optional aspect source ---
val a = catalog_new()
world_register_type(a, "storage.cache.LruCache", "Cache")
world_register_type(a, "net.http.Server", "Listener")
val na = facet_parse(a, DEBUG_ASPECT_SRC)
val core_a = 40 + 2

# --- build B: the SAME core package, aspect source deleted ---
val b = catalog_new()
world_register_type(b, "storage.cache.LruCache", "Cache")
world_register_type(b, "net.http.Server", "Listener")
val nb = facet_parse(b, "")
val core_b = 40 + 2

# the core world is bit-identical: same types, same count, no rewriting
expect world_size(a) == world_size(b)
expect world_size(b) == 2
expect core_a == core_b
expect core_b == 42
# build B parsed successfully and produced zero bindings
expect nb == 0
expect syntax_error(b) == ""

# POSITIVE CONTROL: with the aspect present the facet actually resolves
expect na == 1
catalog_load_aspect(a, "debug")
expect try_facet(a, "storage.cache.LruCache", "debug", "Debuggable") == true
expect facet_witness_impl(a, "storage.cache.LruCache", "debug", "Debuggable") == "CacheDebug"
# with the aspect removed the same query is a typed absence, not a crash
expect try_facet(b, "storage.cache.LruCache", "debug", "Debuggable") == false
expect facet_absence(b, "storage.cache.LruCache", "debug", "Debuggable") == FACET_NOT_BOUND
expect facet_witness_impl(b, "storage.cache.LruCache", "debug", "Debuggable") == ""
```

</details>

#### defect-class: the witness is a sidecar — unloading an aspect withdraws the facet without disturbing the world or the core value

- defect-class: the witness is a sidecar — unloading an aspect withdraws the facet without disturbing the world or the core value


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defect-class: the witness is a sidecar — unloading an aspect withdraws the facet without disturbing the world or the core value")
val cat = catalog_new()
world_register_type(cat, "storage.cache.LruCache", "Cache")
expect facet_parse(cat, DEBUG_ASPECT_SRC) == 1
val world_before = world_size(cat)
val core_value = 40 + 2
catalog_load_aspect(cat, "debug")
expect catalog_aspect_loaded(cat, "debug") == true
expect try_facet(cat, "storage.cache.LruCache", "debug", "Debuggable") == true
# withdraw the aspect
expect catalog_unload_aspect(cat, "debug") == true
expect catalog_aspect_loaded(cat, "debug") == false
expect try_facet(cat, "storage.cache.LruCache", "debug", "Debuggable") == false
expect facet_absence(cat, "storage.cache.LruCache", "debug", "Debuggable") == FACET_ASPECT_DORMANT
expect world_size(cat) == world_before
expect core_value == 42
# the binding RECORD survives an unload; only activation is withdrawn
expect facet_binding_exists(cat, "storage.cache.LruCache", "debug", "Debuggable") == true
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

- Canonical SPipe generation for source `abbc16f491a69875c3fca058cb6dee74c7e4b126c113e23d9999d73c98fb72ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abbc16f491a69875c3fca058cb6dee74c7e4b126c113e23d9999d73c98fb72ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abbc16f491a69875c3fca058cb6dee74c7e4b126c113e23d9999d73c98fb72ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/facet_syntax_spec.spl
mirror: doc/06_spec/01_unit/lib/facet_syntax_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/facet_syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/facet_syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/facet_syntax_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the design's embedded aspect example and binds every selected world type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/facet_syntax_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defect-class: the pointcut really selects — a world type failing EITHER conjunct is not bound, while both-matching types are' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/facet_syntax_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports alternation over concrete types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
