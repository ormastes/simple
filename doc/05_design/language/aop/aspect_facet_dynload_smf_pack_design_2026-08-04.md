# Simple Aspect Facets and Demand-Loaded SMF Packs

**Subtitle:** Typed structural AOP, relative aspect packages, variant-aware deployment, and low-overhead lazy activation  
**Status:** Proposed final research and design (design-only; no implementation in-tree yet)  
**Current implementation check:** As of 2026-08-05, the syntax and runtime for typed facets, aspect-pack catalogs, and facet dyn-loading are not yet present in `src/**` or `test/**` (no `bind facet`, `FacetRef`, `AspectCatalog`, `AspectPack`, or `SMF_FLAG_ASPECT_PACK` symbols found in code).
**See also (2026-08-21):** aspect seal, lifecycle, and critical activation policy are designed in `doc/05_design/compiler/hardening/critical_completeness_design_2026-08-21.md` §8; sequenced as Phase 6 / Wave 2E in `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`.

**Date:** 2026-08-04  
**Repository examined:** `ormastes/simple`, `main`  
**Suggested repository destination:** `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`

---

## 1. Executive Decision

Note: This design is forward-looking and should be treated as the target architecture, not existing behavior. The current codebase already contains established `on pc{...} use ...` advice weaving and `dynsmf_*` startup manifests, but it does not yet provide:

- Facet interfaces (`facet interface`) and declarations (`facet impl`)
- Declarative facet bindings (`bind facet`, `require facet`)
- Runtime optional facet acquisition (`try_facet`, `FacetRef`) or dynloaded facet activation
- Aspect pack directory/route sections and packed module chunk loading

Simple should support applying an optional facet interface to existing business objects and business interfaces through AOP, but it must not model the dynamic case as ordinary interface inheritance.

The final model has four distinct concepts:

1. **Aspect** — a named, optional concern and deployment unit, such as `debug`, `logging`, `profile.memory`, `profile.performance`, or `unit.time`.
2. **Facet interface** — the statically typed API that the aspect exposes as an optional view of a business object.
3. **Facet binding** — a structural AOP rule that binds a facet interface and implementation to business types selected by a type pointcut.
4. **Aspect pack** — one SMF container holding multiple aspect modules, indexed without decompressing module metadata and loaded a module or co-load cluster at a time.

The canonical relationship is:

```text
business object --explicit facet acquisition--> facet interface
       ^                                        |
       |                                        v
  target pointcut <------- facet binding ----- facet implementation
                                                  |
                                                  +-- optional AOP advice
```

The principal design decisions are:

- `bind facet ... to pc{...} using ...` applies a facet to concrete business object types or to every type implementing a business interface.
- Dynamic facets use an external witness/sidecar representation. They do not change the base object's layout or nominal type hierarchy.
- Static-only facets may optionally use nominal interface introduction, equivalent in spirit to AspectJ `declare parents`, but such a facet cannot remain independently unloadable.
- Aspect source can be embedded beside a business package or placed in explicit relative aspect roots. File location never becomes the public aspect identity.
- At deployment, multiple modules may be grouped into one `kind=aspect_pack` SMF under the application's `aspect/` path.
- An application SMF contains a small uncompressed **Aspect Catalog**. It routes a facet or dynamic join-point slot directly to its pack and module without scanning directories or opening every pack.
- Every module payload in an aspect pack is independently compressed. Loading one aspect does not decompress the rest of the pack.
- Simple's existing `variants/` selection supplies platform, hardware, library, and renderer choices to aspect packages. Aspect selection is a separate axis, but both are compiled into one deterministic deployment catalog.
- Core compilation cache keys do not include the enabled aspect set unless static weaving or dynamic patchpoint emission actually changes core code.
- Rarely used aspects should default to `lazy_facet` or `manual` activation. Transparent first-join-point activation is optional because it necessarily leaves a patchpoint, trampoline, or guard in the business path.

---

## 2. Why This Is Not Just Existing AOP

Simple's current AOP model is primarily behavioral:

```simple
on pc{ execution(* target_func(..)) } use advice_func before priority 10
```

It selects execution join points and weaves `before`, `after_success`, `after_error`, or `around` advice. The current authoritative matrix supports `execution`, `within`, and `attr`; type-introduction selectors and link-time weaving are not yet part of the implemented surface.

The proposed facility adds **structural optionality**:

```simple
bind facet Debuggable
    to pc{ implements(Cache) & type(storage.cache.**) }
    using CacheDebug
```

This says that matching objects have an optional `Debuggable` view when the owning aspect is present. It does not say that `Cache` permanently extends `Debuggable`.

The distinction is necessary because ordinary interface extension creates a mandatory dependency:

```simple
# Mandatory business contract: not suitable for an optional dynloaded aspect.
interface Cache extends Debuggable:
    ...
```

Once this is accepted, every `Cache` consumer may invoke `Debuggable`, the base ABI includes the conformance, and removing the debug aspect can make otherwise valid business code fail. Dynamic facet binding instead preserves this invariant:

> Removing an optional aspect cannot invalidate the core business package's type checking, layout, exported ABI, or normal execution path.

---

## 3. Terminology

### 3.1 Aspect

A hierarchical named concern:

```text
debug
logging
profile
profile.memory
profile.performance
profile.gpu
unit
unit.time
unit.distance
database.explain
security.audit
```

An aspect owns facet interfaces, facet implementations, helper functions, optional state, advice, tests, and deployment metadata.

### 3.2 Facet interface

A normal statically typed interface whose availability is optional for a base object:

```simple
facet interface Debuggable:
    fn debug_name(self) -> text
    fn snapshot(self) -> DebugSnapshot
```

A facet interface may extend other facet interfaces. It may not silently become part of an optional business contract.

### 3.3 Facet implementation

The implementation that adapts a base object to a facet interface:

```simple
facet impl CacheDebug<T: Cache>
    for T
    implements Debuggable
    public readonly:

    fn debug_name(self) -> text:
        self.base.name()

    fn snapshot(self) -> DebugSnapshot:
        DebugSnapshot(entries: self.base.entry_count())
```

Internally this is a **role** or **witness factory**. The term `role` is useful in the compiler/runtime design, but does not need to become an additional public keyword.

### 3.4 Facet binding

A pointcut-driven mapping from business types to a facet implementation:

```simple
bind facet Debuggable
    to pc{ implements(Cache) & type(storage.cache.**) }
    using CacheDebug
```

### 3.5 Aspect module

A normal Simple module owned by exactly one aspect. Ownership can be lexical, manifest-derived, or inferred for private helpers.

### 3.6 Aspect package

A source package containing one aspect's modules, variants, contract, tests, and pack policy.

### 3.7 Aspect pack

A deployment SMF containing multiple independently indexed aspect modules or co-load clusters.

### 3.8 Aspect Catalog

A small uncompressed section in the application SMF. It contains only the data needed to route an aspect request to a pack; it does not contain full aspect module metadata or code.

---

## 4. Research Findings and Their Design Consequences

### 4.1 AspectJ: static structural introduction is useful but not dynamically optional

AspectJ inter-type declarations can add fields and methods to existing types, and `declare parents` can make selected types implement an interface. This provides a strong precedent for pointcut-selected interface application.

However, AspectJ's structural introduction is static and changes the target type system. The AspectJ guide also notes that the weaver must control affected target code and that mismatched woven interfaces and implementors can fail at runtime.

**Adopt:**

- AOP-selected interface application.
- Static nominal mode for closed-world builds.
- Compile-time conflict and completeness diagnostics.

**Do not adopt as the dynamic default:**

- Mutating the base type hierarchy for a facet that may be absent, attached later, or unloaded.

### 4.2 Object Teams and OT/Equinox: the closest semantic match

Object Teams introduces roles that specialize existing base objects and teams that group interacting roles. Callout forwards role methods to a base; callin intercepts base behavior. OT/Equinox adds architecture-level aspect bindings between an aspect bundle and a base bundle.

This closely matches the desired Simple model:

```text
Object Teams role       -> Simple facet implementation
Object Teams base       -> Simple business object
team                     -> Simple aspect
aspect bundle            -> Simple aspect package/pack
aspect binding           -> Simple bind facet declaration
callout/callin           -> facet delegation/AOP advice
```

**Adopt:**

- Explicit base-to-role binding.
- Aspect packages separate from base packages.
- A deployment-level binding between an aspect package and base modules.
- Optional private access only through an explicit capability.

**Simplify:**

- Do not eagerly create one role object for every base object. Stateless facets use a type-level witness. Stateful facets allocate sidecar state only on first use.

### 4.3 Classboxes and Aspectboxes: external extensions need bounded visibility

Classboxes allow methods defined in one module to extend classes defined elsewhere while keeping those extensions visible only in a controlled scope. Aspectboxes apply the same principle to aspects: the base system behaves as if no aspect existed outside the aspectbox scope.

**Adopt:**

- Aspect roots are explicit scopes, not globally searched directories.
- Relative roots are resolved from the declaring manifest, canonicalized, ranked, and conflict-checked.
- Aspect bindings affect only the application/deployment scope that imports the aspect package.
- Two applications may deploy different facet bindings for the same business library without modifying that library.

### 4.4 Aspectual Feature Modules: features and aspects are complementary

Aspectual Feature Modules research found that feature modules are effective for large-scale optional composition while aspects handle crosscutting behavior that feature modules cannot localize well.

**Adopt:**

- Use the aspect package/pack as the optional feature module.
- Use AOP inside that package only for actual crosscutting interception.
- Do not force all optional packaging through advice or all advice through package variants.

In Simple terms:

```text
aspect package and pack = optional feature/module boundary
facet binding           = typed structural extension
AOP advice              = behavioral crosscutting inside that boundary
variants                 = implementation selection within the boundary
```

### 4.5 CaesarJ: aspects should scale as components, not isolated snippets

CaesarJ unifies aspects, classes, and packages and was designed for non-invasive component refinement and large-scale aspect components.

**Adopt:**

- An aspect may contain many modules and internal layers.
- Aspect identity and API are independent of one source file.
- Hierarchical aspects may aggregate child aspects.

### 4.6 Nu and dynamic AOP virtual-machine research: bind/remove should be explicit runtime primitives

Nu preserves aspect modularity in intermediate code through `bind` and `remove` primitives. Dynamic AOP VM research shows that runtime deployment can remain fast when the execution environment has explicit support rather than repeatedly rewriting arbitrary high-level structures.

**Adopt:**

- MIR/runtime primitives for binding and unbinding facet witnesses and advice plans.
- Atomic generation publication.
- Precomputed binding metadata rather than runtime source-level pointcut interpretation.
- A clear distinction between loading code and activating bindings.

### 4.7 OSGi lazy activation: catalog first, activation later

OSGi supports bundles that are resolved and started but not activated until their first class load. Its specification explicitly motivates lazy activation as a way to reduce startup time and memory footprint.

**Adopt:**

- A lifecycle state machine.
- A catalog that can describe a pack without loading its code.
- Explicit startup and lazy policies.
- Reverse-order or dependency-aware activation when one lazy load triggers another.

**Avoid as the default:**

- Arbitrary business class loads silently causing expensive I/O. Simple should prefer first facet acquisition or explicit loading for rare aspects.

### 4.8 Linux static keys: transparent dormant hooks are near-zero, not literally zero

Linux static keys use patchable NOP/jump sites to include seldom-used instrumentation in hot paths. Disabled selection can avoid a global-variable load and branch; enabling or disabling is comparatively expensive because code is patched.

**Design consequence:**

- A transparent first-join-point aspect requires a dormant patchpoint, trampoline, or guard.
- Simple may provide a patchable mode with very small disabled-path cost.
- It must not claim byte-for-byte zero overhead for that mode.
- Exact zero business-path overhead is available only when the aspect is statically omitted or is reached through explicit facet acquisition outside the business function.

### 4.9 Indexed lazy content systems and Zstandard: independently addressable chunks

Lazy container image systems demonstrate the value of a small index that allows content to be fetched on demand. Zstandard supports independent frames, and its dictionary mode can improve compression for families of small related payloads.

**Adopt:**

- An uncompressed directory.
- Independent module or co-load-cluster frames.
- Optional pack-level dictionary for small related modules.
- Per-chunk hashes and bounds.

**Reject:**

- One compressed stream for the whole aspect pack. It would require decompressing unrelated modules.

### 4.10 BOLT and code-layout research: pack grouping should eventually be profile guided

BOLT demonstrates that profile-guided code layout remains valuable even after conventional optimization. The direct lesson for aspect packs is not to guess permanent grouping thresholds.

**Adopt later:**

- Cluster modules using observed co-activation and first-use profiles.
- Place startup aspects and hot code separately from rarely touched debug metadata.
- Keep explicit pack assignments as a deterministic override.

---

## 5. Required Semantic Invariants

Let `C` be the core/business declaration set and `A_i` the declaration set owned by optional aspect `i`.

### 5.1 Core independence

For every optional aspect:

```text
no dependency edge C -> A_i
```

Allowed:

```text
A_i -> C
A_i -> A_j   only when explicitly declared
C   -> C
```

A business function calling an aspect-owned function is an error even when a default profile always enables that aspect.

### 5.2 Base layout stability

Dynamic facet binding must not add fields, vtable slots, or nominal parents to the base object.

### 5.3 Explicit optional API access

Optional facet methods are called only through a `FacetRef<T>` or equivalent explicit acquisition operation.

### 5.4 Binding completeness

If an enabled aspect declares a required binding, every matching concrete type must have exactly one valid implementation unless the binding is explicitly declared `multi`.

### 5.5 Binding uniqueness

Two default providers for the same `(base type, facet interface)` pair are an error unless configuration selects one or the facet is declared multi-provider.

### 5.6 ABI compatibility

A facet implementation may bind only when its required public ABI, layout ABI, and runtime ABI fingerprints match the loaded base module.

### 5.7 Atomic activation

No thread may observe a partially loaded aspect. All required chunks, relocations, witnesses, and advice plans are staged before one generation is published.

### 5.8 Deterministic configuration

The same source, target, variant selection, aspect profile, lockfile, and toolchain must produce the same logical bindings and pack catalog.

### 5.9 No hidden runtime search

The runtime never scans aspect directories, parses source manifests, or searches arbitrary relative paths. All source resolution happens at build time; deployment uses catalogued relative pack paths and hashes.

### 5.10 Exact performance claims

Each activation mode has a separately stated cost contract. “Zero overhead when disabled” is not used as a blanket claim for dynamic patchable advice.

---

## 6. Language Design

## 6.1 Canonical grammar

```ebnf
AspectDecl        ::= "aspect" QualifiedName ":" AspectMember*
FacetInterface    ::= "facet" "interface" Identifier TypeParams? Extends? ":" InterfaceMember*
FacetImpl         ::= "facet" "impl" Identifier TypeParams?
                      "for" Type
                      "implements" TypeList
                      FacetAccess*
                      ":" FacetImplMember*
FacetBind         ::= "bind" "facet" Type
                      "to" PointcutExpr
                      "using" Type
                      BindOption*
FacetRequire      ::= "require" "facet" Type "on" PointcutExpr
```

New type pointcut selectors:

```ebnf
TypeSelector      ::= "type" "(" TypePattern ")"
                    | "implements" "(" Type ")"
                    | "subtype" "(" Type ")"
```

The existing `pc{...}` operators, precedence, `attr`, and module patterns are reused. This avoids a second pattern language.

## 6.2 Embedded aspect example

```simple
aspect debug:
    facet interface Debuggable:
        fn debug_name(self) -> text
        fn snapshot(self) -> DebugSnapshot

    facet impl CacheDebug<T: Cache>
        for T
        implements Debuggable
        public readonly:

        fn debug_name(self) -> text:
            self.base.name()

        fn snapshot(self) -> DebugSnapshot:
            DebugSnapshot(entries: self.base.entry_count())

    bind facet Debuggable
        to pc{ implements(Cache) & type(storage.cache.**) }
        using CacheDebug
```

## 6.3 Applying a facet through a business interface

The following binding applies to every current and future concrete type that implements `Cache` within the selected type scope:

```simple
bind facet Debuggable
    to pc{ implements(Cache) & type(storage.cache.**) }
    using CacheDebug
```

This is the answer to the central semantic question: **yes, an aspect can apply a facet interface to a business interface through AOP**.

The binding is evaluated in two situations:

1. At compile/link time for all known types.
2. At module registration time for types loaded later.

No existing objects are scanned. The binding is installed at the type-descriptor level.

## 6.4 Applying to selected concrete objects

```simple
bind facet Debuggable
    to pc{ type(storage.cache.LruCache) | type(storage.cache.ArcCache) }
    using InternalCacheDebug
```

## 6.5 Required implementation

An aspect may force all matching types to provide a facet:

```simple
aspect audit:
    require facet Auditable
        on pc{ implements(BusinessRecord) & type(finance.**) }
```

Because the requirement belongs to `audit`, it is active only in configurations enabling that aspect unless the deployment marks the aspect mandatory.

## 6.6 Generic and concrete implementations

A generic implementation may use only the public business interface:

```simple
facet impl GenericCacheDebug<T: Cache>
    for T
    implements Debuggable
    public readonly:
    ...
```

A concrete implementation may inspect private representation only with explicit authority:

```simple
facet impl LruCacheDebug
    for LruCache
    implements Debuggable
    inspect readonly:

    fn snapshot(self) -> DebugSnapshot:
        DebugSnapshot(
            buckets: self.base._buckets.len(),
            free_nodes: self.base._free_list.len()
        )
```

The second form is tied to the exact private-layout hash of `LruCache`.

## 6.7 Facet acquisition

```simple
fn print_cache_debug(cache: Cache):
    when val debug = cache.facet<Debuggable>():
        print debug.snapshot()
```

Required APIs:

```simple
obj.try_facet<T>() -> Option<FacetRef<T>>
# Never performs I/O. Returns only an already-bound facet.

obj.facet<T>() -> Result<Option<FacetRef<T>>, FacetLoadError>
# May load an aspect when policy is lazy_facet.

obj.require_facet<T>() -> Result<FacetRef<T>, FacetLoadError>
# May load; absence is an error.

aspect.load(name: AspectId) -> Result<AspectHandle, AspectLoadError>
aspect.unload(handle: AspectHandle) -> Result<(), AspectUnloadError>
```

`FacetRef<T>` contains the base object reference, witness/vtable, aspect generation token, and any lazy sidecar-state handle. Holding it pins the loaded generation.

## 6.8 Nominal static mode

For closed-world builds only:

```simple
bind facet SerializableView
    to pc{ implements(Entity) }
    using EntitySerializable
    nominal static
```

In this mode the compiler may materialize ordinary interface conformance. It is analogous to static inter-type introduction.

Restrictions:

- The aspect must be selected at build time.
- The base and all implementors must be controlled by the same build.
- The aspect cannot be hot-unloaded.
- The core ABI and type hierarchy vary with the aspect configuration.

The default is `attached`, not `nominal`.

## 6.9 Facet interface inheritance and mixins

Facet interfaces may compose other facet contracts:

```simple
facet interface Profiled extends SampleSource, MetricSource:
    fn profile_summary(self) -> ProfileSummary
```

Facet implementations may use normal Simple mixins internally. A dynamic facet mixin composes into the sidecar implementation, not into the base object's fields.

## 6.10 Business-interface extension rule

```simple
interface Cache extends Debuggable:
```

This is legal only when `Debuggable` is a mandatory, non-optional interface or the binding is static nominal in every supported product. If `Debuggable` belongs to an optional or dynloaded aspect, the compiler emits an error and recommends a facet binding.

## 6.11 Aspect-owned AOP advice

```simple
aspect debug:
    fn verify_after_put(ctx: AdviceContext):
        val cache = ctx.target.require_facet<Debuggable>()?
        check cache.snapshot().is_consistent()

    on pc{ execution(* storage.cache.*.put(..)) }
        use verify_after_put after_success priority 10
```

Facet binding and execution advice are independent:

- A facet can be demand-loaded without instrumenting normal business methods.
- Runtime-attached execution advice needs static/startup weaving or declared dynamic patchpoints.

## 6.12 Dynamic advice eligibility

A function that may receive advice after deployment must be marked by configuration or declaration:

```simple
@dynamic_joinpoint(debug, profile.performance)
fn put(mut self, key: Key, value: Value):
    ...
```

A package policy may select sites through pointcuts instead of annotating each function, but the build still materializes a finite join-point slot table.

Loading dynamic advice for an unprepared function is an error, not a silent no-op.

---

## 7. Aspect Ownership and Automatic Function Placement

A declaration belongs to an aspect when any of these rules applies, in order:

1. It is inside an embedded `aspect name:` block.
2. Its module was resolved from an aspect package whose manifest declares that aspect ID.
3. It has an explicit `@aspect(name)` annotation.
4. It is private and all reachable callers belong to one aspect; ownership is inferred.

For each private declaration, the compiler computes a usage set:

```text
UsedBy = {core, debug, logging, profile.memory, ...}
```

Placement rules:

| Usage set | Placement |
|---|---|
| `{debug}` | `debug` aspect module/slice |
| `{core}` | core |
| `{core, debug}` | core; explicit aspect ownership is an error |
| `{debug, logging}` | explicit shared-aspect utility or error |
| `{}` | dead declaration |

A core function depending on an explicit facet implementation or aspect helper is always an error:

```simple
@aspect(debug)
fn verify_cache(cache: Cache) -> bool:
    ...

fn put(mut cache: Cache, key: Key, value: Value):
    verify_cache(cache)  # E-AF001
```

Correct alternatives:

- Move a true business invariant into core.
- Invoke the diagnostic function from aspect advice.
- Invoke it from an aspect-aware diagnostic client.

---

## 8. Aspect Source Placement

## 8.1 Supported placement forms

### Embedded beside a business package

```text
src/storage/cache/
  cache.spl
  aspects/
    debug/
      __init__.spl
      src/
        cache_debug.spl
```

### Application-level aspects

```text
aspects/
  __init__.spl
  debug/
    __init__.spl
    src/
      cache_debug.spl
  logging/
    __init__.spl
    src/
      request_logging.spl
```

### Explicit relative shared root

```text
workspace/
  app/
    aspects/__init__.spl
  shared-aspects/
    security-audit/
      __init__.spl
      src/
```

## 8.2 Root registry

`aspects/__init__.spl` is a resolver-owned SDN manifest, analogous to the special `variants/__init__.spl` rule. It is not parsed as general Simple source.

```sdn
aspects:
  version: 1
  order: [package_local, app, company]
  roots:
    package_local: { path: ../src/storage/cache/aspects }
    app:           { path: . }
    company:       { path: ../../shared-aspects, external: true }
  policy:
    same_rank_conflict: error
    direct_core_import: error
    path_escape: error
    symlink_escape: error
```

Every relative path is resolved relative to this manifest, never to the process working directory.

## 8.3 Aspect package descriptor

```sdn
aspect:
  id: debug
  version: 1
  source: src
  pack: diagnostics
  activation_default: lazy_facet
  access_default: public_readonly
  dependencies: []
  variants: inherit
```

The manifest-derived aspect context means source files do not need a repeated outer `aspect debug:` block. Embedded and external syntax lower to the same IR.

## 8.4 Stable identity

Logical identity is derived from the manifest:

```text
aspect id + module path + declared version
```

It is not derived from the absolute file path. Moving an aspect package does not change its public IDs or ABI.

## 8.5 Resolver order

For an aspect module, resolution is:

```text
1. current aspect package relative module
2. active variant roots inside that aspect package
3. aspect package default variant
4. explicitly declared aspect dependencies
5. normal public core/library dependencies
```

Business source cannot directly import hidden aspect-root paths. It imports a published facet contract or uses aspect-aware tooling modules.

## 8.6 Relative path security and reproducibility

At build time:

- Canonicalize paths.
- Record root ID, normalized logical path, content hash, and lockfile identity.
- Reject undeclared workspace escape.
- External roots require an explicit `external: true` policy.
- Same-rank duplicate aspect IDs are errors.

At runtime:

- Relative source roots no longer exist as a resolution mechanism.
- The application catalog names exact pack files and hashes relative to the deployed application image.

---

## 9. Variants and Aspect Configuration

## 9.1 Reuse the existing variant overlay

Simple's existing `variants/` design already supplies stable imports, profile selection, deterministic precedence, defaults, and a selection fingerprint. Aspect packages should reuse that mechanism rather than introduce `@various` grammar.

An aspect package is a package-family root:

```text
aspects/debug/
  __init__.spl
  src/
    sampler.spl
  variants/
    platform/
      linux/sampler.spl
      windows/sampler.spl
      default/sampler.spl
    hw/
      x86_64/counter.spl
      arm64/counter.spl
      default/counter.spl
```

The application supplies the active selections from `config/var.sdn`. The aspect resolver applies the same selected-before-default ordering inside the aspect package.

## 9.2 Separate selection axes

```text
variant profile = which implementation of a stable module is used
aspect profile  = which optional concerns are deployed and how they activate
```

They are related but not interchangeable.

## 9.3 Aspect configuration

```sdn
aspect:
  profile: prod
  profiles:
    prod:
      enabled:
        logging: { activation: startup, pack: observability }
        metrics: { activation: lazy_facet, pack: observability }
      disabled: [debug, profile.memory, profile.performance]

    diagnose:
      inherit: prod
      enabled:
        debug:              { activation: lazy_facet, pack: diagnostics }
        profile.memory:     { activation: manual, pack: diagnostics }
        profile.performance:{ activation: lazy_patchable, pack: diagnostics }
```

Hierarchical configuration is expanded at build time:

```sdn
enable: [profile.*]
disable: [profile.gpu]
```

The runtime receives resolved IDs/bitsets, not wildcard strings.

## 9.4 Activation modes

| Mode | When code is loaded/bound | Disabled business-path cost | First-use cost | Intended use |
|---|---|---:|---:|---|
| `off` | never included | zero | unavailable | production shrink |
| `static` | compile/link time | zero when omitted | none | fixed certified features |
| `startup` | before application publication | no first-use guard after patching | startup load | logging/security required at start |
| `lazy_facet` | first `facet<T>()` | zero in unrelated business methods | pack/module load | debug views, explain APIs |
| `manual` | explicit `aspect.load` | zero | explicit load | memory/GPU profilers |
| `lazy_patchable` | first prepared join point | dormant patchpoint | load + code patch | transparent rare tracing |
| `hot` | attach/detach at runtime | patchpoint/dispatch cost | deployment transaction | development, controlled operations |

`lazy_facet` is the default for rarely used typed facets.

## 9.5 Cache-key separation

Use distinct fingerprints:

```text
CoreVariantFingerprint
    = hash(target, active variants used by core, core dependency ABI)

AspectModuleFingerprint
    = hash(aspect source, aspect dependencies, target,
           active variants used by that aspect, facet contract ABI)

WeaveFingerprint
    = hash(core MIR, static aspects, emitted dynamic join-point schema)

PackFingerprint
    = hash(ordered module chunk hashes, compression and pack policy)

CatalogFingerprint
    = hash(core ABI, resolved aspect profile, pack references and bindings)
```

Consequences:

- Changing a lazy aspect profile does not recompile the core.
- Changing pack grouping repacks modules but does not recompile them.
- Changing an aspect implementation recompiles only that aspect and dependents.
- Changing static advice or the patchpoint schema changes the weave fingerprint and appropriately invalidates core output.
- Variant profile hashes remain in resolver and module compilation keys, preventing cross-profile cache poisoning.

## 9.6 Multi-profile deployments

Default deployment emits only the selected aspect profile.

A fat installation may carry several catalogs and shared content-addressed chunks, but process startup selects one pre-resolved catalog by profile ID. It must not evaluate every profile or scan all packs.

---

## 10. Application Deployment Layout

```text
deploy/
  app.smf
  aspect/
    observability.smf
    diagnostics.smf
    units.smf
```

Example grouping:

```text
observability.smf
  logging.*
  metrics.*
  trace.common.*

diagnostics.smf
  debug.*
  profile.memory.*
  profile.performance.*
```

Grouping many modules into one pack reduces:

- file-open count,
- filesystem metadata lookup,
- signatures and manifests to verify,
- duplicate compression dictionaries,
- small-file deployment overhead.

It must not imply loading all grouped modules.

---

## 11. Two-Level Index Design

## 11.1 Level 1: application Aspect Catalog

The application SMF contains an uncompressed `AspectCatalog` section.

```text
AspectCatalogHeader
PackRef[]
FacetRoute[]
JoinpointRoute[]
StartupAspect[]
ProfileRecord[]          # optional multi-profile image
CatalogStringTable
```

### PackRef

```text
pack_id
relative_path_ref
pack_kind
content_hash
index_hash
signature_policy
required_runtime_abi
```

### FacetRoute

```text
facet_interface_id
facet_contract_abi_hash
pack_id
aspect_id
primary_module_id
activation_mode
```

### JoinpointRoute

```text
joinpoint_slot_id
pack_id
aspect_id
binding_plan_id
activation_mode
```

The catalog is sufficient to answer:

- Is this aspect excluded, present, startup, lazy, or manual?
- Which pack contains `Debuggable`?
- Which pack owns dynamic join-point slot 817?
- What hash and runtime ABI should that pack have?

It is not sufficient to execute the aspect; detailed symbols and relocations remain in the pack.

## 11.2 Level 2: aspect-pack directory

Each aspect-pack SMF contains a small uncompressed `AspectPackDirectory` section.

```text
AspectPackDirectoryHeader
AspectEntry[]
ModuleEntry[]
BindingSummaryEntry[]
DependencyEntry[]
ChunkEntry[]
MinimalStringTable
SignatureTable
```

### ModuleEntry

```text
module_id
aspect_id
module_abi_hash
required_core_public_abi_hash
required_core_layout_hash       # zero when public-only
variant_fingerprint
chunk_range
dependency_range
binding_summary_range
```

### ChunkEntry

```text
chunk_id
kind
flags
compression
file_offset
compressed_size
uncompressed_size
alignment
content_hash
optional_dictionary_id
```

The pack directory is read without decompressing any module.

## 11.3 Full metadata remains inside module chunks

Compressed module chunks contain:

- complete symbol tables,
- code and data,
- relocations,
- full pointcut/binding bytecode,
- `note.sdn`,
- generic/JIT metadata,
- reflection schema,
- debug and source maps.

Only routing and compatibility metadata is duplicated in the uncompressed indexes.

---

## 12. Backward-Compatible Aspect-Pack SMF Implementation

The lowest-risk first implementation embeds complete ordinary SMF modules as pack chunks:

```text
AspectPack SMF
  PackDirectory        uncompressed
  module A .smf blob   independently compressed
  module B .smf blob   independently compressed
  module C .smf blob   independently compressed
```

On load:

1. The pack provider reads the directory.
2. It locates one module chunk.
3. It decompresses that complete SMF image.
4. It passes the bytes to the existing in-memory SMF reader.
5. The existing symbol, relocation, JIT, and metadata paths continue to operate.

This directly fits the current loader architecture, which already has an object-provider boundary and an in-memory SMF reader used for module bytes and relocation handling.

Later versions may deduplicate strings, contracts, and relocations across modules. That optimization is not required for the first functional pack format.

## 12.1 SMF header compatibility

Use the existing trailer/header and section table. Add:

```text
SMF_FLAG_ASPECT_PACK
SectionType::AspectPackDirectory
SectionType::AspectPackSignature
SectionType::AspectPackDictionary   # optional
```

An old loader must reject `SMF_FLAG_ASPECT_PACK` as an ordinary executable module. A new `AspectPackProvider` handles it.

## 12.2 Compression policy

- The application catalog and pack directory are always uncompressed.
- Every module is an independent frame by default.
- Very small modules may be grouped into one co-load cluster only when their activation and dependency profile justifies it.
- Hot/startup code may remain page-aligned and uncompressed for direct mapping.
- Debug/source metadata may be split into a separate cold chunk.
- A pack-level Zstandard dictionary is optional for related small modules.
- Every chunk has an explicit maximum uncompressed size and hash.

## 12.3 Why a whole-pack stream is forbidden

A whole-pack compression stream would make the first use of one debug function depend on decompressing unrelated logging, metrics, or profiling modules. It also prevents independent verification, caching, and eviction. Therefore:

```text
one pack file != one compression stream
```

---

## 13. Pack Grouping Policy

## 13.1 Hard grouping constraints

Modules may share a pack only when they have compatible:

- target triple and ABI,
- trust/signature domain,
- mutation/access authority,
- deployment/update policy,
- encryption policy,
- runtime compatibility generation.

## 13.2 Soft grouping signals

Within hard constraints, group by:

1. Explicit `pack:` name.
2. Aspect hierarchy.
3. Dependency closure.
4. Co-enabled configuration profiles.
5. Similar activation time.
6. Measured co-use and first-use timing.

## 13.3 Independent loading remains mandatory

Even when `debug`, `profile.memory`, and `profile.performance` share `diagnostics.smf`, the directory must allow loading only `debug.cache` and its dependency closure.

## 13.4 Repacking does not recompile

The compiler cache stores ordinary module SMF images or equivalent module chunks. The packer consumes those artifacts. Changing pack placement is a packaging operation.

---

## 14. Loader and Runtime Architecture

```text
Application SMF
   |
   +-- AspectCatalogReader
           |
           +-- AspectActivationManager
                   |
                   +-- AspectPackIndexCache
                   +-- AspectPackProvider
                   +-- FacetBindingRegistry
                   +-- AdviceBindingRegistry
                   +-- ModuleLoader / existing SMF reader
                   +-- ResourceLifecycleManager
```

## 14.1 New components

### AspectCatalogReader

Reads the application catalog once and exposes ID-based routes.

### AspectPackIndexCache

Caches only pack trailer/directory mappings. It does not imply loading payload chunks.

### AspectPackProvider

Implements module lookup by `(pack_id, module_id)`, decompresses selected chunks, and returns ordinary SMF bytes to the existing loader.

### FacetBindingRegistry

Maps:

```text
(concrete_type_id, facet_interface_id, aspect_generation)
    -> witness factory/vtable
```

It also stores open-world rules keyed by implemented business interface IDs.

### AdviceBindingRegistry

Maps prepared join-point slots to static, startup, or dynamic advice chains.

### AspectActivationManager

Runs the load/validate/bind/publish state machine and coordinates concurrent first use.

## 14.2 Runtime state machine

```text
Excluded
   |
Catalogued
   |
IndexMapped
   |
Resolving
   |
ChunksLoaded
   |
Relocated
   |
Bound
   |
Active
   |
Quiescing
   |
Unloaded
```

Failures transition to `Failed` with a stable diagnostic. Retry policy is explicit.

## 14.3 First `facet<T>()` operation

```text
1. get concrete type ID from base object
2. check binding inline/type cache
3. check already-loaded registry
4. consult application FacetRoute
5. if policy permits lazy loading:
      open exact pack path
      map trailer and directory only
      verify index hash/signature
      resolve module dependency closure
      decompress selected module chunks
      load and relocate through existing ModuleLoader
      validate base/facet ABI hashes
      stage witness factories
      publish new binding generation atomically
6. instantiate or retrieve lazy sidecar state if required
7. return FacetRef<T>
```

## 14.4 Open-world business-interface bindings

For:

```simple
pc{ implements(Cache) }
```

The binding plan contains the business interface ID. Every loaded module publishes type descriptors and implemented-interface IDs.

Two load orders are supported:

- **Base first:** loading the aspect indexes existing candidate type descriptors and registers witnesses.
- **Aspect first:** each later base type registration checks rules indexed by its implemented interface IDs.

No heap-object enumeration is required.

## 14.5 Stateless and stateful facets

### Stateless

Only a witness/vtable is needed. All objects of a type share it.

### Per-type state

Allocated when the binding becomes active.

### Per-object state

Allocated lazily on first facet use and stored in an aspect-owned weak/identity side table:

```simple
facet impl CacheProfiler<T: Cache>
    for T
    implements Profiled
    public readonly:

    state per_object lazy:
        samples: Ring<Sample>
```

Dynamic facets never insert this state into the base layout.

## 14.6 Concurrency

First use uses a single activation future/state per aspect generation. Concurrent callers wait for the same transaction rather than loading duplicate chunks.

Recursive activation tracks a dependency stack and rejects cycles before publication.

## 14.7 Unload

`FacetRef` and advice invocations pin an aspect generation. Unload:

1. Marks generation quiescing.
2. Prevents new acquisitions.
3. Removes or patches binding entries.
4. Waits for active references/calls using epochs or reference counts.
5. Releases sidecar state and executable mappings.

Hot unload is not required for the initial release.

---

## 15. Mapping and I/O Policy

The current SMF mmap cache maps the full file and uses sequential access advice. That is appropriate for ordinary modules expected to be consumed as a unit, but not for large cold aspect packs.

Aspect packs require a distinct path:

- Read the fixed trailer.
- Map or `pread` only the uncompressed pack directory.
- Do not issue whole-file sequential readahead.
- Map or read only selected compressed chunk ranges.
- Issue `WILLNEED` only for explicit startup/preload closures.
- Cache decompressed module bytes by content hash.
- Evict cold debug chunks independently from the pack index.

Mapping a whole file may reserve virtual address space without faulting all pages, but the loader should still avoid policies that encourage unnecessary payload read-ahead.

---

## 16. Facet Contracts and SHB/Metadata

A caller may need the `Debuggable` type at compile time without loading its implementation at runtime.

Therefore facet contracts are split from executable aspect payloads:

```text
facet contract = interface ID, method signatures, effects, ABI hash
facet implementation = code, state, private metadata, advice
```

The compiler emits facet contracts into `.shb` interface metadata. When an application references a facet contract, the packer also copies the minimal normalized contract descriptor into the application Aspect Catalog.

This does not load aspect code.

Recommended SHB additions:

```text
FACET_INTERFACES
FACET_REQUIREMENTS
ASPECT_IMPORTS
```

Contract identity should use stable serial IDs plus a structural ABI hash, consistent with the existing SHB design direction.

---

## 17. ABI and Compatibility Model

Every binding records:

```text
facet_interface_id
facet_contract_abi_hash
base_business_interface_id
required_core_public_abi_hash
required_core_layout_hash       # only inspect/private bindings
runtime_witness_abi_version
target_triple
variant_fingerprint
```

Compatibility levels:

| Facet access | Required compatibility |
|---|---|
| public interface only | business public ABI |
| private read/inspect | exact private layout ABI |
| mutate domain state | exact layout + mutation contract |
| structural/unsafe | exact compiler/runtime generation |

A public-interface facet can survive many implementation changes. A private memory profiler is intentionally invalidated by layout changes.

---

## 18. Access and Mutation Policy

Facet-local mutable state is always separate from domain mutation.

Access levels:

| Level | Domain authority | Default compatibility |
|---|---|---|
| `public readonly` | public methods/fields only | public ABI |
| `inspect readonly` | private representation read | exact layout hash |
| `mutate` | write domain state | explicit grant + exact ABI |
| `structural` | alter ownership, dispatch, or layout-sensitive state | unsafe/privileged |

Default:

```text
public readonly
```

A business package may tighten policy:

```simple
@facet_policy(public_readonly)
class FlightController:
    ...
```

or grant a named aspect:

```simple
@allow_facet_access(debug, inspect_readonly)
class LruCache:
    ...
```

The exact attribute spelling may be finalized with the broader capability system; the semantic requirement is mandatory.

---

## 19. Mission-Critical Profile

```sdn
aspect_policy:
  dynamic_attach: deny
  unload: deny
  lazy_io_after_start: deny
  domain_mutation: deny
  private_inspect: allow_signed_exact_abi
  activation: [static, startup]
  signed_pack: require
  catalog_hash: require
  deterministic_budget: require
```

Rules:

- All enabled aspects are fixed before operational state.
- No first-use disk I/O in real-time/interrupt/noalloc contexts.
- `try_facet<T>()` is permitted after startup; lazy-loading `facet<T>()` is not.
- Runtime `around` advice and hot patching are denied by default.
- Domain-mutating facets are rejected.
- Every configuration has a generated manifest and real system test.
- A failed aspect load prevents application publication rather than leaving a partially instrumented system.

For operational diagnostics that cannot satisfy these constraints, prefer an external debug process/protocol rather than in-process hot attachment.

---

## 20. Exact Performance Contract

## 20.1 Application startup with cold aspects

For `lazy_facet`, `manual`, and excluded aspects:

- The runtime reads the application Aspect Catalog only.
- No aspect-pack file is opened unless startup verification policy explicitly requires it.
- No module payload is decompressed.
- No aspect executable pages are mapped.
- No per-object state is allocated.
- No aspect source path is searched.

## 20.2 Business hot path

### Facet-only dynamic aspect

A normal business function contains no aspect branch. Cost appears only when aspect-aware code calls `facet<T>()`.

### Static omitted aspect

Core output should be byte-identical to a build with no aspect declaration, preserving Simple's existing static AOP guarantee.

### Patchable dynamic advice

The disabled path contains a patchpoint/NOP or equivalent trampoline. It may be extremely cheap but is not described as zero code footprint.

## 20.3 First use

First-use latency includes:

```text
catalog lookup
+ pack open/index map
+ signature/hash validation
+ selected dependency-closure decompression
+ module relocation
+ binding publication
```

It does not include decompression of unrelated modules in the same pack.

## 20.4 Steady state

- A retained `FacetRef<T>` invokes a direct witness/vtable entry.
- Repeated acquisition uses a type-level inline cache or hash lookup keyed by `(type_id, facet_id, generation)`.
- Loaded advice chains are preordered; they do not re-evaluate source pointcuts.

## 20.5 Configuration performance

- SDN aspect/variant files are parsed at build/deploy preparation, not normal application startup.
- Runtime profile selection is one ID lookup or a direct catalog section selection.
- Disabled profiles do not cause pack probing.
- Core module cache entries are reusable across lazy aspect profiles.

---

## 21. Diagnostics

### Compile/type diagnostics

```text
E-AF001 core declaration depends on optional aspect declaration
E-AF002 required facet implementation missing
E-AF003 ambiguous facet binding
E-AF004 invalid facet target pointcut
E-AF005 nominal binding used with dynamic/unloadable aspect
E-AF006 unauthorized private or mutable domain access
E-AF007 aspect dependency cycle
E-AF008 helper belongs to multiple aspects without explicit shared owner
E-AF009 direct business import from hidden aspect root
E-AF010 dynamic advice targets a function without a prepared join point
```

### Source/path diagnostics

```text
E-APATH001 relative aspect root escapes allowed workspace
E-APATH002 symlink escapes declared root
E-APATH003 duplicate aspect ID at same resolution rank
E-APATH004 aspect manifest identity conflicts with lockfile
```

### Pack/load diagnostics

```text
E-APACK001 malformed or unsupported pack index
E-APACK002 aspect/core ABI mismatch
E-APACK003 pack or chunk hash/signature failure
E-APACK004 decompression size/count limit exceeded
E-APACK005 variant fingerprint mismatch
E-APACK006 missing module dependency in pack/catalog
E-APACK007 activation cycle
E-APACK008 attempted lazy I/O in forbidden execution context
```

### Performance-policy diagnostic

```text
E-AF011 transparent first-join-point activation requested under an exact-zero-overhead policy
```

Help should explain that the user must choose static omission, explicit facet activation, or a patchable low-overhead mode.

---

## 22. Compiler and IR Architecture

## 22.1 Frontend AST

```simple
struct FacetInterfaceDecl
struct FacetImplDecl
struct FacetBindDecl
struct FacetRequireDecl
struct AspectContext
```

Extend pointcut AST with type selectors rather than creating a new predicate AST.

## 22.2 HIR/type checking

Responsibilities:

- resolve facet contracts,
- validate implementation completeness,
- expand known closed-world targets,
- preserve open-world binding rules,
- enforce access capabilities,
- check ambiguity and requirements,
- reject core-to-aspect dependencies.

## 22.3 Placement IR

```simple
struct DeclPlacement:
    decl: DeclId
    owner: CoreOrAspect
    reason: PlacementReason

enum PlacementReason:
    LexicalAspect
    AspectPackage
    ExplicitAttribute
    UsageInferred
    SharedExplicit
```

## 22.4 Binding IR

```simple
struct FacetBindingPlan:
    aspect_id: AspectId
    facet_interface_id: TypeId
    target_predicate: TypePredicateBytecode
    implementation_id: TypeId
    representation: Attached | NominalStatic
    multiplicity: Single | Multi
    access: FacetAccess
    required: bool
```

## 22.5 MIR/runtime primitives

```text
facet_lookup(base, facet_id, policy)
facet_bind_type(type_id, facet_id, witness_factory, generation)
facet_unbind_generation(generation)
advice_bind_slot(slot_id, chain, generation)
advice_unbind_generation(generation)
aspect_publish_generation(generation)
```

Static builds lower these away when possible. Dynamic builds preserve only the required primitives and slots.

## 22.6 Backend/packaging

New outputs:

- facet contract metadata in SHB,
- binding summary metadata in ordinary aspect-module SMF,
- aspect-pack directory,
- application Aspect Catalog,
- per-pack/module content hashes.

---

## 23. Integration with Existing Simple Architecture

### Existing AOP

Retain the current `on pc{...} use ...` advice grammar and ordering. Add structural facet declarations and type selectors as a separate lowering path.

### Existing mixins

Reuse mixin composition inside facet implementations. Do not use mixins to inject dynamic facet state into base layouts.

### Existing MDSOC+

Treat each aspect as a vertical functional group with internal layers:

```text
aspects/debug/
  contract/
  binding/
  domain/
  runtime/
  tooling/
  test/
```

This keeps a debug agent from reading unrelated logging or profiler implementation while preserving layer boundaries inside the aspect.

### Existing variants

Generalize the current variant-root computation to accept an aspect package-family root and the application's active selection fingerprint.

### Existing SMF and loader

Use embedded ordinary SMF blobs in pack v1. Add an `AspectPackProvider` before changing the ordinary SMF reader format.

### Existing `note.sdn` and JIT

Each embedded module retains its own metadata, lazy generic information, and relocation structures. The pack directory only routes to the module.

### Existing hot reload/lifecycle

Use a composite owner ID:

```text
pack_id : module_id : aspect_generation
```

This permits module-level ownership even though several modules share one physical file.

---

## 24. Development Plan

## Phase 0 — Specification and executable scenarios

- Finalize terminology and grammar.
- Add SSpec scenarios before implementation.
- Define ABI and diagnostic codes.
- Define exact performance assertions.

## Phase 1 — Static attached facet binding

- Parse `facet interface`, `facet impl`, `bind facet`, `require facet`.
- Add `type`, `implements`, and `subtype` selectors.
- Implement closed-world witness tables.
- Implement `try_facet<T>()` without dynload.
- Enforce core dependency and access rules.

## Phase 2 — Open-world registry

- Publish type descriptors and implemented-interface IDs from modules.
- Register binding rules in either load order.
- Add generic public-interface and concrete private-layout implementations.
- Add binding ambiguity diagnostics.

## Phase 3 — Relative aspect packages

- Implement resolver-owned aspect manifests.
- Add explicit relative roots, canonicalization, lockfile identity, and conflict checks.
- Reuse variant selection within aspect package roots.
- Add LSP navigation showing logical aspect ID and physical source.

## Phase 4 — Aspect pack v1

- Add `SMF_FLAG_ASPECT_PACK` and uncompressed pack directory.
- Embed independently compressed complete ordinary SMF modules.
- Implement `AspectPackProvider` returning module bytes.
- Reuse existing in-memory reader, relocation, JIT, and lifecycle paths.

## Phase 5 — Application catalog and lazy facet activation

- Emit `AspectCatalog` in app SMF.
- Implement exact pack routing and `lazy_facet`.
- Add index/chunk caches and concurrent activation transaction.
- Ensure no runtime directory search or config parsing.

## Phase 6 — Startup AOP and static weaving integration

- Load startup packs before application publication.
- Register aspect-owned advice plans.
- Preserve current no-aspect static output guarantee.

## Phase 7 — Patchable dynamic join points

- Emit finite join-point slot tables.
- Implement architecture-specific NOP/jump or trampoline patching.
- Enforce W^X, safe points, and instruction-cache synchronization.
- Measure disabled and enabled fast paths separately.

## Phase 8 — Unload/hot deployment

- Generation pinning and quiescence.
- Atomic remove/replace.
- Sidecar state lifecycle.
- Rollback and failure injection.

## Phase 9 — Pack optimization and formal verification

- Profile-guided co-load clustering.
- Shared compression dictionaries.
- Optional deduplicated pack metadata.
- Lean model for dependency direction, binding uniqueness, activation atomicity, and safe unload.

---

## 25. Test and Verification Plan

## 25.1 Language/system correctness

- Bind a facet to one concrete type.
- Bind to all implementors of a business interface.
- Load base before aspect and aspect before base.
- Load a new matching base module after the aspect is active.
- Verify no base object layout change.
- Verify required binding failures.
- Verify ambiguity and multi-provider behavior.
- Verify public-only versus private-layout ABI invalidation.
- Verify core-to-aspect dependency errors.
- Verify helper ownership inference.

## 25.2 Relative source roots

- Package-local, application, and external relative roots.
- Manifest-relative path resolution independent of CWD.
- Same-rank collision.
- Path and symlink escape rejection.
- Moving a root without changing logical IDs.
- Variant selection inside an aspect root.

## 25.3 Pack behavior

Use real generated SMF files and the production loader path; do not use mocks for the system acceptance suite.

- One pack with many modules; load one module only.
- Assert unrelated module bytes are not decompressed.
- Corrupt index, chunk, signature, and ABI hashes.
- Missing dependency and activation cycle.
- Pack path relocation relative to the application.
- Repack without recompiling modules.

## 25.4 Performance acceptance

With many catalogued cold aspect packs:

- zero pack opens before first permitted activation,
- zero aspect payload bytes read/decompressed,
- zero aspect code pages mapped,
- zero sidecar allocations,
- no runtime filesystem glob/stat storm,
- unchanged business function machine code for facet-only lazy profiles,
- core cache hits across aspect-profile changes.

Measure:

- startup wall time,
- pack file-open count,
- bytes mapped and faulted,
- bytes decompressed,
- RSS,
- minor/major page faults,
- first-use p50/p95/p99,
- repeated facet lookup cost,
- branch and instruction-cache behavior for patchable mode.

Thresholds should be set from a checked-in baseline on each supported host, not invented before measurement.

## 25.5 Mission-critical tests

- No lazy I/O after operational transition.
- Signed exact catalog/pack hashes.
- Startup failure is fail-closed.
- No mutating or hot aspects.
- Deterministic module and advice ordering.
- Fault injection at every activation transaction step.

---

## 26. Complete Example

### Source layout

```text
project/
  src/
    storage/cache/
      cache.spl
      lru_cache.spl
      aspects/
        debug/
          __init__.spl
          src/lru_private_debug.spl
  aspects/
    __init__.spl
    debug/
      __init__.spl
      src/cache_debug_contract.spl
      src/cache_debug_generic.spl
      src/cache_debug_advice.spl
    profile.performance/
      __init__.spl
      src/cache_sampler.spl
  config/
    var.sdn
    aspect.sdn
```

### Facet contract

```simple
facet interface Debuggable:
    fn debug_name(self) -> text
    fn snapshot(self) -> DebugSnapshot
```

### Generic implementation

```simple
facet impl CacheDebug<T: Cache>
    for T
    implements Debuggable
    public readonly:

    fn debug_name(self) -> text:
        self.base.name()

    fn snapshot(self) -> DebugSnapshot:
        DebugSnapshot(entries: self.base.entry_count())
```

### Concrete private implementation

```simple
facet impl LruPrivateDebug
    for LruCache
    implements Debuggable
    inspect readonly:

    fn debug_name(self) -> text:
        "LruCache"

    fn snapshot(self) -> DebugSnapshot:
        DebugSnapshot(
            entries: self.base._entries.len(),
            buckets: self.base._buckets.len(),
            free_nodes: self.base._free_list.len()
        )
```

### Bindings

```simple
bind facet Debuggable
    to pc{ implements(Cache) & !type(storage.cache.LruCache) }
    using CacheDebug

bind facet Debuggable
    to pc{ type(storage.cache.LruCache) }
    using LruPrivateDebug
```

### Optional advice

```simple
fn validate_after_put(ctx: AdviceContext):
    when val debug = ctx.target.try_facet<Debuggable>():
        check debug.snapshot().is_consistent()

on pc{ execution(* storage.cache.LruCache.put(..)) }
    use validate_after_put after_success priority 20
```

### Aspect config

```sdn
aspect:
  profile: diagnose
  profiles:
    prod:
      disabled: [debug, profile.performance]
    diagnose:
      enabled:
        debug: { activation: lazy_facet, pack: diagnostics }
        profile.performance: { activation: manual, pack: diagnostics }
```

### Deployment

```text
deploy/
  app.smf                      # core + AspectCatalog
  aspect/
    diagnostics.smf            # debug and performance-profile modules
```

### Runtime

```simple
val cache: Cache = create_cache()
cache.put(key, value)          # no debug facet branch in lazy_facet mode

when val debug = cache.facet<Debuggable>()?:
    print debug.snapshot()     # first call loads only debug module closure
```

---

## 27. Rejected Alternatives

### Make every business interface extend its aspect interfaces

Rejected because optionality becomes a mandatory type and ABI dependency.

### Rewrite every business call as `if aspect_enabled(...)`

Rejected because it spreads aspect awareness into core and leaves a load/branch on every path.

### Search aspect directories at runtime

Rejected because it harms startup, makes configuration non-deterministic, and creates path-security problems.

### One SMF file per tiny aspect module

Rejected as the only deployment form because it creates file-open and metadata overhead. It remains useful as an intermediate build artifact.

### One compressed stream per aspect pack

Rejected because selective loading becomes impossible.

### Automatically load an aspect on any matching business method by default

Rejected as the default because it requires pervasive dynamic join points and hidden first-use I/O. Available only as explicit `lazy_patchable` policy.

### Put dynamic facet state directly in the base object

Rejected because it changes layout, prevents independent unload, and imposes memory cost on objects that never use the aspect.

### Include aspect selection in every core cache key

Rejected because it creates a configuration-product explosion. Only transformations that change core output affect the core/weave cache key.

---

## 28. Final Recommendation

Implement the design around this minimal public surface:

```simple
aspect debug:
    facet interface Debuggable:
        fn snapshot(self) -> DebugSnapshot

    facet impl CacheDebug<T: Cache>
        for T
        implements Debuggable
        public readonly:
        ...

    bind facet Debuggable
        to pc{ implements(Cache) & type(storage.cache.**) }
        using CacheDebug

    on pc{ execution(* storage.cache.*(..)) }
        use trace_cache before
```

and this deployment model:

```text
app.smf
  uncompressed AspectCatalog

aspect/diagnostics.smf
  uncompressed AspectPackDirectory
  independently compressed ordinary SMF module chunks
```

The central invariant is:

```text
core is complete without an aspect;
facet binding gives a typed optional view;
AOP advice connects optional behavior only where requested;
variant selection chooses implementations;
the catalog and pack indexes prevent cold aspects from harming startup.
```

This model gives Simple a stronger capability than conventional static AOP: aspects can be large, separately placed, variant-aware, independently packaged, demand loaded, type checked, and safely absent without contaminating the business interface or hot path.

---

## 29. Research References

1. AspectJ Programming Guide, Eclipse Foundation — inter-type declarations and `declare parents`.
2. Eclipse Object Teams and OT/Equinox documentation — roles, teams, callin/callout, and architecture-level aspect bindings.
3. Bergel, Ducasse, Nierstrasz, Wuyts, **Classboxes: Controlling Visibility of Class Extensions**, 2005, doi:10.1016/j.cl.2004.11.002.
4. Bergel, Hirschfeld, Clarke, Costanza, **AspectBoxes — Controlling the Visibility of Aspects**, ICSOFT 2006.
5. Aracic, Gasiunas, Mezini, Ostermann, **An Overview of CaesarJ**, 2006, doi:10.1007/11687061_5.
6. Apel, Leich, Saake, **Aspectual Feature Modules**, IEEE TSE 34(2), 2008, doi:10.1109/TSE.2007.70770.
7. Dyer, Setty, Rajan, **Nu: Towards a Flexible and Dynamic Aspect-Oriented Intermediate Language Model**, Technical Report 07-06.
8. Dyer, Rajan, **Supporting Dynamic Aspect-Oriented Features**, ACM TOSEM 20(2), 2010, doi:10.1145/1824760.1824764.
9. Bockisch, Arnold, Dinkelaker, Mezini, **Adapting Virtual Machine Techniques for Seamless Aspect Support**, OOPSLA 2006, doi:10.1145/1167515.1167483.
10. OSGi Core Specification, lifecycle and lazy bundle activation policy.
11. Linux Kernel Documentation, **Static Keys** — jump-label patching for seldom-used fast-path features.
12. Panchenko, Auler, Nell, Ottoni, **BOLT: A Practical Binary Optimizer for Data Centers and Beyond**, 2018, arXiv:1807.06735.
13. Zstandard reference implementation and RFC 8878; independently framed compression and dictionaries.
14. containerd stargz snapshotter/related lazy-pulling systems — indexed on-demand content loading.

## 30. Simple Repository Evidence Examined

- `doc/02_requirements/language/aop/aop.md`
- `doc/05_design/lib/stdlib/aop_support_matrix.md`
- `doc/06_spec/03_system/compiler/mixin_spec.md`
- `src/compiler_rust/compiler/src/module_resolver/mod.rs`
- `src/compiler_rust/compiler/src/module_resolver/var_overlay.rs`
- `src/compiler/99.loader/module_resolver/var_resolution.spl`
- `doc/02_requirements/feature/var_resolution_rules.md`
- `doc/05_design/compiler/language_design/codegen/smf_note_sdn_implementation.md`
- `doc/05_design/compiler/language_design/codegen/simple_header_binary_design.md`
- `src/compiler/99.loader/loader/smf_cache.spl`
- `src/compiler/99.loader/loader/module_loader.spl`
- `doc/04_architecture/runtime/jit_index.md`
- `doc/03_plan/compiler/bootstrap/cross_platform_dynload_remaining_plan_2026-07-10.md`
