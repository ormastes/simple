# Simple Aspect Facets and Demand-Loaded SFM Packs

**Subtitle:** Typed structural AOP, relative aspect packages, variant-aware deployment, and low-overhead lazy activation
**Status:** Revised design aligned with current Simple architecture
**Date:** 2026-08-04
**Repository examined:** `ormastes/simple`, `main`
**Compatibility filename:** `aspect_facet_dynload_smf_pack_design_2026-08-04.md`; “SMF pack” in the original request now means an SFM aspect pack containing opaque SMF code units.

<!-- codex-design -->

> **Normative alignment correction:** Current Simple architecture assigns optional
> feature/capsule packaging to SFM and keeps ordinary SMF modules opaque. This
> revision therefore places `AspectCatalog` and `AspectPackDirectory` in SFM
> outer metadata, extends the existing object-provider/loader/dynSMF lifecycle,
> resolves variants entirely at build time, and permits V1 facets to use only
> public contracts or explicit owner-exported capability facades. Earlier
> proposals for `SMF_FLAG_ASPECT_PACK`, private-layout inspection, or a parallel
> activation registry are rejected.

### Implemented first-slice modules

The current pure-Simple slice maps directly to existing owners:

- `compiler/00.common`: versioned structural predicate bytecode;
- `compiler/10.frontend`, `20.hir`, `35.semantics`: feature-scoped facet
  declarations, lowering, canonical name resolution, and coherence;
- `std.aop.facet`: no-I/O, policy-aware optional, and required typed acquisition;
- `compiler/99.loader/module_resolver`: manifest-relative aspect roots;
- `std.sfm.aspect_pack`: `SFM2` outer directory and independent opaque SMF frames;
- `compiler/99.loader/loader`: exact-digest provider, application catalog, and
  an activation transaction composed over existing dynSMF/generation contracts.

This slice stages and validates the control-plane contracts. Executable mapping,
relocation, resource pin/drain, and dynamic advice patchpoints remain owned by
the established loader and must not be inferred merely from catalog publication.

---

## 1. Executive Decision

Simple should support applying an optional facet interface to existing business objects and business interfaces through AOP, but it must not model the dynamic case as ordinary interface inheritance.

The final model has four distinct concepts:

1. **Aspect** — a named, optional concern and deployment unit, such as `debug`, `logging`, `profile.memory`, `profile.performance`, or `unit.time`.
2. **Facet interface** — the statically typed API that the aspect exposes as an optional view of a business object.
3. **Facet binding** — a structural AOP rule that binds a facet interface and implementation to business types selected by a type pointcut.
4. **Aspect pack** — one SFM container holding multiple opaque ordinary SMF modules, indexed without decompressing module metadata and loaded a module or co-load cluster at a time.

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
- At deployment, multiple modules may be grouped into one `kind=aspect_pack` SFM under the application's `aspect/` path.
- The application SFM contains a small uncompressed **Aspect Catalog**. It routes a facet or dynamic join-point slot directly to its pack and module without scanning directories or opening every pack.
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

It selects execution join points and weaves `before`, `after_success`, `after_error`, or `around` advice. The declared support matrix names `execution`, `within`, and `attr`, but the current tokenized evaluator reliably matches only its implemented function selector paths; `within`/`attr`, type-introduction selectors, and link-time weaving require focused implementation evidence before they may be claimed. All grammar in this document is proposed and feature-gated.

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

Internally this is a **role adapter** described by a frozen witness descriptor
whose ordered method entries resolve through the ordinary-SMF symbol table.
There is no executable witness factory. The term `role` is useful in the
compiler/runtime design, but does not need to become an additional public
keyword.

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

A deployment SFM capsule containing multiple independently indexed opaque SMF modules or co-load clusters. SFM owns the directory, compression, signature, and catalog metadata; SMF remains the existing executable module format.

### 3.8 Aspect Catalog

A small uncompressed section in the application SFM. It contains only the data needed to route an aspect request to a pack; it does not contain full aspect module metadata or code.

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

A concrete implementation that needs representation-specific data must request it through an explicit owner-exported capability facade:

```simple
facet impl LruCacheDebug
    for LruCache
    implements Debuggable
    public readonly:

    fn snapshot(self) -> DebugSnapshot:
        DebugSnapshot(
            buckets: self.base.debug_capability().bucket_count(),
            free_nodes: self.base.debug_capability().free_node_count()
        )
```

The capability is owned and versioned by `LruCache`; the aspect never reaches through tree-private state. Arbitrary private-layout inspection/mutation is deferred beyond V1.

## 6.7 Facet acquisition

```simple
fn print_cache_debug(context: AspectExecutionContext, cache: LruCache):
    when val debug = context.facet<Debuggable>(cache)?:
        print debug.snapshot()
```

The explicit context is mandatory for dynamic acquisition. It is the stable
application-owned capsule that reaches the canonical loader, registry, and
lifecycle state. A future lexical-context feature may permit the shorter
`cache.facet<Debuggable>()` spelling inside a bound aspect scope, but an
implicit process-global/current context is forbidden.

`AspectExecutionContext` is a compiler-known nominal source type for facet
syntax. Application code may use it in signatures without importing
`app.startup` implementation modules; the compiler binds it to the canonical
application-owned identity and rejects an unrelated same-named class/struct.
The embedding entrypoint supplies the value; facet source does not construct
the application capsule.

Required dynamic APIs:

```simple
context.try_facet<T>(obj) -> Option<FacetRef<T>>
# Never performs I/O. Returns only an already-bound facet.

context.facet<T>(obj) -> Result<Option<FacetRef<T>>, FacetAcquireError>
# May load an aspect when policy is lazy_facet.

context.require_facet<T>(obj) -> Result<FacetRef<T>, FacetAcquireError>
# May load; absence is an error.

aspect.load(name: AspectId) -> Result<AspectHandle, AspectLoadError>
aspect.unload(handle: AspectHandle) -> Result<(), AspectUnloadError>
```

`FacetRef<T>` is compiler surface sugar over a private application-local
adapter generated for `(Base, FacetContract)`. The adapter retains the typed
base operand and an application-owned opaque descriptor-lease handle; it does
not decode or embed the runtime descriptor aggregate. Context-first validation
checks the complete contract, and context-first method selection uses the
compile-time ordinal and expected name. Generated code then prepends the typed
base as ABI argument zero and lowers through ordinary `CallIndirect`.
It is never serialized and never uses the currently incomplete `dyn Trait`
vtable path or an `Any`/raw-pointer erased base.

A leased dynamic `FacetRef<T>` is an affine lexical guard: it cannot be copied,
stored globally, returned, or moved into async/thread work, and the compiler
must release its lease through the same context on every scope exit. Static
refs with no lease remain ordinary values. The current public
`dynamic_facet_ref` constructor is compatibility-only and is not production
dynamic acquisition evidence.

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
  app.sfm
  aspect/
    observability.sfm
    diagnostics.sfm
    units.sfm
```

Example grouping:

```text
observability.sfm
  logging.*
  metrics.*
  trace.common.*

diagnostics.sfm
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

The application SFM contains an uncompressed `AspectCatalog` section.

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

Each aspect-pack SFM contains a small uncompressed `AspectPackDirectory` section.

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

## 12. Backward-Compatible SFM Aspect-Pack Implementation

The lowest-risk first implementation embeds complete ordinary SMF modules as pack chunks:

```text
AspectPack SFM
  SFM manifest + PackDirectory  uncompressed
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

## 12.1 SFM container compatibility

Extend the pure-Simple SFM manifest/container contract with a versioned
`kind=aspect_pack` directory. Do not add SMF flags or sections and do not depend
on planned SMF compression/trailer work. Every embedded payload remains a
complete current ordinary SMF image consumed through `SmfReaderMemory`.

An older SFM reader rejects the unsupported SFM kind/version before exposing a
payload. `AspectPackProvider` validates the outer directory and returns only the
selected opaque SMF bytes through the existing object-provider boundary.

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

Even when `debug`, `profile.memory`, and `profile.performance` share `diagnostics.sfm`, the directory must allow loading only `debug.cache` and its dependency closure.

## 13.4 Repacking does not recompile

The compiler cache stores ordinary module SMF images or equivalent module chunks. The packer consumes those artifacts. Changing pack placement is a packaging operation.

---

## 14. Loader and Runtime Architecture

```text
Application SFM
   |
   +-- AspectCatalogReader
           |
           +-- DynSmfSession activation adapter
                   |
                   +-- AspectPackIndexCache
                   +-- AspectPackProvider
                   +-- FacetBindingRegistry
                   +-- AdviceBindingRegistry
                   +-- ObjectProvider / ModuleLoader / existing SMF reader
                   +-- existing generation and resource lifecycle owners
```

## 14.1 New components and adapters

### AspectCatalogReader

Reads the application catalog once and exposes ID-based routes.

### AspectPackIndexCache

Caches only validated SFM manifest/directory mappings. It does not imply loading
payload chunks. Keys include pack digest, catalog generation, target, resolved
variant fingerprint, runtime ABI, core public ABI hash, and core layout ABI
hash. Entries are bounded and invalidated when any exact identity or semantic
ABI dimension changes; decoded module entries additionally respect canonical
loader resource pins.

### AspectPackProvider

Implements module lookup by `(pack_id, module_id)`, decompresses selected chunks, and returns ordinary SMF bytes through `ObjectProvider` to the existing loader. It is a provider adapter, not a second module loader.

### FacetBindingRegistry

Maps:

```text
(concrete_type_id, facet_interface_id, aspect_generation)
    -> resolved witness descriptor with ordered method entries
```

It also stores open-world rules keyed by implemented business interface IDs.

Each binding summary names exactly one target identity: `concrete_type_id` or
`business_interface_id`. Production activation stages candidates only after
`ModuleLoader` proves that every witness symbol is owned by the selected module
owner, and publication requires the candidate's exact
`activation_key@generation`. One active publication pointer per aspect makes
replacement atomic while exact-generation unbind remains isolated. Lookup
combines concrete matches with open-world rules and fails on ambiguity.

This registry owns binding visibility only; the existing lifecycle manager
owns generation state and leases. `AspectApplicationRuntime` resolves and pins
the exact binding generation through `acquire_published_facet`, and removes
visibility before unload drain. Dynamic advice-slot publication is loader-owned:
catalog metadata identifies prepared slot, form, priority, specificity, witness,
and capabilities, and loader ownership checks the witness before staging.
Advice and facet publication are computed before the existing lifecycle
promotion; exact-generation unbind removes both registries before drain. No
runtime pointcut evaluator or parallel advice lifecycle/call path is introduced.
Native driver/runtime wiring and representative startup, lookup-latency, and
RSS evidence remain explicit verification residuals; this implementation does
not convert its focused static/unit/system coverage into performance claims.

### AdviceBindingRegistry

Maps catalog-prepared join-point slots to static, startup, or dynamic advice
chains. Chains use the existing static AOP order: priority descending,
specificity descending, then witness name ascending. Candidate identity is the
exact activation key and generation; lookup rejects unknown slots and records
hits, misses, disabled checks, and disabled branches. A stable descriptor marks
the disabled path as one prepared-slot check and one conditional branch, with
`disabled_footprint_bytes = 1` explicitly labeled as a contract minimum rather
than backend measurement, never as zero overhead. Mission policy denies runtime
patch publication.

The frozen execution seam is `advice_dispatch_slot`. It accepts one prepared
slot and one phase (`before`, `after_success`, or `after_error`), applies the
active exact-generation filter and canonical chain order, validates every
record's resolved address and owner against `ModuleLoader`, then invokes through
the loader's existing native zero-argument `fn() -> i64` primitive; dynamic
advice pack producers must emit that fixed ABI, and returned values are receipts
rather than substitutes for business control flow. Validation is two-pass so
an invalid later record cannot cause partial phase execution. Dispatch counters
cover attempts, successful callback invocations, failures, and rejected around
requests. `around` admission and dispatch both fail closed until an actual
exactly-once proceed continuation is designed and lowered.

`CompileOptions.prepared_dynamic_advice` now selects a real producer from the existing
`WeavingConfig`/`weave_function` authority. It emits one stable execution slot
per matched function and automatic `simple.prepared_advice_dispatch.v1(slot,
phase)` MIR intrinsics at entry, successful returns, and abort exits. Duplicate
rules of one phase share one call because the loader dispatches the whole chain.
Slot identity includes module, function name, canonical MIR signature, and
lowering-owned symbol identity so overloads cannot alias. Entry injection uses
`MirFunction.entry_block`, not block-array position.

`PreparedAdviceSlotPlan` is the frozen common contract for that future lane. Its
fields are `schema_id`, `schema_version`, `slot_id`, `target_function_id`, and
`admitted_forms`. The producer boundary accepts only schema v1 and
`before`/`after_success`/`after_error`; empty, duplicate, unknown, and `around`
forms fail closed. `MirModule.prepared_advice_slots` is preserved by every
current module reconstruction and VHDL aggregation. Deterministic JSON uses
`serialize_mir_prepared_advice_slots`; the driver collects and validates the
table and rejects duplicate global slot IDs. Native/SMF emission still refuses
non-empty tables until the reviewed explicit execution-context bridge exists. The option
participates in compile/cache identity; check/interpreter reject it directly,
and JIT/all AOT backends reject produced slots centrally before code generation.
The common backend entry additionally rejects slot metadata or the prepared
intrinsic itself, preventing direct backend callers from silently dropping it.

#### Production prepared-slot ownership status

The loader registry remains the sole publication authority. A typed immutable
dispatch projection is derived only after loader owner/address validation and
carries exact publication and generation identity. It is a port contract, not
a second registry; no native table is installed yet.

The required producer sequence is:

1. frontend/HIR select and validate a finite set of permitted sites;
2. `compiler/50.mir` assigns stable slot IDs and emits prepared-dispatch MIR
   plus module slot metadata;
3. MIR optimization preserves the operation and exactly-once placement;
4. `compiler/80.driver` validates the exact typed `AspectExecutionContext`
   argument and rewrites v2 to the ordinary source-owned
   `prepared_advice_dispatch_context_invoke` call;
5. existing backends lower that ordinary call through their normal ABI;
6. the context-owned loader registry binds an exact generation, and runtime
   dispatch invokes the preordered chain under its matching generation lease.

Steps 1–6 and the deterministic table contract exist for the admitted
sequential execution path. Release remains blocked on the callback-safe state
gate: projection/publication/lifecycle mutation must be serialized, pins must
be committed to canonical state before callbacks run, no lock may cross a
callback, and unload must observe those committed pins before resource cleanup.

The backend bridge cannot be implemented as a slot/phase-only native lookup.
The emitted operation currently has no loader-owned lifecycle handle or
generation token, while safe callback execution requires the canonical
generation lease to remain pinned through the last callback. A separately
reference-counted runtime snapshot would create a second unload authority and
is rejected even if its replacement and invalidation were internally atomic.
The reviewed bridge threads one exact typed `AspectExecutionContext` reference
through the opt-in target. That stable capsule solely owns `ModuleLoader`,
`LifecycleManager`, the facet/advice registries, and `AdviceDispatchProjection`.
The driver rewrites `simple.prepared_advice_dispatch.v2(context, slot, phase)`
to an ordinary source call; it does not install a backend trampoline or a
process-global handle. Until that contract is implemented, all code-generation
paths retain E-AF010.

#### Resolver composition boundary

Automatic discovery uses the existing `85.mdsoc/feature/module_loading`
application boundary. `ModuleResolverDiscoveryPort.resolve_inputs(inputs)` is
implemented by the 99-loader adapter and injected by production CLI/public-driver
composition. `ModuleResolverPort` remains the immutable shared result. Shared
normalization/containment/importer authorization lives once in layer 00; the
loader retains manifest-relative discovery, variant selection, filesystem and
symlink policy. Legacy constructors select the explicit empty adapter.

### DynSmfSession activation adapter

Extends the existing `DynSmfManifestEntry`/`DynSmfSession` policy and evidence contract to run the load/validate/bind/publish transaction. It preserves manifest-derived status, reason, generation, unload/reload, `--no-dynsmf`, and `SIMPLE_DYNSMF` behavior. It does not introduce a second lifecycle registry.

### Application aspect runtime owner

`app.startup.AspectApplicationRuntime` retains the selected `AspectCatalog`,
external `AspectPackTrustPolicy`, canonical bounded `AspectPackProviderCache`,
and `AspectActivationCoordinator` for one process. Catalog routes carry a
validated deployed-image-relative `pack_path`, exact pack/module digests, and
core public/layout ABI hashes. The application I/O owner opens only the path
returned by `pack_path_for`; the facade accepts those bytes without adding a
filesystem or environment shortcut. Admission always uses
`AspectPackProvider.from_trusted_bytes`, and executable activation always uses
`AspectActivationCoordinator.activate_with_loader`.

The runtime activation overload receives that one cache instance. Dependency
staging selects/decompresses each module through `get_module_bytes` once, maps
and validates through `ModuleLoader`, then acquires every exact module cache pin
before atomic publication. A partial pin failure releases only pins acquired by
that transaction and rolls back mappings. Published metadata retains the exact
module keys and activation owner key.

The facade exposes `acquire_published_generation` and
`release_published_generation` as the future `FacetRef` lease boundary. They
delegate opaque replay-safe `GenerationToken` issuance/release to the existing
`LifecycleManager`; `std.aop` must not import application or OS owners directly.
The app boundary converts those tokens to ownership-neutral
`FacetGenerationLease` values carried by dynamic `FacetRef` instances.

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
      read the SFM manifest and aspect-pack directory only
      verify index hash/signature
      resolve module dependency closure
      decompress selected module chunks
      load and relocate through existing ModuleLoader
      validate base/facet ABI hashes
      resolve every ordered witness descriptor method through ModuleLoader
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

Only one resolved ordered witness descriptor is needed per bound concrete type
and generation. All objects of that type share it; each retained ref still owns
its exact lease.

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

The current SMF mmap cache maps an ordinary executable module as a unit. That remains appropriate for opaque embedded SMF payloads, but the outer SFM aspect pack must not map or decompress unrelated payload chunks.

Aspect packs require an SFM provider path integrated below the current object-provider/cache seam:

- Read the bounded SFM header/manifest and uncompressed pack directory.
- Use canonical file/mmap facades; app and feature leaves add no raw `rt_*` calls.
- Do not issue whole-file sequential readahead.
- Map or read only selected compressed chunk ranges.
- Issue `WILLNEED` only for explicit startup/preload closures.
- Cache decompressed module bytes by `(pack digest, module digest, target, resolved variant fingerprint, runtime ABI)`.
- Bound negative cache entries; invalidate on catalog/generation/digest changes.
- Evict cold chunks independently while respecting loader generation pins and resource refcounts.

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
| owner capability | owner-exported read-only facade | capability ABI |

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

or export a named capability facade:

```simple
class LruCache:
    fn debug_capability(self) -> LruCacheDebugCapability:
        ...
```

V1 does not grant arbitrary private, mutating, or structural access. Such access requires a future language-wide unsafe capability design and is not implied by a layout hash or pack signature.

---

## 19. Mission-Critical Profile

```sdn
aspect_policy:
  dynamic_attach: deny
  unload: deny
  lazy_io_after_start: deny
  domain_mutation: deny
  private_inspect: deny
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
- The application calls `enter_operational()` explicitly. In mission mode the
  transition fails until every `startup` catalog entry is published; afterward
  `LazyIo`, `DynamicAttach`, `Unload`, and `Patch` authorization fails closed.
- Ordinary unload quiesces the exact aspect owner, makes its bindings
  unavailable, and returns a retryable `quiescing` status while generation
  tokens drain. The drained completion unloads existing `ModuleLoader` owners,
  releases exact module-cache pins, invalidates the exact provider, completes
  the canonical lifecycle generation, and only then drops publication metadata.

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

- A retained `FacetRef<T>` invokes its compile-time ordinal from the resolved
  descriptor through ordinary indirect-call lowering while its lease is held.
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
facet_bind_type(type_id, facet_id, resolved_witness_descriptor, generation)
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
- SFM-owned aspect-pack directory,
- application-SFM Aspect Catalog,
- per-pack/module content hashes.

Implementation status: SHB v1.1 writes an optional ninth facet-contract
section and reads both v1.0/eight-section and v1.1 artifacts. The canonical
`facet_witness_symbol(implementation_id)` is an inert descriptor identity and
method-symbol prefix; it is not an executable factory export. Facet
implementation method bodies are retained in `FacetMethodDecl.body_source` and
`HirFacetMethod.body_source`. Receiver-independent bodies project into ordinary
compiler input under
`facet_witness_method_symbol(implementation_id, method_name)`, currently
`<implementation>__facet_witness__<method>`, and proceed through ordinary HIR
and MIR function lowering. The receiver ABI passes the concrete base as
argument zero; token-aware projection lowers `self.base` to that explicit
parameter without rewriting comments. Receiver tokens in strings,
interpolation, raw strings, or qualified access fail closed. Bare `self` fails with
E-AF005 because wrapper-value semantics are not defined, while its facet
AST/HIR metadata remains intact. Interface methods remain declaration-only.
Receiver-aware resolved calls prepend the base operand and lower through the
same `CallIndirect` operation, rejecting signature arity mismatches. Artifact
admission derives a frozen `FacetWitnessDescriptorV1` from canonical
`FacetContractMetadata.method_names` and requires every contract-ordered
canonical method symbol. Only those ordered method symbols are executable. The
artifact encoder accepts only inert descriptors (`owner_id == ""` and every
`resolved_address == 0`); serialization of loader-resolved authority fails with
E-AF002 rather than silently dropping it. The ordinary-SMF writer supports deterministic multiple
`.text`-relative symbol entries and string offsets, and the AOT path extracts
those symbols only from one relocatable ELF64 object; multi-object and embedded
ELF facet modes fail closed. The loader checks exact catalog equality, exact
descriptor ABI hash, and same-module ownership for every method symbol, then
stores ordered resolved method entries in the published binding. Application
acquisition returns an exact method address with its generation lease; calls
lower through existing `CallIndirect` from that explicit operand. Inherited
method-table flattening, generic implementations/methods, and user-facing
type-directed facet-method sugar remain fail-closed residuals; no native
factory return ABI, runtime-private invoke path, or placeholder witness exists.

## 22.7 MDSOC owner map

| Contract | Authoritative owner | Visibility rule |
|---|---|---|
| `AspectId`, `FacetId`, `TypePredicateBytecode` | `src/compiler/00.common/structural_contracts/` when shared by four or more compiler consumers | Common immutable contracts only; no layer implementation leaks. |
| Facet/aspect syntax | `src/compiler/10.frontend/` | Public only to the next lowering layer through its facade. |
| Facet type/coherence rules | `src/compiler/20.hir/`, `25.types/`, `30.types/`, `35.semantics/` according to existing responsibility | No sibling-private reach-through; common nodes are extracted rather than imported sideways. |
| Static binding/weave plan | `src/compiler/50.mir/` and existing `85.mdsoc/` facade | Existing AOP exactly-once ordering remains authoritative. |
| Packaging/orchestration | `src/compiler/80.driver/` plus `src/lib/nogc_sync_mut/sfm/` codec | Driver coordinates; SFM owns outer format. |
| Resolution/load | `src/compiler/99.loader/` | Resolver owns source roots; loader owns module publication. |
| dynSMF policy/lifecycle evidence | `src/os/smf/` | Startup app is a thin facade-using adapter only. |

No aspect may bypass a target owner’s tree-private state. Shared contracts move
to a common node only when their consumer count justifies it; otherwise they
stay owner-private and are exposed through the parent/next-layer facade.

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

The directory sketch is logical, not permission to bypass compiler or domain
owners. Aspect leaves consume only public/next-layer facades and explicit
owner-exported capabilities.

### Existing variants

Reuse the current variant-root computation while resolving the aspect package at build time. The emitted SFM catalog contains only concrete selected module IDs and the selection fingerprint. Runtime activation never reevaluates `variants/` or traverses variant roots.

### Existing SMF and loader

Use embedded ordinary opaque SMF blobs in SFM aspect-pack v1. Add `AspectPackProvider` as an `ObjectProvider` adapter and do not change the ordinary SMF reader format.

### Existing `note.sdn` and JIT

Each embedded module retains its own metadata, lazy generic information, and relocation structures. The pack directory only routes to the module.

### Existing hot reload/lifecycle

Extend existing loader/dynSMF generation ownership with a composite owner ID:

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

## Phase 1 — Shared type predicates and static attached facet binding

- Add `TypePredicateBytecode` and deterministic `type`, `implements`, and `subtype` evaluation against the compile-time `ModuleSurface` projection.
- Parse `facet interface`, `facet impl`, `bind facet`, `require facet`.
- Implement closed-world witness tables.
- Implement `try_facet<T>()` without dynload.
- Enforce core dependency and access rules.

## Phase 2 — Open-world registry

- Publish type descriptors and implemented-interface IDs from modules.
- Register binding rules in either load order.
- Add generic public-interface and explicit owner-capability implementations.
- Add binding ambiguity diagnostics.

## Phase 3 — Relative aspect packages

- Implement resolver-owned aspect manifests.
- Add explicit relative roots, canonicalization, lockfile identity, and conflict checks.
- Reuse variant selection within aspect package roots.
- Add LSP navigation showing logical aspect ID and physical source.

## Phase 4 — SFM aspect pack v1

- Add versioned `kind=aspect_pack` SFM manifest metadata and an uncompressed pack directory.
- Embed independently compressed complete ordinary SMF modules.
- Implement `AspectPackProvider` as an `ObjectProvider` adapter returning module bytes.
- Reuse existing in-memory reader, relocation, JIT, and lifecycle paths.

## Phase 5 — Application catalog and lazy facet activation

- Emit `AspectCatalog` in the application SFM.
- Implement exact pack routing and `lazy_facet`.
- Extend `DynSmfSession`, loader generation staging, and resource lifecycle for the concurrent activation transaction; do not add a parallel manager.
- Add bounded index/chunk caches with exact keys, invalidation, eviction, and negative-cache policy.
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
- Verify public-contract versus owner-capability ABI invalidation.
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
    public readonly:

    fn debug_name(self) -> text:
        "LruCache"

    fn snapshot(self) -> DebugSnapshot:
        DebugSnapshot(
            entries: self.base.debug_capability().entry_count(),
            buckets: self.base.debug_capability().bucket_count(),
            free_nodes: self.base.debug_capability().free_node_count()
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
  app.sfm                      # application capsule + AspectCatalog + core SMF payload
  aspect/
    diagnostics.sfm            # aspect-pack SFM with opaque SMF modules
```

### Runtime

```simple
val context: AspectExecutionContext = app.aspect_execution_context()
val cache: LruCache = create_cache()
cache.put(key, value)          # no debug facet branch in lazy_facet mode

when val debug = context.facet<Debuggable>(cache)?:
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
app.sfm
  uncompressed AspectCatalog + opaque core SMF payload

aspect/diagnostics.sfm
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
## Exact-generation dispatch lifecycle addendum (2026-08-04)

The typed dispatch operation consumes `AdviceDispatchProjection`, canonical
`AdviceBindingRegistry`, canonical `LifecycleManager`, and `ModuleLoader`, and
returns their updated registry/lifecycle values plus status, reason, invocation
receipts, and acquired/released token counts. Tests inject a typed callback to
observe exact chain order and callback failure without calling fabricated
native addresses; production supplies the existing native zero-argument call.

Publication ordering is derive/validate projection, register and promote the
exact lifecycle generation, then install the coordinator value. Retirement
computes facet/advice removal, exact projection invalidation, the quiescing
publication, and exact lifecycle quiesce before assigning the next coordinator
state; only that fully invalidated state may evaluate drain and unload
resources.

## 31. Reviewed Execution-Context Bridge (2026-08-04)

`AspectExecutionContext` is the required stable application reference capsule.
It solely owns the validating `ModuleLoader`, `LifecycleManager`, canonical
facet/advice registries, and `AdviceDispatchProjection`; `AspectApplicationRuntime`
and `AspectActivationCoordinator` reference it instead of copying those mutable
owners. Activation, facet acquisition/release, prepared advice dispatch, and
unload therefore observe one exact state.

Prepared targets opt in with one typed context parameter. MIR emits
`simple.prepared_advice_dispatch.v2(Copy(context_arg), slot, phase)` and a
driver pass rewrites a validated v2 instruction to an ordinary direct call of
`prepared_advice_dispatch_context_invoke`. The dispatcher synchronously stores
the returned registry/lifecycle state and reports failure only after token
cleanup. A target without the exact context, or any backend that receives a
residual v1/v2 intrinsic, fails E-AF010. Hosted CPU AOT entry-closure is the
first admissible surface; other surfaces require separate ABI/link evidence.

Dynamic facet acquisition uses the same lexical context once per retained ref,
not once per method. The compiler generates a private typed adapter containing
the concrete base and an opaque application-owned descriptor lease, selects
methods through the context-first checked ordinal accessor, and emits the
existing base-first `CallIndirect`. Exact descriptor version/hash/count/order/
name/owner/address checks precede ref construction. Lease release is
compiler-inserted on every modeled lexical exit.

Rejected designs are a global/current context cell, a numeric handle registry,
copied coordinator/lifecycle state, backend-specific raw callbacks, existing
`dyn Trait` (no production vtable ABI), and `Any`/raw-pointer base erasure.

### 31.0 Callback-safe concurrency correction

The earlier audit found that dispatch accepted copied registry/lifecycle values
and returned replacements after callbacks, which was safe only for sequential
tests. That defect is now closed on the context-owned production path: canonical
pins and attempt counters are installed before callback invocation, finalize
merges deltas into current state, and unload observes the committed pins. The
context-owned path also ignores caller-supplied loader compatibility values and
uses only its retained canonical loader. Legacy isolated-value compatibility
composition is not a concurrent application ownership boundary.

Production advice dispatch now uses a three-part operation owned by
`app/startup`, not by `AdviceBindingRegistry`:

1. **Prepare under the application state mutex:** validate the current
   publication/projection and loader identity, acquire every exact generation
   token, and commit lifecycle/counter mutations before returning a private
   ticket.
2. **Invoke with no locks held:** execute the immutable ordered callback plan.
   Reentrant dispatch and callback-requested unload must not deadlock.
3. **Finish under the same mutex:** release the ticket tokens in reverse order,
   commit outcome counters, and only then return or panic.

Activation publication and unload invalidation/quiesce use that same state
mutex. Physical loader cleanup remains outside callback execution and may begin
only after the canonical lifecycle is quiescing and drained; one retirement
claim prevents duplicate cleanup by concurrent unload retries. The lazy I/O
single-flight mutex is a separate gate and is not a substitute for this state
owner.

`advice_binding_registry.spl` is limited to publication/order/lookup/unbind.
An immutable loader projection module owns row derivation and owner/address
validation. `os/smf/LifecycleManager` remains the sole token authority.
`ModuleLoader`/`ResourceLifecycleManager` remain the physical mapping/cache
owners. `AspectExecutionContext` composes those owners and alone serializes
their transition order. Publication/lookup counters remain registry-owned;
dispatch attempt/invocation/failure counters move with the application
coordinator so updates cannot be lost. The split and application lifecycle gate
are implemented; callback-safe concurrent behavior remains an evidence claim,
not an implementation gap. Portable unwind and barrier-controlled native thread
evidence remain release-blocking; sequential or static token accounting is not
concurrency evidence.

### 31.1 Implementation checkpoint

The stable context class, context-owned dispatcher, typed v2 producer, exact
argument/slot/phase validator, hosted-CPU-entry-closure surface gate, ordinary
unit-call rewrite, slot/phase coverage proof, and residual v1/v2 backend
rejection now exist. The source-owned
`prepared_advice_dispatch_context_invoke_or_panic` wrapper first runs the
Result dispatcher, which stores cleanup state, and only then invokes canonical
panic on failure. This preserves arbitrary business return values and ensures
failure never continues the join point or strands a generation token.

The compiler also now has genuine
`context.try_facet<T>(base)`/`facet<T>`/`require_facet<T>` parser, AST, and HIR
nodes plus a typed adapter plan that retains the concrete base,
validates the entire resolved descriptor, selects by contract member, lowers
through base-first `CallIndirect`, rejects erased bases, and diagnoses every
currently wired affine escape category by HIR symbol identity. The application
exposes context-first whole-descriptor acquisition/release with validation and
failure cleanup. The current continuation wires exact nominal context/contract
proof, canonical method ordinal/signature resolution, HIR-symbol lambda/async
capture checks, and typed-base indirect dispatch through an opaque lease and
context-first checked method accessor. The compiler now preserves the three
documented wrapper shapes, installs adapters only for successful acquisition,
and emits reverse-order release for fallthrough, return, `?`, loop transfer,
and explicit/generated panic paths. Lazy pack loading is now connected through
an injected application-owned exact-route I/O port: `try_facet` retains the
no-I/O published-binding probe, while `facet` and `require_facet` resolve a
catalogued `lazy_facet` route and return canonical `std.aop.FacetAcquireError`.
`AspectPackIoPort` is the canonical injection contract.
`aspect_pack_io_port_for_embedding` validates the embedding owner and
`AspectExecutionContext.create_with_loader_and_pack_io` is the canonical
composition point; default construction remains fail-closed. The repository
does not supply a universal deployed-image adapter: each embedding still binds
its deployed-image and detached-signature storage policy through the exact-route
callback, and no guessed sidecar convention is permitted.
Generated MIR carries leases only as the compiler-private opaque
`__simple_facet_descriptor_lease_abi` type. The startup implementation still
exports `PublishedFacetDescriptorLease` from its owner leaf, although the
top-level startup facade no longer re-exports it. Simple supports private and
`pub(peer)` visibility, but narrowing only the class is unsafe while public
runtime functions expose it in their signatures. Removing the leaf export
requires a separate opaque-handle runtime facade migration and no compiler ABI
change. Lazy-acquire callers now use a Mutex/channel single-flight: one owner
performs I/O/activation and same-route followers receive the shared typed
completion. The application lifecycle gate now serializes prepared-advice
prepare/finalize, facet lease/descriptor/method operations, activation commits,
and retryable unload/quiesce transitions. Lazy preflight/reservation and
commit/revalidation are separate gated phases around exact-route pack I/O;
native advice invocation runs outside the gate. The current single-flight owner
permits only one active flight per context, so different routes are globally
serialized. Synchronous same-route port-callback re-entry is prohibited and
would wait on itself; no canonical task/thread identity exists to reject it
deterministically.

Construction, `enter_operational`, and configuration mutation (including
loader and pack-I/O installation) remain startup-only operations outside the
lifecycle gate, and policy/catalog reads assume immutable post-construction
state. Native callback panic remains process fail-stop, not a recoverable unwind
path.

The compiler now has an explicit required `MirCallUnwindContract` on
`CallTerminator`, a validator/canonical constructor for the exact
`NoUnwind`/no-edge and `MayUnwind`/edge pairs, JSON serialization, and exact
preservation through the owned borrow and MIR optimizer paths. The interpreter
consumes the contract, textual LLVM emits `invoke` for `MayUnwind`, and native
or otherwise unsupported backends reject it rather than silently emitting a
plain call. The LLVM C-API backend remains fail-closed because it has no invoke
binding. Generic indirect calls with unknown effects under a live facet lease
now fail with E-AF007.

The typed source/HIR effect owner and fail-closed bridge are now implemented.
Every function has exactly one unwind effect: `@no_unwind` is the default,
`@may_unwind` is explicit, extern alone does not imply unwind, and `Async` is
preserved independently. Callable declarations, imports, function types, and
resolved instance/static/trait/free calls retain the effect. MIR admits an
ordinary call only for `NoUnwind`; `MayUnwind` without a real cleanup successor
and missing/conflicting metadata fail with E-MIR-UNWIND001. A live facet lease
retains E-AF007 precedence for the same unsupported call.

The remaining gap is not effect identity: MIR still lacks the cleanup-successor
producer, throw/resume cleanup pads, and async cancellation cleanup. LLVM C-API
invoke binding and executable verification are also open. Those gaps continue
to prevent portable callee/foreign unwind claims. Broader lifecycle concurrency is therefore implemented but remains
unproven until barrier-controlled threaded evidence passes. Portable
callee/foreign unwind, deployment-specific I/O binding, opaque runtime lease
facade migration, and executable evidence also remain open. `throw`, `await`, `yield`,
unsupported `MayUnwind`/unknown calls, and `throw`/`await`/`yield` fail closed
with E-AF007 while a lease may be live.

#### Typed landing-pad payload and cleanup CFG

The cleanup successor must carry an implementation exception token, not a
source-language thrown value. The canonical core extension is
`MirTypeKind.ExceptionToken` plus
`MirInstKind.LandingPad(dest: LocalId)`. `LandingPad` defines the token as the
first non-phi instruction of an unwind-only block; `MirTerminator.Resume` must
consume an operand of that type. The token is compiler-private, linear across
cleanup-only CFG, and unavailable to ordinary calls, returns, aggregates, or
user storage.

The exact construction API is `MirBuilder.emit_landing_pad() -> LocalId`,
`MirBuilder.terminate_resume(token)`, and
`validate_mir_exception_cfg(body) -> Result<(), text>`. Facet lowering exposes
`emit_facet_unwind_cleanup_successor(first_scope: i64) -> BlockId`; it snapshots
the selected entries, emits the unwind path, restores the current normal block,
and leaves `facet_cleanup_scopes` unchanged. There is no `CatchException` in
this cleanup-only phase because decoding/handling the language payload depends
on the still-missing runtime exception-packet ABI.

A typed `MayUnwind` call lowers to a `CallTerminator` whose unwind successor
starts with `LandingPad`, releases every live facet descriptor exactly once in
reverse scope/acquisition order, and terminates in `Resume(move token)`. Guarded
releases may branch after the landing pad, provided the token dominates both
paths and they converge on one Resume. The normal successor retains the cleanup
scope metadata and releases only at its ordinary lexical exits; constructing
the unwind path never consumes normal-path ownership.

MIR validation owns unwind-only predecessor checks, first-instruction placement,
one-definition/one-resume token linearity, and rejection of cleanup fallthrough.
Borrow checking treats the token as compiler-owned/non-borrowable. SSA and copy
propagation may rename it without duplication; DCE, LICM, outlining, and CFG
rewrites preserve the invoke edge, landing pad, cleanup calls, and resume.

For the textual LLVM implementation, `ExceptionToken` maps to `{ptr, i32}`, the
pad emits `landingpad {ptr, i32} cleanup`, and Resume emits the same aggregate.
This is enabled only when the function declares the single runtime-owned
personality selected by the exception ABI. The repository currently has no such
personality or source-value-to-runtime-exception packet owner, and its MIR
interpreter stores scalar `i64` values only. Therefore no backend may map the
token to `ptr`, zero, nil, abort, return, or a normal branch as a placeholder;
unsupported consumers retain E-MIR-UNWIND002, while lowering retains
E-MIR-UNWIND001 until the complete cleanup successor can be constructed.
