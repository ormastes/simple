<!-- codex-research -->

# Simple Minimal-Bootstrap, Configuration-Composed Dynamic Architecture

> Status: user-supplied research captured on 2026-08-14. Repository observations and implementation status must be re-verified before design or implementation.

## Executive decision

The intended end state is a three-layer system, not a fully dynamic Simple distribution:

1. **`simple-core`** — a small, stable, statically linked executable containing the composition-image reader, provider loader/query ABI, basic diagnostics, security and capability enforcement, and recovery commands.
2. **Simple Composition Image (`.sci`)** — one validated immutable binary containing application registration, CLI commands, provider bindings, interface groups, build targets, file associations, capabilities, and exact artifact identities.
3. **Provider artifacts** — independently built `.smf`, `.so`, `.dylib`, or `.dll` files implementing stable, explicitly versioned interface groups.

The expected containment properties are:

- Application-list changes rebuild only the SCI.
- CLI implementation changes rebuild only that provider and the SCI containing its new digest.
- Compiler implementation changes with unchanged interfaces rebuild only that provider and outputs whose tool-behavior dependency changed.
- Interface-group changes rebuild only consumers of that group.
- Full self-host bootstrap remains an explicit release/trust operation.

## Current repository assessment

### Existing foundations

The repository already has useful but disconnected pieces:

- `dynload` as the default bootstrap mode, with `one-binary` retained explicitly.
- ELF/SMF/PE dynamic-library abstraction and checked dynSMF loading.
- Launch metadata serializable into an SMF section or native trailer.
- A unified `SimpleArtifactManifest` whose design prohibits a second manifest.
- Typed compiler pipeline-port concepts.
- DI runtime slots with declared-slot validation and deterministic provider ordering.
- Four interface-compatibility digests.
- Named-target and minimal-bootstrap planning.
- A target-graph implementation reported complete in another worktree but not landed on main.

### Sources of broad rebuilding

| Area | Current condition | Consequence |
|---|---|---|
| Bootstrap policy | Compiler-path changes are escalated too readily to T3/full bootstrap | Private implementation edits trigger excessive work |
| Pure-Simple native cache | Scope includes the entire loaded source closure | A leaf edit can behave like a cold build |
| Interface compatibility | Four digests are computed/logged but do not drive reuse | Dependents rebuild without compatibility proof |
| Target graph | Typed target/edge IR is not authoritative on main | No authoritative minimal scheduler |
| Bootstrap CLI | Direct concrete compiler-driver import | Bootstrap inherits the driver closure |
| Main CLI | Most commands are statically imported | Unrelated product changes broaden the CLI closure |
| Launcher | Apps, aliases, shortcuts, and associations are source constants | Catalog edits recompile launcher code |
| Desktop app catalog | A second built-in manifest exists | Duplicate sources of truth |
| Disk launch mapping | Baremetal aliases form another hard-coded table | Packaged-app edits touch loader-adjacent code |
| dynSMF | Provider entries and source mappings are embedded in code | Adding a provider changes infrastructure |
| Compiler services | In-process `any` callables and no-op defaults | Not a stable cross-binary ABI |
| SMF metadata | Rust and Simple reportedly disagree on header layout | Metadata cannot safely be authoritative |

### Hard-coded composition points

The reported duplication spans launcher initialization/registry state, desktop app manifests, baremetal FAT32 mappings, root CLI imports, dynSMF provider/source maps, and the bootstrap compiler-driver import. These should become projections of one composition source rather than parallel registries.

## Recommended architecture

Text SDN configuration (`apps.sdn`, `cli.sdn`, `compiler.sdn`) is parsed, validated, normalized, and bound by a separately buildable `simple-configc`. It emits `default.sci`. Both host `simple-core` and SimpleOS core read this image and load the selected compiler, CLI, and application providers.

### `simple-core`

The stable nucleus should contain only:

- Minimal argument parsing.
- SCI reading and validation.
- Native and SMF provider loading.
- Provider query ABI.
- Artifact hash/signature validation.
- Capability/path-policy enforcement.
- Stable host-service tables.
- Basic diagnostics and `doctor`.
- Minimal recovery commands (`help`, `version`, config/provider inspection, and build/bootstrap delegation).
- Optionally, a statically linked emergency compiler provider limited to the bootstrap subset.

It should not statically import the full compiler driver, ordinary developer tools, IDE/office/browser/UI products, OS-management commands, optional backends, the package manager, or the application catalog.

### Simple Composition Image

Canonical identity:

- Name: Simple Composition Image
- Extension: `.sci`
- Magic: `SCI\0`

SCI is an immutable data image, not a shared library. It may be embedded in an SMF section or native resource, but configuration must not execute constructors or acquire a platform-specific code-loader ABI.

SCI must be a superset/projection source for existing launch metadata and `SimpleArtifactManifest`, not a rival manifest.

#### Proposed v1 sections

Header; section directory; string table; interface schema and group tables; provider table; imports/exports; bindings; CLI commands; app catalog; associations; launch policy; build targets; typed dependency edges; generated-file ownership; provenance; signatures; and skippable versioned extensions.

Use offsets/indices rather than serialized pointers, fixed-width integers, canonical ordering, independent section digests, and explicit required-versus-optional extension semantics.

### Configuration compiler

`simple-configc` must not import `compiler.driver`. Its closure is restricted to low-level I/O, SDN parsing, validation, canonical serialization, hashing/signatures, SCI writing, and diagnostics.

Required pipeline:

`SDN -> CompositionIr -> validation -> normalization -> overlay resolution -> interface/provider resolution -> binding/capability/target validation -> artifact locking -> canonical ordering -> SCI write -> read-back verification -> signature`

Provider building and composition binding remain distinct actions. Runtime startup must not shell out to compile missing providers; it fails closed with a typed missing-artifact diagnostic.

## Stable provider and interface contracts

Every provider exposes one discovery entry, conceptually:

```c
int32_t simple_provider_query_v1(
    const SimpleInterfaceRequestV1* request,
    SimpleInterfaceResultV1* result
);
```

Requests identify interface/version, host ABI, target, and requested capabilities. Results report status, provided version, descriptor size/table, provider context/identity, and implementation/ABI digests.

Cross-provider ABI must exclude `any`, Simple object layouts, mutable compiler IR structs, native text/generic collections, exceptions/unwinding, implicit allocator ownership, and compiler-internal enum layouts. It may use fixed-width scalars, opaque handles, explicit views/buffers, host allocators, versioned POD descriptors, and stable status codes.

Each interface has an ID, major/minor version, descriptor size, and ABI digest. Compatible minor additions use known descriptor prefixes or separately queried extension interfaces. Ownership, calling convention, layout, required-operation, or error-semantic changes require a new major.

Recommended groups include host services, CLI commands, application lifecycle/actions, public compiler operations, compiler backend/link capabilities, build graph/action/cache/explain, and configuration validation/extensions. SCI binds named groups to concrete providers.

## Compiler decomposition

Decompose in stages to avoid freezing unstable internal representations:

1. **Coarse `CompilerDriverV1`:** opaque sessions, source sets, diagnostic sets, compile requests, and artifact descriptors; AST/HIR/MIR remain internal.
2. **Backend/link providers:** exchange a versioned serialized capsule or provider-owned opaque handle, not in-memory MIR objects.
3. **Stable extension seams:** lint/format rules, diagnostics, source transforms, target descriptions, linker adapters, artifact processors, static analysis, and AOP policy.
4. **Optional stable IR services:** initially read-only; mutation is transactional and validated.

Raw parser/HIR/MIR mutation plugins remain compiler-version-pinned experiments until stable serialization and compatibility rules exist.

## Configuration-driven launcher and CLI

Consolidate launcher seed data, aliases, shortcuts, associations, desktop manifests, and disk mappings into one SCI app catalog. The launcher retains process state and IPC, but loads immutable app records and builds indexes once. Display-name, icon, shortcut, association, and policy changes become SCI-only changes.

The root CLI becomes a small SCI command registry. Only recovery commands remain static. Migrate formatter/linter/fixer/TODO first, then statistics/docs/test tooling, UI/office/IDE, browser/dev-hub/OS, and finally compiler commands after `CompilerDriverV1`. SCI carries summary help/completion metadata so common help does not load providers.

## Build graph and invalidation

Preserve and activate:

- `ImplementationDigest`
- `CompileInterfaceDigest`
- `AbiInterfaceDigest`
- `CompileSemanticDigest`

Add link-export, runtime-contract, configuration-projection, and tool-behavior digests.

Edges must be typed: implementation, compile-interface, ABI, semantic, link, runtime, tool, generated, configuration, resolution, and AOP selection.

Use red/green propagation: recompute the relevant identity and stop propagation when it is unchanged. Action keys include only declared tool/source/config/target/profile/runtime/environment/schema inputs. Store action metadata separately from immutable content-addressed artifact bytes. Cache-format changes create namespaces; they do not clear global caches.

## Bootstrap policy

Full bootstrap is allowed only for typed reasons such as missing/corrupt/unsupported seed, required language-feature incompatibility, bootstrap runtime or artifact-format major changes, bootstrap-core interface major changes, explicit self-host convergence, release trust verification, or diverse double compilation.

App/catalog/CLI/provider-private/backend-private/docs/test/config/cache-miss changes are not full-bootstrap reasons.

Compiler changes are classified by contract impact rather than path:

| Change | Required action |
|---|---|
| Provider body/private helper | Rebuild provider and outputs whose tool behavior changed |
| Public compile interface | Rebuild direct compile-interface consumers |
| Cross-binary ABI | Rebuild ABI consumers; bind a new major when incompatible |
| Bootstrap language/runtime dependency | Rebuild the smallest incompatible bootstrap stage |

Bootstrap and release checks become named targets. `build-explain` reports admitted compiler identity, required features/ABI/formats, compatibility (`Exact`, `Compatible`, `Unknown`, `Incompatible`), selected closure, and typed bootstrap reason. `Unknown` may rebuild but never authorizes reuse.

## SMF prerequisites

Before authoritative SCI/provider metadata:

1. Specify the SMF wire layout independently of language structs.
2. Encode/decode integers by explicit offsets.
3. Add versioned dual readers and strict malformed-input rejection.
4. Stop raw struct-memory serialization.
5. Put extensible metadata in versioned TLV sections.
6. Add Rust-writer/Simple-reader and Simple-writer/Rust-reader tests.
7. Migrate caches by namespace.

Provider activation must preserve fail-closed proof that resolved code is process-callable. Stabilize the shared contract first with host native libraries, then implement identical query semantics for SMF; do not create separate native and SMF provider APIs.

## Implementation waves

1. Inventory composition points, repair SMF layout, recover target IR, define one-manifest ownership, and baseline closures/bootstrap reasons.
2. Freeze SCI/provider contracts; implement composition schema, parser repairs, compiler, readers, code generation, and overlays.
3. Implement provider ABI, host services, native/SMF loaders, generation pinning/rollback, compatibility, and security.
4. Prove launcher/app catalog and leaf CLI migrations.
5. Introduce coarse compiler driver, opaque handles, backend/link providers, emergency provider, and performance evidence.
6. Wire compatibility digests, consumer assumptions, red/green scheduling, CAS, linking, AOP, and resolution edges.
7. Convert bootstrap into named graph targets with typed reasons, stage-local rebuilding, convergence, DDC, and explain evidence.
8. Update policy, skills, CI mutation matrices, and documentation.

The first three milestones are:

1. Edit an SDN app record, rebuild one SCI, and observe the changed catalog through unchanged `simple-core`.
2. Edit the formatter, rebuild only its provider and SCI digest projection, and run it through unchanged root CLI.
3. Load the compiler through `CompilerDriverV1`, removing the concrete driver import from the bootstrap executable.

## Acceptance and verification

The required mutation matrix proves SCI-only catalog edits; provider-only private changes; compatibility-scoped interface/ABI/semantic rebuilds; backend/frontend separation; and explicit bootstrap reasons.

Non-negotiable tests cover:

- Body/private/public/ABI/semantic digest propagation.
- Old/new host-provider compatibility, descriptor bounds, duplicate/unstable interfaces, pinned unload, and query failure.
- Deterministic SCI output, bounds/overlap/hash/signature validation, binding/slot/path/interface validation, and optional-provider policy.
- Zero bootstrap targets for app/CLI mutations, no `simple-core` rebuild for compiler-private changes, backend/frontend containment, and explicit convergence targets.

## Principal risks

- **Premature ABI freeze:** mitigate with coarse opaque driver boundaries.
- **Dynamic-call overhead:** cross boundaries at compilation-unit or pipeline-stage granularity.
- **Config compiler monolith:** keep it independent and keep the binary reader smaller than the text compiler.
- **Incomplete SMF executable loading:** validate the ABI first with native libraries while retaining identical SMF semantics.
- **Provider security:** require declared imports, capabilities, paths, and bindings; prohibit ambient discovery/access.
- **Hidden AOP/generated dependencies:** model them as explicit typed edges with conservative digests.
- **False compatibility:** only proven `Exact`/`Compatible` results permit reuse; `Unknown` rebuilds.

## Recommended critical path

1. Repair SMF wire-format divergence.
2. Land named-target/typed-edge IR.
3. Freeze SCI and provider-query ABI v1.
4. Implement low-dependency `simple-configc` and SCI readers.
5. Migrate app catalog, then leaf CLI tools.
6. Introduce `CompilerDriverV1` and remove the bootstrap driver import.
7. Make compatibility identities normative build inputs.
8. Replace path-based bootstrap escalation with typed reasons.
9. Split backend/link providers.
10. Keep convergence and DDC as explicit release targets.

## Research disposition

This document records the submitted architecture research and executive recommendation. It does not select final feature/NFR requirement options and does not authorize implementation. The next research-pipeline step is repository verification plus explicit feature/NFR option documents for user selection.

## Addendum — 2026-08-14: Minimal rebuild and ad-hoc bootstrap speed plan

This addendum makes development selection structural and receipt-driven. Wall
clock and RSS remain useful observations, but heterogeneous hosts make them
unsuitable as the first acceptance oracle. The hard invariant is:

> No bootstrap action may start unless a typed `BootstrapReason` receipt is
> emitted first. A path, cache miss, empty worktree, or desire for confidence is
> not a reason.

### CLI change classifier

- **CLI-0 — static `simple-core`:** only `--help`, `--version`, `config verify`,
  `provider inspect`, and `doctor`. These recovery/inspection commands require
  no ordinary CLI provider.
- **CLI-1 — essential CLI provider:** `run`, `compile`, `native-build`, `build`,
  `check`, `test`, `config`, and `query`. This is the smallest ordinary
  development command surface.
- **CLI-2 — extended providers:** `lint`, `fmt`, `fix`, `duplicate`, spec tools,
  MCP/LSP, stats, SBOM, docs, IDE, Office, UI, browser, and other optional
  products. Each is independently bound and packaged where practical.

Config-zero-code acceptance requires: `modules_parsed=0`, `modules_typed=0`,
`modules_lowered=0`, `objects_generated=0`, `providers_packaged=0`,
`links_performed=0`, `bootstrap_required=false`, and only the declared
`sci_sections_regenerated` count is nonzero. Cache hit/miss counts are still
reported; a cache miss must not broaden the closure.

### Ad-hoc build and producer ladder

The build scope and admitted producer are independent choices:

- **B1 — Rust seed:** bootstrap-only producer. It is never a silent fallback or
  normal development/release evidence source.
- **B2 — pure-Simple bootstrap compiler:** minimal compiler/tool surface built
  by B1 and admitted for its recorded supported commands.
- **B3 — self-host admitted compiler:** pure-Simple compiler admitted through
  the self-host stage; still not automatically the deployed full CLI.
- **P0 — `simple-core`:** stable static recovery/config/provider nucleus.
- **P1 — essential CLI:** provider bundle for CLI-1 commands.
- **P2 — optional providers:** independently composed CLI-2/application/tool
  providers.
- **R0 — release bundle:** explicit assembled release product, including only
  the requested convergence/trust targets.

B2/B3 admission records absolute binary path, hash, stage, provenance,
supported commands, and isolated output/cache. Evidence is stage-labeled and
cannot substitute for deployed P0, general SPipe/docgen/test-runner, release,
convergence/DDC, or cross-host evidence. There is no silent Rust-seed fallback.

### Exact mutation matrix

| Mutation | Class | Initial action | Maximum ordinary closure |
|---|---|---|---|
| App name/icon/shortcut/association | P2 configuration | config validation | SCI catalog/policy sections |
| CLI alias/help summary | CLI-1/CLI-2 configuration | config validation | SCI command section |
| Binding/capability selection | P1/P2 configuration | config validation | affected SCI binding/policy sections |
| Extended provider private body/log text | CLI-2 | focused test | one P2 provider; SCI digest projection if locked |
| Essential command implementation | CLI-1 | focused test | P1 provider and affected products |
| `simple-core` recovery/config logic | CLI-0 | focused core check | P0 only unless its ABI changes |
| Optional interface extension | P1/P2 | compatibility check | provider plus opt-in consumers |
| Compile-interface change | producer contract | digest comparison | direct compile-interface consumers |
| ABI major/layout/ownership change | producer contract | ABI comparison | selected ABI consumers and product link |
| Macro/CTFE/AOP semantics | compiler provider | semantic comparison | semantic consumers |
| Backend optimization | compiler provider | named backend build | outputs with that tool-behavior edge |
| Bootstrap runtime/artifact/core major | B1/B2/B3 | emit typed reason | smallest incompatible stage, possibly R0 |
| Docs/tests only | none | focused doc/test check | no compiled artifact |
| Release convergence/DDC | explicit trust | typed trust reason | R0 named target |

### Cache layers and explain receipt

Cache lookup is layered: normalized configuration projection; source parse;
typed/semantic interface; lowered IR; object; packaged provider; product link;
SCI section; complete immutable artifact/CAS. Every layer has a versioned
namespace and declared key. Missing entries rebuild only that layer; global
cache clearing is prohibited.

Examples:

```text
simple build explain --target //config:default_sci --changed config/apps.sdn
class=P2-config producer=B3 product=P0 bootstrap_required=false
modules parsed/typed/lowered=0/0/0 objects=0 providers=0 links=0
sci_sections_regenerated=1 cache_hits=7 cache_misses=1

simple build explain --target //compiler:formatter_provider --changed formatter.spl
class=CLI-2 producer=B3 product=P2 bootstrap_required=false
modules parsed/typed/lowered=3/3/3 objects=3 providers=1 links=1
sci_sections_regenerated=1 cache_hits=42 cache_misses=5
```

Explain must precede execution and report requested target, classifier,
producer admission, changed digest classes, selected closure, every structural
counter, cache hits/misses, `bootstrap_required`, and typed reason. Unknown
compatibility never permits reuse; it chooses the smallest conservative target
recomputation with an explicitly admitted B2/B3 producer. B1 remains
bootstrap-only.

### Structural budgets

Each target declares upper bounds for modules parsed, typed, and lowered;
objects generated; providers packaged; links performed; SCI sections
regenerated; and cache misses. Tests assert these counts and unchanged artifact
identities. Timing, p50/p95, and max RSS may be recorded with host, OS, CPU,
memory, producer hash/stage, warm/cold state, and sample count, but are
observational until representative baselines justify portable thresholds.

### Normative implementation order

1. **P0 — cheap decisions:** classifier, build-explain, structural counters,
   and typed-reason preflight before execution.
2. **P1 — core extraction:** isolate CLI-0 `simple-core` and its stable reader/
   loader/recovery boundary.
3. **P2 — CLI configuration:** compile command/app/binding metadata into SCI
   with config-zero-code acceptance.
4. **P3 — essential provider:** move CLI-1 into the essential provider bundle.
5. **P4 — leaf providers:** migrate CLI-2 tools/products independently.
6. **P5 — per-module cache:** typed-edge digests, layered CAS, red/green stop,
   and structural cache receipts.
7. **P6 — compiler engine provider:** coarse opaque compiler provider; B2/B3
   admission remains explicit.
8. **P7 — full product composition:** assemble P0+P1+selected P2 artifacts from
   unchanged CAS inputs.
9. **P8 — release bootstrap:** reason-gated bootstrap stages and explicit R0
   convergence/trust/DDC targets.

Required policy: classify first; explain before execute; use the smallest named
target/product closure; preserve exact B2/B3 producer admission; report structural
counters; fail closed on unsupported commands or unknown activation
compatibility; and keep R0 explicit. Prohibited policy: path-based bootstrap,
startup compilation, global cache deletion, silent seed fallback, unscoped
Stage 2/3 evidence, timing-only containment claims, or implicit convergence/DDC.
