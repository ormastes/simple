<!-- codex-architecture -->

# Architecture: Minimal-Bootstrap Configuration-Composed Dynamic Architecture

## Status

Accepted direction; incremental implementation. This document fixes ownership and contracts for the first application-catalog and leaf-CLI slices without claiming that all later compiler/provider waves already exist.

## Decision

Simple is composed from three layers:

1. `simple-core`, a stable statically linked nucleus;
2. `SimpleCompositionImageV1`, one immutable validated data image;
3. independently built providers queried through `SimpleProviderQueryV1`.

Configuration is data, never executable code. `SimpleArtifactManifest` remains the launch/security authority for an artifact; SCI owns composition and generates its launch-policy projection. Full bootstrap is a named compatibility/trust target, not a source-path heuristic.

## Context and current owners

Current composition is distributed across `src/os/services/launcher/launcher.spl`, `src/os/desktop/app_manifest.spl`, `src/os/kernel/loader/disk_launch_manifest.spl`, `src/os/smf/dynsmf_session.spl`, root CLI imports, and startup adapters. `src/os/kernel/loader/artifact_manifest.spl` already declares one unified artifact policy surface. `src/compiler/35.semantics/interface/compile_interface.spl` supplies one required identity, while the scheduler still needs authoritative typed-edge use.

## Layer and ownership model

```text
SDN sources + overlays
        |
        v
simple-configc ---- build graph / artifact lock
        |
        v
SimpleCompositionImageV1 (.sci, immutable)
        |
        v
simple-core -- SimpleProviderQueryV1 --> provider generations
        |             |                     |
        |             +-- SimpleCliCommandV1
        +---------------- SimpleAppLaunchV1
```

| Owner | Owns | Must not own |
|---|---|---|
| composition schema/common layer | wire structs, IDs, canonical encoder, validation status | provider implementation or launcher process state |
| `simple-configc` | text parsing, overlays, validation, artifact locking, SCI write/read-back | provider compilation or compiler driver import |
| SCI reader/core | bounds/hash/signature validation, indexed views, provider selection | SDN parsing, directory scans, startup compilation |
| provider loader | native/SMF mapping, query, generation pinning, rollback | interface-specific business behavior |
| launcher adapter | app indexes and lifecycle state from SCI records | a second built-in app catalog |
| CLI registry | recovery commands and SCI summary lookup | static imports of ordinary command bodies |
| build graph | typed dependencies, compatibility, actions/CAS, explain receipt | path-only bootstrap escalation |

This is an Adapter architecture with a composition virtual capsule spanning build, startup, loader, CLI, and launcher concerns. Cross-cutting integrity/capability checks remain at the core/provider boundary rather than being duplicated inside product providers.

## `SimpleCompositionImageV1`

The header contains magic, format version, byte order, total length, section-directory bounds, schema digest, and composition digest. Directory entries contain type, version, required/optional flags, offset, length, and content digest. V1 sections cover strings, interfaces/groups, providers, imports/exports, bindings, commands, apps, associations, launch policy, build targets/edges, generated ownership, provenance, signatures, and typed extensions.

All values use fixed widths; references are offsets or indices, never pointers. Canonical sorting occurs after overlay resolution. Readers validate integer arithmetic, directory overlap, bounds, hashes, identities, uniqueness, bindings, paths, capabilities, and required interfaces before publishing a read-only view. Unknown required sections fail; unknown optional extensions skip safely.

Independent section digests define narrow `ConfigProjectionDigest` values, so changing app display text does not perturb interface schemas or unrelated command projections.

## Provider contract

`SimpleProviderQueryV1` is the sole discovery entry across native and SMF loaders. The request contains interface ID, minimum major/minor, host ABI, target identity, and requested capabilities. The result contains status, provided version, descriptor size/table, opaque provider context, provider identity, implementation digest, and ABI digest.

`SimpleCliCommandV1` owns `describe`, `validate_args`, `run`, and `complete` operations at command granularity. `SimpleAppLaunchV1` owns launch request/result at application granularity. Neither exposes language-native objects. Optional capabilities are separate queried interfaces or known descriptor prefixes. A breaking ownership/layout/calling/error change creates a new major.

The loader verifies the locked artifact digest/signature and capability ceiling before query, proves that a resolved entry is process-callable, queries a stable interface set, then atomically publishes a generation. Handles pin that generation; unload waits for the pin count to reach zero. Query crash/error leaves the old generation active and returns a typed diagnostic.

## One-manifest projection

SCI owns configuration identities and bindings. At admission, its app/provider launch-policy record is projected into `SimpleArtifactManifest` validation rather than checked by a competing policy object. Existing launch metadata/trailers remain serialized projections where required. During migration, old catalogs may be read only through an explicit compatibility importer; they cannot override SCI fields silently.

## Build, cache, and invalidation

The graph uses typed implementation, compile-interface, ABI, compile-semantic, tool, link, runtime, configuration, generated, resolution, and AOP-selection edges. Each edge selects its relevant digest. Recompute marks a node green when that digest is unchanged and stops propagation on that edge.

Action keys contain only declared tool, source, configuration projection, target, profile, runtime ABI, allowed environment, and output-schema identities. Action-result metadata points to immutable CAS artifacts. Schema/cache changes create namespaces; they do not clear global caches.

Build and bind are separate actions: provider targets produce artifacts; config targets lock their exact identities into SCI. Missing runtime artifacts fail with `ProviderArtifactMissing`; runtime never shells out to compile.

## Bootstrap decision

`build-explain` returns `Exact`, `Compatible`, `Unknown`, or `Incompatible`, the selected closure, digest deltas, reuse counts, and a typed bootstrap reason. `Unknown` never authorizes reuse. Only seed failure/unsupported target, required bootstrap language/runtime/artifact/core incompatibility, or explicit convergence/trust/DDC targets can select full bootstrap. Normal feature targets have no dependency on convergence or DDC.

## Startup and hot paths

Core startup maps/reads one SCI, validates it once, constructs section indexes once, and resolves command/app records by indexed identity. `--help` uses SCI summary metadata and does not load providers. Dispatch performs one binding lookup, artifact admission, generation lookup/query when not already active, and one coarse operation call. No hot path scans the repository, rereads text config, merges overlays, or spawns build subprocesses.

NFR-005 through NFR-007 use structural budgets: modules parsed/typed/lowered,
objects generated, providers packaged, links performed, SCI sections
regenerated, and cache hits/misses. Timing and RSS remain host-labeled
observations. No bootstrap edge may be scheduled until its typed reason receipt
exists. CLI-0/1/2 identify static/essential/extended command surfaces;
B1/B2/B3 identify seed/bootstrap/self-host producers; P0/P1/P2/R0 identify
core/essential/optional/release products.

Architecture evolves in this order: P0 cheap decisions, P1 core extraction, P2
CLI configuration, P3 essential provider, P4 leaf providers, P5 per-module
cache, P6 compiler engine provider, P7 full product composition, and P8 release
bootstrap. No later phase may weaken the earlier classifier/reason receipts.

## Failure and recovery

- Invalid SCI: reject before exposing partial indexes; retain the last admitted image where policy permits.
- Missing/incompatible provider: return typed status and build-explain hint; do not compile.
- Capability/path/signature failure: reject before mapping/query.
- Provider query failure: preserve prior active generation.
- Unknown build compatibility: rebuild the smallest producer/stage.
- Corrupt/missing admitted bootstrap producer: escalate using a typed reason.

Static recovery commands (`help`, `version`, `config verify`, `provider inspect`, build/bootstrap delegation) remain usable without ordinary providers.

## Compiler evolution

The first compiler boundary is coarse `CompilerDriverV1` with opaque session/source/diagnostic/artifact handles. AST/HIR/MIR remain private. Backend/link providers follow only after a versioned capsule exists. Fine-grained compiler-internal plugins remain version-pinned experiments.

## Security invariants

- configuration load executes no code;
- every artifact is identity-locked before activation;
- providers receive only declared host interfaces/capabilities;
- paths are normalized and constrained;
- required unknowns fail closed;
- process-callable proof precedes invocation;
- activation is atomic and generations are pinned.

## Consequences

Positive: app and command composition becomes data-only; private provider changes are contained; rebuild decisions become explainable; release trust remains explicit. Negative: new wire/ABI compatibility obligations, loader-generation machinery, and measurement infrastructure are required. The design deliberately delays fine compiler decomposition to avoid freezing unstable IR.

## Verification boundary

System scenarios use `compile_composition`, `load_unchanged_core`, `dispatch_provider`, and `explain_rebuild`. Integrity and compatibility matrices are focused pure-Simple checks. Platform-specific native/SMF parity requires separate evidence and cannot be inferred from host success.

## References

- `doc/01_research/local/minimal_bootstrap_configuration_composed_dynamic_architecture.md`
- `doc/01_research/domain/minimal_bootstrap_configuration_composed_dynamic_architecture.md`
- `doc/04_architecture/compiler/bootstrap_build_modes.md`
- `src/os/kernel/loader/artifact_manifest.spl`
- `src/compiler/35.semantics/interface/compile_interface.spl`
