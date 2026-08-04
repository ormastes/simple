<!-- codex-research -->
# Local Research: Aspect Facets and Demand-Loaded SFM Packs

## Scope and selected direction

The user selected the referenced aspect/facet design subject to alignment with current Simple design and principles. Current architecture requires the outer deployment artifact to be an SFM capsule and keeps compiled SMF modules opaque. Consequently this lane uses the compatibility name “SMF pack” only for the user-facing feature title; the concrete container is an SFM aspect pack containing indexed SMF payloads.

## Current owners

| Concern | Current owner and reusable contract | Finding |
|---|---|---|
| AOP syntax | `src/compiler/10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl` | Current declarations lower `on pc{...} use ...`; facet grammar does not exist. |
| AOP common contract | `src/compiler/00.common/structural_contracts/aop.spl` | `PointcutQueryRef`, `PointcutSelectorKind`, and `AopRule` are the shared seam to extend. |
| AOP lowering/weaving | `src/compiler/20.hir/hir_definitions.spl`, `src/compiler/50.mir/mir_aop_injection.spl`, `src/compiler/80.driver/driver_pipeline_aop.spl` | Compile-time weaving is authoritative. Runtime facet work must not replace it. |
| Type inventory | `src/compiler/20.hir/hir_types.spl`, `src/compiler/20.hir/hir_lowering/module_surface.spl`, `src/compiler/35.semantics/resolve.spl` | Compile-time types/trait implementations exist, but stable runtime type/interface descriptors do not. |
| Variant overlay | `src/compiler/99.loader/module_resolver/var_resolution.spl` | Variants are resolver/build-time only. Aspect packages may reuse candidate-root logic but runtime cannot reevaluate variants. |
| Feature container | `doc/04_architecture/language/simple_feature_module.md`, `src/lib/nogc_sync_mut/sfm/` | SFM is the pure-Simple feature/capsule container and embeds opaque SMF payloads. |
| SMF format | `doc/04_architecture/format/smf_specification.md`, `src/compiler/80.driver/smf_writer.spl` | Current SMF v0.1 has no production pack directory or independently compressed section contract. |
| Loader byte seam | `src/compiler/99.loader/loader/object_provider.spl`, `src/compiler/70.backend/linker/_SmfReaderMemory/header_parser.spl` | `ObjectProvider.get_module_bytes/get_reader` and `SmfReaderMemory.from_data` are the reusable boundary for SFM-provided SMF bytes. |
| Generation lifecycle | `src/compiler/99.loader/loader/module_loader.spl`, `src/compiler/99.loader/loader/resource_lifecycle.spl`, `src/os/smf/smf_generation.spl` | Existing staged replacement/generation ownership must be generalized; ordinary mapping is not yet atomic for a multi-module aspect transaction. |
| dynSMF policy | `src/os/smf/dynsmf_session.spl`, `src/app/startup/dynsmf_autoload.spl` | Existing manifest, policy, evidence, generation, unload/reload, `--no-dynsmf`, and `SIMPLE_DYNSMF` semantics must be extended rather than duplicated. The manifest size is dynamic and must never be pinned in tests. |
| Compression | `src/lib/common/compress/zstd.spl` | Pure-Simple zstd is reusable, but overlapping dirty edits belong to another lane and are not absorbed here. |

## Design mismatches found

1. The proposal adds `SMF_FLAG_ASPECT_PACK`, `AspectPackDirectory`, and an application-SMF catalog. Current Simple architecture assigns outer feature packaging to SFM; adding a new SMF container path would duplicate ownership and depend on planned SMF format work.
2. The proposal permits arbitrary private-layout inspection/mutation. MDSOC tree privacy requires public contracts or explicit owner-exported capability facades. Private structural access is deferred from v1.
3. The proposal presents type selectors, facet grammar, runtime slots, and hot patching as if implemented. They are proposed and feature-gated; current AOP remains compile-time and supports a narrower selector surface.
4. Runtime catalog/profile wording blurs the variant axis. Variant selection is fully resolved at build time; runtime aspect activation selects only catalogued concrete modules.
5. A new activation manager and registry would duplicate `DynSmfSession`, loader generation, object provider, and cache ownership.
6. Cache design lacks exact keys, invalidation, eviction, negative-cache, and refcount rules.
7. File/process/env access must remain behind the existing owner facades; app leaves may not add raw `rt_*` operations.

## Dependency order

1. Define shared `TypePredicateBytecode` and deterministic `type`/`implements`/`subtype` evaluation against a compile-time descriptor projected from `ModuleSurface`.
2. Add facet AST/HIR/coherence contracts and static `FacetRef<T>` binding without dynamic loading.
3. Publish stable runtime type/interface metadata for open-world registration.
4. Add an SFM v2 aspect-pack manifest/directory with independently framed opaque SMF chunks.
5. Adapt `ObjectProvider` and staged loader publication to byte-backed multi-module activation.
6. Integrate catalog routing and activation policy through `DynSmfSession` and the thin startup adapter.

## Cooperative review

- `design_audit` reviewed architecture and principles.
- `implementation_gap` mapped current source owners and dependencies.
- `spec_and_requirements` audited artifacts and executable evidence.
- Root Codex is merge owner and final reviewer.

