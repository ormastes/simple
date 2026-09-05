# Link Manager Plan (LINK lane — GraphResolveCore, SMF linker, StyleLinker)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** architecture doc Part VII (§18–§19) and §29 Wave 7.

## Scope

- **GraphResolveCore:** definitions/references/resolution records,
  hash/intern, stable sort/group, deterministic group reduction, reachability
  frontiers, constraint propagation, scan-based placement, patch emission,
  receipts.
- **Profiles** (share primitives, never semantics):
  - `SmfLinkProfile` — the L0–L12 pipeline (decode → resolve → archive
    fixpoint → reachability → address layout → relocation → output →
    provenance → staged/direct SSD write → manifest commit);
  - `ClangOffloadLinkProfile` — host/device images, offload sections,
    registration records;
  - `WebResourceLinkProfile` / StyleLinker — stylesheet imports,
    custom-property graph, fonts, keyframes, resources.
- Linker tags (`link.*`) and profile-driven section ordering as MutationIR
  with new address mappings + relocation/debug invalidation.

Spatial layout is **not** a profile here. Native ELF/Mach-O/PE stays on
established native linkers (mold does not emit SMF); the GPU linker is
SMF-first.

## Owned paths

```text
src/lib/common/structural/resolve/          # GraphResolveCore + profile API
src/compiler/70.backend/linker/gpu_smf/
test/01_unit/lib/structural/resolve/
test/01_unit/compiler/linker/gpu_smf/
```

## Dependencies

- Frozen contracts: ResolveProfile, MutationIR, StageReceipt, placement hints.
- gpu_mmu for resident symbol/relocation/output arenas (resident tier only).
- html_css_parser lane consumes StyleLinker output (`StyleLinkResult`).

## Phases

1. **CPU core (Wave 1).** GraphResolveCore + SmfLinkProfile over canonical
   arenas; byte-identical output to the current SMF linker + receipts.
2. **StyleLinker (Wave 6/7).** WebResourceLinkProfile; custom-property
   dependency graph with cycle detection.
3. **Hybrid SMF (Wave 7).** GPU hash/sort/resolve/reachability/scan/relocation
   batches; CPU decode/control.
4. **Resident SMF (Wave 9).** Objects/symbols/relocations/output chunks stay
   in Object VM; compact host commit; staged/direct SSD output.
5. **ClangOffloadLinkProfile** after clang_bridge C1 lands.

## Acceptance

- Deterministic output bytes; CPU/hybrid/resident parity by hash.
- Malformed SMF bounds/overflow rejected; duplicate-symbol diagnostics in
  stable order.
- Reachability/dead-strip and relocation formula fixtures pass.
- Input entity → output byte-range provenance queryable via MappingGraph.
- Web resolution parity: StyleLinker output equals current resolver for the
  browser corpus.
