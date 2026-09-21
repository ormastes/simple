# Module Surface Export Provenance Requirements

**Selection:** robust infrastructure with an immediate safe provenance slice.

- **REQ-001:** Every re-exported name resolved through a `ModuleSurface` shall
  identify its canonical declaring surface and original declaration name.
- **REQ-002:** Logical aliases of one physical file shall coalesce to one owner;
  aliases shall never manufacture duplicate declarations.
- **REQ-003:** Named, aliased, glob, relative, package-`__init__`, and multi-hop
  re-exports shall use one provenance resolution contract.
- **REQ-004:** Cycles, missing sources, and competing physical owners shall fail
  deterministically with facade, exported name, and candidate-owner context.
- **REQ-005:** Direct declarations remain in existing dictionaries. The new map
  stores only re-export provenance and shall not copy bodies or declarations.
- **REQ-006:** Explicit and glob import registration shall consume the same
  provenance result. The legacy chase may remain only as a temporary diagnostic
  fallback with observable fallback counts.
- **REQ-007:** Streaming and retained surface construction paths shall finalize
  provenance after all aliases have been registered and before HIR consumers run.
- **REQ-008:** Existing import spellings and visibility behavior remain compatible.
- **REQ-009:** The design shall reserve a phased path to a
  `ResolvedModuleGraph` owning canonical nodes, typed import/export edges, and
  symbol-body closure without requiring that larger migration now.
- **REQ-HIR-CACHE-SCOPE-001:** Resolution facts retained across streaming HIR
  modules shall remain live after each transient scope ends, including newly
  appended cache payloads. Importer-local enum owner rows shall be cleared for
  the next module. Native scope tests and the three-module
  `test/fixtures/hir_resolution_cache_scope` fixture cover this correction;
  current verification scope is macOS arm64.
- **REQ-EXPORT-SCRATCH-001:** Streaming export-origin resolution shall reclaim
  temporary lookup and import-walk graphs after each surface, retain origin
  arrays and projections across fixpoint passes, and preserve errors after
  cleanup. The canonical macOS Stage 3 compile at jobs=8 must peak below
  1,000,000,000 bytes RSS for the compiler process; a smaller fixture does not
  establish that full-closure memory requirement.
