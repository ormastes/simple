# Explicit target loader acceptance

Requirement REQ-GENERIC-CONFIG-TARGET-002, generic formal hardening §6/P4.

Five real SMF header/validator/mmap and metadata-record refusal scenarios. Executable owner: `test/01_unit/compiler/loader/native_target_validation_spec.spl`.

Status: authored manual; compiler/interpreter/native/SSpec/docgen UNRUN. No test fixture or compiler was executed while preparing this packet. Existing modern SSpec runner and spipe-docgen remain required. Tests call real APIs and existing SMF/daemon codecs; no copied success implementation or replacement runner.

Expected behavior: explicit target survives serialization and regeneration; absent target stays unspecified. Target-only drift rejects existing artifact options. A positive header-only mmap fixture checks only the existing options-loading boundary; it does not establish executable mapping or dependency admission. A header without dependency receipts remains rejected by the regeneration validator. Loaded-record fixture uses actual parsed metadata but asserts only refusal before mapping/service creation, not prior executable ownership. Exact-target text alone cannot authorize reuse when mapped target provenance is unavailable.

Full native target feasibility, real watcher/inline compiler regeneration, cold/warm lifetime/concurrency and required core/lib/MCP checks remain separate unrun acceptance gates.
