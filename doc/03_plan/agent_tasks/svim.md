# svim Agent Task Breakdown

1. Complete shared-core modal grammar, search repeat, text-object editing, quickfix traversal, and deterministic visual edit behavior.
2. Keep the host shell thin while adding line-shell UX for multi-file sessions, open/save/search prompts, and command batching.
3. Add a SimpleOS-facing adapter shim that reuses `SvimSession` instead of duplicating edit logic.
4. Add a language bridge that converts parser diagnostics into shared buffer diagnostics and quickfix entries.
5. Run targeted `svim` tests and host-shell verification; track the remaining native spec-wrapper limitation separately from shared-core behavior.
