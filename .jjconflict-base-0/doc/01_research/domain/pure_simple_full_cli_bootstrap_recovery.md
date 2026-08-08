# Pure-Simple full CLI bootstrap recovery — domain notes

Date: 2026-07-17

This failure is repository-specific; no external dependency selection is
needed. The applicable build-system principles are:

- a temporary directory's owner must retain its lifetime through link/archive;
- staging must not live inside a subtree that another allowed operation
  recursively deletes;
- concurrent writers use unique staging directories and never share a cache
  write target without an ownership contract;
- a clean operation may remove cache data, but not another build's live inputs;
- code generators fail closed on unresolved symbols instead of inventing data
  globals or placeholder operations.

The selected sibling-staging design follows those constraints while retaining
the existing on-disk object flow and bounded memory behavior.
