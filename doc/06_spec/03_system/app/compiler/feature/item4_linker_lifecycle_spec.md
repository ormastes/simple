# Linker lifecycle callbacks and pack refusal

Requirement: ITEM4-REQ-010. **UNRUN — authored manual, not canonical docgen.**
Executable: `test/03_system/app/compiler/feature/item4_linker_lifecycle_spec.spl`.

- Pin a real static ELF callback, refuse an unauthorized pack path, and verify
  the active generation and real static linking remain intact.
- Refuse malformed ABI digests, denied capabilities and host ABI disagreement
  before mapping. A rejected owner cannot invoke and closes idempotently.
- Exhaust generation slots and execute independent static recovery, preserving
  both real ELF success and a real unresolved-input failure.
- Replace a provider while an old session stays pinned; each operation keeps its
  original entrypoint semantics. Collection waits for release.
- Reject incompatible provider schemas without changing the active generation.
- Reject stale session handles after close and slot reuse.
- Reject configured jobs and configured recovery through legacy-only callbacks,
  retaining session cleanup rather than dropping explicit native options.

The callback scenarios use actual linker calls. Native loading is covered by the
separate native pack spec; no callback success substitutes for its execution.
