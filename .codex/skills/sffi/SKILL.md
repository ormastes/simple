---
name: sffi
description: Use or review Simple FFI boundaries, distinguish native Simple counterparts from foreign wrappers, and select pure-Simple database engines before SQLite/PostgreSQL SFFI. Trigger for SFFI, FFI wrappers, native libraries, or database backend selection.
---

# SFFI

Before adding an `extern fn` or foreign-library wrapper:

1. Read `doc/00_llm_process/llm_wiki.md` for repository aliases.
2. Search `src/lib/**` and `src/os/**` for a pure-Simple counterpart using the
   capability name and synonyms.
3. Use SFFI only when the requested capability genuinely requires foreign code.
4. Keep extern ownership in the canonical no-GC sync backend; compatibility
   families should export that owner rather than duplicate runtime hooks.
5. Verify wrapper ABI, error propagation, ownership, and compiled execution.

Database rule:

- “Simple embedded DB” / “Simple SQLite” means
  `std.database.pure_sql.PureDatabase` unless C SQLite is explicitly requested.
- `sqlite_sffi` is the C SQLite adapter, not the pure-Simple engine.
- PostgreSQL-compatible Simple server work belongs under
  `std.database.postgres_mimic` and composes `PureDatabase`.
- Production database paths use cached SMF/LSM or native executable artifacts,
  including when the caller itself runs in interpreter mode.

Detailed SFFI reference: `doc/07_guide/platform/ffi/sffi.md`.
