# Target 5 SQLite shared-provider probe (2026-09-28)

## Result and limits

On Linux aarch64, the existing `runtime_sqlite.c` builds as a separate O2
shared library with SONAME `libsimple_sqlite_provider.so`: 21,872 bytes,
SHA-256 `e2d14283453aff745217b711281ebb644dbaee67a4c5e472aa912c1a59f4f3f5`,
27 exported `rt_sqlite_*` symbols, and `libsqlite3.so.0` in `DT_NEEDED`.

A no-stub Stage2 native UI access-store spec linked against a debug build of
that library. The executable is 121,392 bytes, SHA-256
`0b2b56f87a3311def892c9ffc0af1a90b887a7d18049d4af853a3be05a374249`.
It passes two examples with zero failures: two inserts and two reads exercise
cached prepared-statement reuse, while a disabled-cache case checks cleanup
after both a binding error and successful operations before close.

The executable itself names the provider library in `DT_NEEDED`, so the loader
maps it at process startup. This probe proves a separate linkable artifact and
the focused UI storage behavior; it does **not** prove first-demand loading,
release-small size, startup/RSS improvement, packaging, or cross-platform
feature preservation. No normalized time/RSS verdict is claimed.

## Bugs exposed and fixed

1. `PreparedStatement.execute()` and `query_rows()` finalized a cached SQLite
   statement. `Database.exec()`/`query()` then reset or reused the freed handle.
   GDB showed `sqlite3_reset` trying to lock mutex `0xfd71` through the stale
   statement. Removing those premature finalizations leaves finalization with
   `StatementCache.clear()` on close or eviction. When caching is disabled,
   `Database` now finalizes its caller-owned statement on success and error.
2. SQLite returned correct text: GDB observed `sqlite3_column_text` bytes
   `main`, and the returned Simple string had length 4. Direct native probes
   passed text through the extern, `DbValue`, a `DbRow` array, and prepared
   rows after reset and close (5 examples, 0 failures). The UI row decoders
   passed optional row values directly into non-optional fields. Explicit
   unwraps after their nil guards preserve event text in the final spec.

The final spec covers event decoding; surface and node decoder changes use the
same guarded unwrap pattern but are not independently exercised here.

## Remaining Target 5 work

Package the provider with an immutable ABI/variant receipt and an atomic
install manifest, activate it on first UI storage demand, test missing/corrupt
and concurrent activation, then measure startup, peak RSS, and binary size on
matched workloads. The full CLI still has unresolved optional-provider link
symbols; this isolated spec does not qualify that closure.
