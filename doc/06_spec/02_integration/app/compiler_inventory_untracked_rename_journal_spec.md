# Compiler inventory watcher and Git rename replay spec

Executable source:
`test/02_integration/app/compiler_inventory_untracked_rename_journal_spec.spl`.

The spec admits a Git inventory with an untracked `src/a.spl`, renames it to
`src/b.spl`, and appends an unpaired watcher rename. Warm refresh must reject
the event and retain the old inventory. The spec then replaces the journal
row with a paired rename; warm refresh must admit exactly the tracked source
and `src/b.spl`, with no duplicate or stale `src/a.spl` entry.

The 2026-09-28 no-stub native execution reports one example and zero
failures. See
`doc/09_report/compiler/target6_rename_journal_replay_2026-09-28.md` for
binary identity and limits.
