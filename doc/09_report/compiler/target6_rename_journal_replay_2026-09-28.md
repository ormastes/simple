# Target 6 Git and watcher rename replay (2026-09-28)

**Focused correctness result: PASS.** An unpaired filesystem rename in the
SCV journal rejects warm inventory refresh without changing the admitted
inventory. Replacing that row with a paired rename lets the next warm refresh
apply the same untracked move observed by Git and the watcher. The resulting
inventory contains the tracked source and new untracked path exactly once.

The executable spec is
`test/02_integration/app/compiler_inventory_untracked_rename_journal_spec.spl`.
Its no-stub Stage2 entry-closure native execution reports **1 example,
0 failures**. Binary SHA-256:
`7e3e60d1b11fff97d96e222740a891f1cdfe3b1ae9803dced6d41908de3529b8`.
The admitted pure-Simple Stage2 compiler SHA-256 is
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.

This fixture checks one Linux Git repository and one journal row. Loss,
concurrent publishers, longer replay histories, full entrypoint routing, and
production native performance still require qualification.
