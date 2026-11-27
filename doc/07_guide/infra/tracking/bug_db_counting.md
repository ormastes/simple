# Counting the merged bug database

Run `sh scripts/check/bug-db-shard.shs count [legacy.sdn]`. It applies the
per-bug shards beside the legacy file, counts both bug tables, and prints
sorted `<table> <severity> <status> <n>` plus `TOTAL` rows.

Check the command's exit status before accepting its output. A valid database
with zero bug rows returns zero and prints no tally rows. Missing legacy input
prints an `ERROR` diagnostic to stderr, emits no tally, and returns 2. A merge,
aggregation or sorting failure returns nonzero; do not interpret it as zero
bugs. The operation reads the database and uses private temporary files only.

Use `sh scripts/check/bug-db-shard.shs --selftest-count` for the bounded
read-only count controls: missing input is rejected, a valid empty database
succeeds, and nonzero counts combine both tables exactly. This command needs
no seal hasher or compiler. The existing full `--selftest` includes these
controls and additionally tests shard publication and seals; its hash-provider
requirements still apply. Count tests do not qualify seal validation or the
Simple database implementation.
