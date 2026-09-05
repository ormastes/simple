# Mandatory Check Tiering Detail Design

`check-push-must-pass.shs` consumes standard pre-push ref rows, rejects malformed
input or more than two unique updates, and deduplicates identical tip/base
pairs. For each remaining outgoing revision it loads the manifest and ledger from that committed revision,
recomputes the source fingerprint, validates ledger cardinality/status/command
parity and evidence hashes, and runs the registry's `tier=push` range/ref rows.
Production evidence is a regular blob loaded from the exact pushed revision;
the live checkout is not consulted, and aggregate hashed size is limited to
64 MiB. The tree-size range row is dispatched in `--push-tip` mode:
it retains absolute size, duplicate entry, source shape, load-bearing path, and
first-parent delta checks without materializing or scanning every outgoing
commit. Exhaustive detector fixtures run in the bootstrap tier.
The quick rules row extracts `rules.sdl` from the same committed ref before
parsing its numeric commands. An explicit `--rules` path exists only for
diagnostic and self-test fixtures.

`check-bootstrap-must-pass.shs` runs expensive automated manifest rows. Its
bootstrap-completion mode first requires the exact Stage 2/3 full-provenance
verdict and Stage 4 `post_bootstrap_stage4_acceptance=true` oracle, records
distinct Stage 1–4 evidence references, and then executes every automated row.
Gate logs are retained under
`doc/08_tracking/check/evidence/<source-fingerprint>/` and accepted only when the
last non-empty line is an explicit PASS verdict. Ledger replacement is atomic
only after row evaluation completes.
Production recording requires fingerprinted inputs to match `HEAD`. The
`--record-gate-pass <id> --evidence <repo-relative-path>` interface applies only
to manifest `todo` rows and accepts a committed regular evidence blob. Repeating
the same receipt preserves its first PASS timestamp; later fingerprints retain
it only while the same blob and SHA-256 remain committed.
In completion mode, automated dispatch receives the canonical validated Stage 4
candidate as both `SIMPLE_BINARY` and `SIMPLE_BIN`; these assignments override
any ambient value. The
self-test supplies a conflicting ambient path and requires its fake gate runner
to observe the admitted candidate.

Statuses are `pass`, `todo`, `blocked`, or `fail`. TODO and blocked are never
aliases for PASS. Only explicitly push-blocking rows prevent an interactive
push, allowing broad hardware/performance requirements to remain honestly open.
Each v3 result row adds `owner` and `unblock_condition`: owner may not be empty
or `unassigned`; TODO/blocked rows require a concrete non-`none` condition;
PASS requires `none`. The bootstrap producer derives stable team ownership from
the gate ID and copies the manifest description into unfinished rows.
