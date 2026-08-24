# Mandatory Check Tiering Detail Design

`check-push-must-pass.shs` consumes standard pre-push ref rows, rejects malformed
input or more than two unique updates, and deduplicates identical tip/base
pairs. The canonical pre-push wrapper marks its invocation explicitly: an empty,
readable stream in that context is a named `0 refs to push (no-op)` PASS, while
direct empty input remains a failure so a missing producer cannot pass vacuously.
For each remaining outgoing revision it loads the manifest and ledger from that committed revision,
recomputes the source fingerprint, validates ledger cardinality/status/command
parity and evidence hashes, and runs the registry's `tier=push` range/ref rows.
Production evidence is a regular blob loaded from the exact pushed revision;
the live checkout is not consulted, and aggregate hashed size is limited to
64 MiB. The tree-size range row is dispatched in `--push-tip` mode:
it retains absolute size, duplicate entry, source shape, load-bearing path, and
first-parent delta checks without materializing or scanning every outgoing
commit. Exhaustive detector fixtures run in the bootstrap tier.
Production profiling on 2026-08-24 found the former tree-mode subset alone took
about 59 seconds. Eight whole-tree, compiler, or executable checks were moved
to automated bootstrap rows: use-target resolution, C runtime compilation,
direct-runtime scanning, signature provenance, performance-mechanism coverage,
process-wait EINTR coverage, guard wiring, and outline parsing. Their ledger
rows remain required TODO until a bound bootstrap records real PASS evidence.
The use-target resolver requires every Git-indexed `src/` and `test/` input to
be physically materialized; sparse/partial inputs are ERROR, not empty modules.
Its baseline identity excludes diagnostic line numbers and binds class, source
file, module, and member, preventing line-only edits from creating NEW/STALE
pairs.
The push tier retains the two measured sub-second structural tree checks plus
the bounded committed-ref/range guards.
The runtime-API range guard uses `--scan-only` only from its closed push
dispatch row; that mode requires an explicit range. Its four mutation fixtures
remain a separate automated bootstrap row, while default manual execution still
runs them before scanning.
An earlier committed tree measured 10.21 seconds/225,032 KiB before the fixture
split and 9.27 seconds/223,520 KiB afterward. Current main measures 11.05
seconds/225,736 KiB after runtime extraction optimization, so NFR-MCT-001 is
again RED by 1.05 seconds. The focused fixture is coverage, not the production
timing oracle; the current production row is authoritative.
The interpreter-extern registry and type-walk constructor mutation fixtures now
run only as distinct required bootstrap rows; their production push rows use
`--scan-only`. The same exact committed-ref production oracle passes in 4.57
seconds/227,920 KiB afterward: 58.6% lower elapsed time than 11.05 seconds, with
a 0.97% peak-RSS increase. NFR-MCT-001 is GREEN.
For the runtime-API range gate, Git tree equality over both runtime roots is an
algorithmic fast path: an unchanged range extracts and counts the tip once;
any changed runtime root performs the full base/tip removal analysis. The
unchanged-range scan measured 7.43 seconds before and 3.89 seconds afterward,
with non-vacuity and mutation fixtures retained.
Committed symbol extraction is batched by implementation through one Git tree
grep for Rust and one for C rather than one `git show` per file. Exact-set
comparison proved 1,804/1,804 Rust and 1,504/1,504 C symbols identical; combined
with tree equality, the unchanged-range scan reaches 0.84 seconds.
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
to manifest `todo` rows and accepts a committed
`simple.must-check-gate-receipt/v1` whose gate ID, source fingerprint, final
PASS verdict, and separate committed artifact SHA-256 all validate. Repeating
the same receipt preserves its first PASS timestamp; later fingerprints retain
it only while the same blob and SHA-256 remain committed.
In completion mode, automated dispatch receives the canonical validated Stage 4
candidate as both `SIMPLE_BINARY` and `SIMPLE_BIN`; these assignments override
any ambient value. The
self-test supplies a conflicting ambient path and requires its fake gate runner
to observe the admitted candidate.
Bare run mode fails before evaluation or ledger mutation because it lacks that
Stage 1–4 binding. The ledger completion timestamp stays `never` unless every
bootstrap row is PASS, then equals the latest preserved row PASS timestamp.

Statuses are `pass`, `todo`, `blocked`, or `fail`. TODO and blocked are never
aliases for PASS. Only explicitly push-blocking rows prevent an interactive
push, allowing broad hardware/performance requirements to remain honestly open.
Each v3 result row adds `owner` and `unblock_condition`: owner may not be empty
or `unassigned`; TODO/blocked rows require a concrete non-`none` condition;
PASS requires `none`. The bootstrap producer derives stable team ownership from
the gate ID and copies the manifest description into unfinished rows.
