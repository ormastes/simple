# Ordinary parser retained-memory regression

Fixture: `test/fixtures/ordinary_parser_retention/main.spl`.
Spec: `test/05_perf/compiler/ordinary_parser_retention_spec.spl`.
Native execution and expected counterfactual failure: **UNRUN**.

Build the fixture once with a pinned native producer and record source and
binary hashes. Run each mode/size in a fresh process under the unchanged
external 7 GB guard. Do not use the Rust seed as a general runner.

Before each run and the SSpec, bind `SIMPLE_ORDINARY_PARSER_PRODUCER_SHA256`,
`SIMPLE_ORDINARY_PARSER_PRODUCER_SOURCE_REVISION` and
`SIMPLE_ORDINARY_PARSER_SOURCE_REVISION` to the independently verified producer
binary SHA256, producer source commit and fixture source commit. The fixture
rejects missing/malformed identities; SSpec requires the exact identities,
profile, fixture digest parity, and actual cold/warm hit/miss/parse counts.
Retain the hash/build receipts separately: echoed environment identities alone
do not attest the executable and are not canonical release admission.

Arguments: `<fixture> ordinary|scoped-reference|prepare cold|warm <root> 4|8`.
Create the absolute root directory first. Cold runs require an empty cache.
For warm runs, first run `prepare cold <root> <count>` in a separate process;
then use that identical source and warmed cache in the measured process.
Each mode gets a separate cache with the same cold/warm preparation, source
bytes and count. Retain both measurement and preparation outputs. Never run
ordinary then reference against the same newly warmed cache as a cold pair.

Save stdout as `<mode>-<cache>-<count>.env` for ordinary and scoped-reference,
each cold/warm and 4/8 modules. All eight runs must exit 0 and say
`complete=yes`. Set `SIMPLE_ORDINARY_PARSER_RETENTION_REPORT_DIR` to their
directory before executing the SSpec through an admitted runner. Missing or
duplicate metrics fail closed. No collector/admission framework is added here.

The fixture validates all 128 executable function bodies, function names,
public flags, expression source spans and exact returned values in every retained
module after later-file allocations and arena closes. It reports live bytes
after each file, final live bytes/objects and elapsed microseconds. Cold/warm
mode asserts exact parse-work/cache-hit counts rather than relying on a label.

Acceptance: ordinary retained bytes <= scoped-reference + 64 KiB and live
objects <= reference + 128; ordinary elapsed <= reference * 1.5 + 20 ms;
doubling module count <= 3 times elapsed + 20 ms. The byte/object tolerances
cover bounded wrapper bookkeeping, not an allowance per retained module.
These are proposed regression budgets, not measured results. Keep external
peak-RSS receipts; complete full-module builds below 7 GB are separately
required before claiming the user goal achieved.

The timed reference primes a private immutable cache memo and uses plain
functions; ordinary AOT deliberately starts that memo cold. Both preserve
parser slots and semantic owners through the shared promotion helper.
Post-timing cases require `metadata_ok=yes`, `early_rejection_ok=yes` and
`shared_memo_ok=yes`: resource/unsafe/enum metadata, diagnostic recovery,
pre-parser advisory rejection, and scoped shared-authority publication/reuse/
changed-digest rejection/restoration must all pass before `complete=yes`.
The shared case publishes real private-cache flat-pool bytes through the
immutable cache API, not a mocked provider.

The production candidate excludes full-inventory target-cfg selection,
coverage, MC/DC and non-AOT routes. This fixture does not qualify those
excluded ownership contracts. Native and SSpec execution remain pending;
neither the source candidate nor these assertions are a release PASS.
