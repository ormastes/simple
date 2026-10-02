# SCV snapshot materialization resource profile

Executable specification: `test/05_perf/scv/compile_snapshot_resource_profile_spec.spl`.
Standalone native fixture: `test/fixtures/scv_snapshot_memory/main.spl`.
Collector: `scripts/check/check-scv-snapshot-resource-profile.shs`.

Status: authored; native execution and measured acceptance are pending. This
manual records intended assertions, not a performance or release PASS.

## Scenarios and thresholds

| Scenario | Native work | Assertion |
|---|---|---|
| Fresh scoped versus unscoped baseline | Separate OS processes at 256 and 512 unique source paths | Equal retained-row SHA256 at each size; all fields present exactly once |
| Cold first materialization | A UTF-8/CRLF source over 64 KiB, before any prior transient scope | Retained result survives later scopes; destination bytes and digest match |
| Raw-table high-water cleanup | Both modes run the same large inventory-file event, followed by 255/511 files under 1 KiB | Scoped elapsed <= baseline * 1.5 + 20 ms; scoped 2N <= scoped N * 3 + 20 ms |
| Retention and peak RSS | Whole-process kernel high-water RSS; exact live-object delta during materialization | Scoped live objects * 2 < baseline; scoped RSS <= baseline + 16 MiB |
| Failure and recovery | Stale admitted digest followed by a valid file | Exact drift-refusal reason, empty failed row, subsequent valid row |

Each process refuses an already populated fixture directory and begins with
an empty chunk store. The same two content bodies and path order are used in
both modes: one large file followed by many small files. Small files share a
content-addressed chunk, so both modes have identical cold/hit sequences.

The inventory prelude grows allocation-table cardinality through a real
production path; a large byte buffer alone would not establish that condition.
No warm-up precedes the first scoped snapshot operation. Snapshot elapsed time
includes that first cold operation and the subsequent small-file interval,
but excludes the identical inventory prelude and post-run checks. Peak RSS
includes fixture setup, prelude, materialization and validation. Raw-table
capacity is not claimed to be directly measured. Every retained row and every
destination's exact bytes are checked after scopes end. Positive elapsed and
live counts are required. Elapsed samples must be below 60 seconds.

## Producer and fixture binding

Compile this fixture once using the reviewed pure-Simple producer after its
hello compilation and execution pass, in a private producer-bound cache and
under the existing owner guard. The collector does not compile anything.
Do not use the Rust seed as a general fixture/test runner. Record actual build
evidence; receipt-shaped files alone do not establish production admission.

Use the successful hello route's exact backend/runtime/guard bindings, changing
only the entry, private cache and output. For the current Windows LLVM lane:

```sh
"$SCV_PROFILE_COMPILER" native-build --backend llvm --entry-closure \
  --runtime-bundle core-c-bootstrap --runtime-path "$PINNED_RUNTIME" \
  --entry test/fixtures/scv_snapshot_memory/main.spl \
  --cache-dir "$PRIVATE_FIXTURE_CACHE" --mode one-binary --threads 1 \
  --output "$SCV_SNAPSHOT_PROFILE_BINARY"
```

The owner must run that command inside its existing bounded wrapper; this is
not authorization to retry a failed compiler unchanged or bypass admission.

Set these environment variables:

- `SCV_PROFILE_COMPILER`: absolute native producer path.
- `SCV_SNAPSHOT_PROFILE_BINARY`: absolute compiled fixture path.
- `SCV_SNAPSHOT_PROFILE_SOURCE_SHA256`: pinned SHA256 of the producer's reviewed
  source manifest. The fixture is added to that frozen source lineage, with
  its own content hash recorded below; do not silently replace dependencies.
- `SCV_SNAPSHOT_PROFILE_BUILD_RECEIPT`: actual fixture build receipt.

The build receipt is UTF-8 key/value text, one row per key:

```text
schema=simple-scv-snapshot-profile-build-v1
producer_sha256=<producer executable hash>
binary_sha256=<compiled fixture hash>
source_sha256=<pinned producer source-manifest hash>
source_manifest=<absolute manifest path>
fixture_sha256=<hash of test/fixtures/scv_snapshot_memory/main.spl>
build_exit_status=0
complete=yes
```

The default collector replays the existing canonical Stage2 admission validator
through `check-scv-inventory-resource-profile.shs --admission-only`. A missing
admission is a failure; the collector never falls back to provisional mode.

An explicit `--diagnostic-only` permits the currently authorized provisional
Windows lane after hello PASS. It additionally requires
`SCV_PROFILE_COMPILER_SHA256` and `SCV_SNAPSHOT_PROFILE_HELLO_RECEIPT`. The hello
receipt must point to the actual successful compile/run evidence and binary:

```text
schema=simple-scv-snapshot-profile-hello-v1
producer_sha256=<same pinned producer hash>
source_sha256=<same pinned producer source-manifest hash>
compile_exit_code_path=<actual hello compile exit-code file containing 0>
run_exit_code_path=<actual hello execution exit-code file containing 0>
run_stdout_path=<actual hello stdout containing hello>
binary_path=<actual hello executable>
binary_sha256=<actual hello executable hash>
complete=yes
```

Diagnostic reports emit `admission=provisional` and `qualification=pending`.
Even successful metric assertions do not admit release, Phase3/4 or the full
compiler. Default reports emit `admission=canonical` and identify only producer
qualification, not full release qualification.

## Linux/macOS collection and Windows measurement handoff

With the bindings above, Linux/macOS owners run four fresh processes using
the collector's bounded `/usr/bin/time` route:

```sh
sh scripts/check/check-scv-snapshot-resource-profile.shs
# Explicit provisional diagnostics only:
sh scripts/check/check-scv-snapshot-resource-profile.shs --diagnostic-only
```

The collector prints its unique retained evidence directory to stderr and the
typed aggregate report to stdout. For Windows, the owner runs the same four
commands through its existing bounded process wrapper, with unique empty
roots, and writes `scoped_n.out`, `scoped_double.out`, `baseline_n.out`, and
`baseline_double.out` from the fixture's actual stdout:

```sh
"$SCV_SNAPSHOT_PROFILE_BINARY" --scoped --root /absolute/new/scoped-n
"$SCV_SNAPSHOT_PROFILE_BINARY" --scoped --double --root /absolute/new/scoped-double
"$SCV_SNAPSHOT_PROFILE_BINARY" --baseline --root /absolute/new/baseline-n
"$SCV_SNAPSHOT_PROFILE_BINARY" --baseline --double --root /absolute/new/baseline-double
```

Every process has a 60-second owner timeout. Capture the Windows process's
kernel `PeakWorkingSetSize` while its handle is retained; interval RSS samples
and Job commit counters are not interchangeable with that lifetime peak.
Preserve raw measurements. Next to each `.out`, the owner writes its matching
`.env` measurement receipt from the actual execution:

```text
schema=simple-scv-snapshot-profile-measurement-v1
producer_sha256=<bound producer hash>
source_sha256=<bound source hash>
binary_sha256=<bound fixture hash>
mode=scoped
size=n
fresh_process=yes
fixture_root=<unique absolute root used by this sample>
exit_status=0
peak_rss_bytes=<positive kernel process peak working-set bytes>
peak_kind=kernel-process-high-water
stdout_sha256=<raw .out hash>
```

Set `SCV_SNAPSHOT_PROFILE_EVIDENCE_DIR` to the four-pair directory and consume
the receipts without rerunning any native process:

```sh
sh scripts/check/check-scv-snapshot-resource-profile.shs --diagnostic-only --receipts
```

LF and CRLF receipt/stdout line endings are accepted; hashes bind original
bytes. Missing/duplicate fields, unsupported peak semantics, hash mismatches,
failed exits, reused fixture roots, invalid metrics or missing completion
cannot emit `complete=yes`. That marker means collection completed, not that
thresholds passed. The SSpec owns the numerical comparisons.

When an admitted test-capable runner is available, set the evidence directory
to reuse measurements, and run:

```sh
<self-hosted-test-runner> test test/05_perf/scv/compile_snapshot_resource_profile_spec.spl --mode=interpreter
```

For explicit provisional comparisons also set
`SCV_SNAPSHOT_PROFILE_DIAGNOSTIC=1`; canonical qualification remains pending.
No native measurements were produced while authoring this harness.
