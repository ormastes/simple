# Windows live process runner buffers child progress

Status: OPEN. Source audit only; no production repair or native regression PASS.
Date: 2026-10-24.
Audited release: `a4e59c4fc3756127c1f98b5d6709f023342b0d27`.

## Observed operation

Codec diagnostic probe5 launched parent PID42972 and final worker PID27912 using
producer SHA256 `88f3c81b4a529d344cfc9459f1b3e036b6b34b49c81c1530f8d7e6af8edd8798`.
Two HIR shards completed at about108.6 seconds. The retained outer log then
showed no new child phase lines while the child remained active. CPU/RSS and
silence do not identify its stack or compiler phase.

Preserved evidence: `C:/dev/simple-hir-codec-decode-storage-20261024/probe5/build.log`,
`build.receipt`, `build.rss.env` and `inputs.sdn`. The temporary collector log
was finalized and no longer exists. These diagnostic paths are not bootstrap
admission.

The probe is now terminal: native exit1, quiescent1, peak10914728KiB, with no
timeout or RSS-guard termination. The final buffered log records HIR completion
at elapsed731904ms (dt554364ms), then MIR completion369/369:368 succeeded and
one failed at elapsed982260ms. The actual error is `convert_nodes.spl:1657`,
where `PatternKind.Array(..., nil)` supplies `nil` to an optional-text field
that requires `None`. The final log therefore proves that part of the silent
interval contained HIR/MIR work. It does not establish the exact stack at any
earlier CPU/RSS observation.

The worker argv contains `run src/app/cli/native_build_worker.spl`. This does
not prove source interpretation: producer source `a3ea4530e3a` already contains
`bootstrap_main.spl:613-628` and `bootstrap_internal_worker_routing.spl:2-8`.
With the admitted worker marker, that allowlisted command enters the compiled
backend installer and shared native worker entry. The coordinator sets the
marker before shards and final worker dispatch. The live child's environment
and actual branch were not independently observed in this audit.

## Proven source defect

`src/app/cli/native_build_main.spl:1485` invokes
`process_run_timeout_live`. Despite its live-relay contract,
`src/lib/nogc_sync_mut/io/process_ops.spl:1656-1661` sends Windows requests to
`process_run_timeout_windows`, whose line1619 calls `_process_run_bounded_raw`.
The tuple is returned after child capture completes. Unlike the POSIX branch,
this path does not incrementally relay child stdout or stderr. Thus buffered
progress explains the missing visibility. The finalized child log proves
HIR/MIR activity during part of the interval; it does not reconstruct a stack
for each earlier silent observation.

## Why a direct redirected-owner replacement is incorrect

The existing pure-Simple `windows_redirected_process.spl` owns exact argv,
retained JobObject lifecycle and raw DWORD completion. However its spawn wrapper
replaces HOME, temporary-directory and cache environment variables. Its wait
loop cancels children when capture files exceed the configured limit. Both are
observable changes from the current live-runner contract.

The original 64MiB limit applies independently to retained stdout and stderr.
It retains stream heads and tails with a truncation marker; output overflow
itself does not terminate the child. This is implemented in
`src/compiler_rust/runtime/src/value/sffi/env_process.rs:492-530` and
`src/runtime/runtime_process.c` (`WinCapture`, `win_capture_*`,
`win_process_run_capture`). Timeout markers and legacy signed exit conversion
also belong to those owners and must be preserved, not guessed.

Retaining head/tail data in memory while leaving unbounded capture files on
disk would not provide bounded resource use. Killing on overflow is not an
authorized replacement for truncation. Concurrently truncating a file still
owned by the child would introduce offset/race hazards.

## Existing chunk-owner boundary

The process observation adapter in `process_ops.spl:422-429` requires advertised
provider capabilities before admission; its poll wrapper exposes byte chunks.
On Windows, `runtime_process_owned.c:5335-5345` advertises the V3 observation
adapter unavailable, and its poll entry at5401 returns an unsupported receipt.
The existing Windows implementation exposes synchronous collection, not this
required asynchronous chunk-owner capability. Therefore it cannot be silently
used as a working Windows streaming provider.

## Required narrow repair

Extend the existing Windows owner with supported bounded byte-chunk observation
under its existing JobObject and exact argv/env/cwd custody. Preserve the
current per-stream head/tail truncation contract and timeout/exit markers.
Do not create a second child policy, reinterpret absent capabilities as support,
or change Rust-seed/bootstrap authority. Keep raw native DWORD status until the
existing legacy tuple boundary; diagnostics remain separate from admission.

The facade can then poll at100ms in this long-process wrapper, relay bytes in
bounded chunks without decoding split UTF8 scalars or inserting newlines, and
maintain independent per-stream order. No total order across stdout/stderr is
promised. Collect the final tail only after genuine tree-empty/reaped proof;
release the process slot once and clean only owned files/handles on all paths.
Existing callers of the redirected wrapper retain their current policy.

## Native acceptance design (not run)

A child emits stdout and stderr, then waits for a parent-controlled release.
The parent must observe both before allowing child exit; a final tuple alone
cannot pass streaming acceptance. Include a multibyte UTF8 scalar crossing a
64KiB boundary, no-newline final output, partial writes, quotes/spaces/Unicode
argv, and inherited HOME/TMP/cache sentinel values. Check independent stream
byte fidelity, raw nonzero DWORD including `0xC0000005`, zero/unlimited and
negative/default deadlines, timeout with a grandchild, head/tail truncation
without overflow cancellation, failed reads/writes, and exact cleanup/slot
release. Use24 requested test jobs under normal resource admission.

No native build or test was launched for this audit. Preserve the failed
producer and probe5 evidence; no existing repair was applied. A new compiled
owner must be qualified with a matching runtime/ABI before claiming a fix.
