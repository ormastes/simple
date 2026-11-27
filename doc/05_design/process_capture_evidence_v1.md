# Owned capture evidence V1

Status: SOURCE_AUTHORED_NOT_RUN. Eleven authored cases are NOT_RUN. No native,
bootstrap, runtime, linker, scheduler or engine qualification occurred.

## Problem and explicit routes

Existing `process_run_bounded_observed_v1` and Windows
`process_run_bounded_environment_v1` return an ordinary four-word native capture
projection: stdout text, stderr text, exit status and limit flags. They do not
carry EOF, stream counters or a pending cleanup owner. Exit0 and absence of a
limit flag cannot establish complete transcript capture. These existing APIs
and their executors remain unchanged.

The NEW opt-in `std.nogc_sync_mut.io.process_capture_evidence_v1` facade uses
the EXISTING POSIX ProcessObservationOwnerV1, or the EXISTING Windows canonical
WindowsCommandOwnerV2. It creates no new native executor/export, stdin route,
shell interpolation, PID adoption or caller-DTO evidence factory. Provider
consumers must explicitly select the appropriate read capture route; nothing
silently upgrades an ordinary capture result into evidence.

## Interface and admission

`ProcessCaptureRequestV1` contains `command,args,timeout_ms,stdout_limit,
stderr_limit,term_grace_ms`. `process_capture_begin_v1(request)` admits only an
absolute executable path, bounded NUL-free argv and the existing observationV1
limits: timeout1..3600000ms, grace1..30000ms and each stream0..1048576 bytes.
There is no ambiguous aggregate max; the native start receives the sum and
the existing owner installs the independent stream bounds. The facade does
not widen that native capability. Existing capability admission decides
whether the actual observation provider is available; Windows metadata
capabilities explicitly remain unsupported, so this entry cannot masquerade
as the Windows implementation.

This POSIX route inherits the trusted Host environment and sets pin=false,
matching the existing absolute-path trust boundary. It has no env/cwd/Unix
expiry, image digest, V4 resource or descendant-policy authority. Callers
requiring sanitized explicit environments must not route through it and infer
that policy. A capability-lacking provider is unavailable, not empty success.

`process_capture_windows_begin_v1(request:WindowsCommandRequestV2)` instead
preserves the installed Windows provider's exact explicit child environment,
absolute cwd, timeout, output cap and Unix expiry. Args/environment are copied
before admission. It uses `windows_command_capture_begin_v1/step_v1` over the
same canonical CommandState and single private step reducer used by the legacy
Windows command APIs. The original Windows turn/result API shape is unchanged.
The legacy route does not allocate a new evidence snapshot. There is no SSH
stdin executor, new credential/namespace change or executable digest claim.

Both entries return `ProcessCaptureTurnV1 {owner?,evidence?,error}` and
`process_capture_step_v1(owner,cancel=false)` continues the actual retained
owner. `ProcessCaptureOwnerV1` is an opaque private slot/generation. A bounded
canonical registry (32 active,100000 nonreused lifetime slots) owns the exact
lower lease, progress, busy state and sticky first diagnostic. It reserves a
slot before lower admission effects and publishes any returned lower carrier
before further classification. Positive retirement clears the resource once,
while a small closed tombstone keeps the first diagnostic; aliases can return
no fresh evidence/result after retirement. Generic native ESTALE is never
interpreted as retirement. Invalid/reentrant entries refuse without release.

Before every registry entry, including tombstones, existing native-mode gates
run and actual origin is checked. This new facade is Linux MAIN-THREAD-ONLY,
using the existing genuine retained procfs process-origin guard (including
fork/PID-namespace collision refusal), or Windows canonical-thread-only.
Other platforms and Linux worker threads are unsupported, even where the
older observation API supports other contexts. The shared Linux origin guard
retains its existing process-lifetime descriptor/arena; this leaf does not
create a second origin framework or close/reuse that inherited guard in a
child. No caller PID or origin boolean is accepted.

Cancel calls the existing same-owner bridge or Windows reducer. The private
Linux poll/collect implementation now explicitly returns the updated lease
and receipt; each collect iteration threads its returned poll lease forward,
and the capture facade stores the exact returned cancel/collect lease on
pending/error turns. Legacy public poll/collect receipt signatures and native
call order remain unchanged. No value-copy mutation propagation is assumed.
The shared pure progress reducer tests first-diagnostic and positive-consumed
transitions, but its public value DTO cannot mint or mutate canonical owners.

## Genuine evidence, absence and output

`ProcessCaptureEvidenceV1` is privately minted only from those actual owner
receipts. Its immutable getters expose the actual ProcessResult when strict
UTF8 decoding is possible, raw stdout/stderr byte copies, optional combined
`output_complete`, optional per-stream EOF/counts/truncation, delivered-to-Simple
byte counts, optional terminal/reaped/identity/cancel/native-error facts and
explicit retirement confirmation. Mutable raw-byte getters return fresh
copies. An embedded NUL or invalid UTF8 byte is preserved as bytes; no lossy
text reencoding or empty-success replacement occurs. Decode failure keeps the
raw evidence and an explicit error; a retired owner is not resurrected merely
to carry invalid text.

The POSIX V1 metadata supplies only COMBINED EOF. Per-stream EOF getters are
nil. Native seen/kept/truncation, final identity-revalidation, reaped, cancel
and raw error fields are projected only when actually observed. Additive
defaulted fields in ObservedProcessResultV1 preserve legacy constructors and
distinguish unknown metadata from false/zero. Delivered counts denote actual
native byte arrays received by Simple, not guessed total pipe traffic.

Windows evidence comes directly from private CommandState raw arrays, actual
broken-pipe EOF observations, exact process/job terminal observation and
positive native handle/allocation cleanup. Evidence is emitted only after
actual closed state, before the nonreused canonical slot is retired. The
combined EOF is the conjunction of those genuine per-stream facts, independent
of exit/limits. Windows seen/truncation/POSIX-reap/native-error/identity fields
are nil because the existing owner does not supply them. Kept/delivered are
the actual retained byte lengths; the existing ProcessResult carries the
actual global output/timeout limit. No unsupported per-stream flags or image
attestation are invented.

Consumers must inspect the actual receipt and error rather than trusting exit0.
Incomplete stdout, timeout/truncation, invalid text, native error and failed
cleanup remain distinct. This facade does not settle container charges or
turn a CLI process exit into workload completion; common container/logs and
app integration remain separate consumers.

## Retirement and cleanup

Existing native V3 collect adapters retire a reaped terminal outcome even if
its runtime_error is nonzero, except EAGAIN/EBUSY. The old observation wrapper
discarded that terminal-error retirement before returning its error receipt.
The narrow repair records genuine raw final receipt fields and sets consumed
before returning ProviderFailed. `observed_process_collect_retired_v1` is the
shared pure rule matching runtime_process_owned.c collect/end-consume; it is
explicitly not success or EOF. A terminal provider error can therefore return
retired=true with an error and incomplete output. It cannot leave a supposedly
live Simple carrier for a native record already consumed.

For malformed, missing, pending or uncertain native receipt, the real owner
remains Some. The facade never derives retirement from exit0, EOF, absence of
truncation, a PID or an arbitrary caller receipt. POSIX CleanupPending is a
retryable observation status, not automatically a sticky native failure.
Other provider/cancellation/decode errors remain diagnostics while cleanup can
continue. Windows retains its canonical native handles/allocations on every
cleanup failure and confirms retirement only from actual closed state or the
known nonreused retired slot. It never reconstructs authority from text.

Native array projection loss/malformed collect can leave retirement uncertain;
the wrapper retains that unresolved carrier, rather than claiming release.
This source change does not fix native allocation/projection error behavior.
It also does not claim all OS resources successfully closed merely from POSIX
record retirement: that is the existing native adapter's exact consumption
fact, while Windows closed specifically follows its positive cleanup checks.

## Bounds and qualification

POSIX collect reuses its existing25ms poll loop and finite
`(timeout+grace+1000)/25+4` budget; it is synchronous, not a new nonblocking API.
Windows steps keep the existing bounded pipe chunks and wait0; this facade
adds no Sleep or positive Windows wait. Final raw snapshot/copies can process
the existing bounded capture size (Windows<=16MiB), so turn/copy latency is
unqualified. Native fixture scheduling yields are confined to test code.

Six pure cases exercise actual production defaults, retirement rule, raw
copy, request admission and sticky/positive-retirement transitions. Four Linux
native prerequisite specimens use real printf/sleep for complete output,
copied-owner completion with a real non-UTF8 diagnostic, truncation and cancel. One Windows
specimen uses real whoami on the canonical native thread and verifies genuine
EOF while unsupported counters remain nil. Missing external platform setup
fails; no fake native owner or skip is used. All eleven are NOT_RUN.

NOT_COVERED: native projection/close/kill faults, late descendants holding pipes,
adversarial clock/identity changes, cross-thread scheduling, real managed
sanitized-env integration, common provider/logs qualification, native ABI/link,
latency/RSS and live container engines. No native campaign was restarted.
