# Windows configured PTY launch: independent source review

Date: 2026-10-25. Reviewer: Astra independent audit lane.
Workspace: D:/dev/simple-coremux-shared-20261025.
Scope: frozen v1, nine production paths and five companion artifacts.
STATUS: WARN; v1 has one P1 and one P2 source finding. Executable qualification: NOT_RUN.
Nine authored unit scenarios and the standalone native fixture are not executed evidence.
No compiler, test, native fixture, helper executable, or product was launched by this review.

## Exact reviewed inputs

Both manifest hashes and all fourteen file hashes were checked once and matched.
These are historical v1 pins; subsequent author corrections do not alter this evidence.

- build/review/windows-pty-configured-launch-source-freeze-v1.sdn:
  49d9eb20aef3dc3de45b1dafcf06daa389c6033ded0b40dde538c6486c18485f
- build/review/windows-pty-configured-launch-artifact-manifest-v1.sdn:
  510b60cf92c9f8d09d23133274f07ba5702e68a573b2c141d21afd6146c72ba4

| Frozen path | SHA256 |
| --- | --- |
| src/lib/sys/pty_launch.spl | 1794814de109168412a33c80976d08a1f17a1428d76de7c7c2145c9fc8f09b92 |
| src/lib/sys/pty.spl | e79dd31649d941ee04bafc86c5bd68a2d39737512c53fb9364a42be921dd055d |
| src/lib/nogc_sync_mut/sosix/pty.spl | 4a15648e6fa83825d28c61a3bc6bb0b55eea24c7cc2fc0535816efbb51093ac9 |
| src/lib/nogc_async_mut/sosix/pty.spl | 334a1d03798d734026b849b634f2bae028c0d65d04f45ddc32f32965b58cfef5 |
| src/providers/windows_native/lib/sys/pty.spl | 5f3e26f4108a85bb9070d14e661877cbfe81afe2f6ec196e37c46b280fe67087 |
| src/lib/nogc_sync_mut/io/windows_pty_launch_abi.spl | 79cf67c213cdb830aab08422e626218281c83907efb631fd4dde40755c1f08d5 |
| src/lib/nogc_sync_mut/io/windows_pty_launch_config.spl | 255b6344e100607b3a8de0b7d6b0114a05ba01abbcdafdaf7e99587af5c3b477 |
| src/lib/nogc_sync_mut/io/windows_pty_environment_owner.spl | f1844e7bb46fb9d858da6d894f32db5d95deae29bb82036988458d7caa39f308 |
| src/lib/nogc_sync_mut/io/windows_pty_owner.spl | 0d2df0f4807b2a4bd44fd982693d293c469e860af9cf52e16bc72fb7ae911145 |
| test/01_unit/lib/io/windows_pty_launch_config_spec.spl | 277732770897d9575fbeac9f13331c1cb1b34a7d9779c15179148a35b0aec95e |
| doc/06_spec/01_unit/lib/io/windows_pty_launch_config_spec.md | acbb66e133eb8d49f32b606abeef2838a8c12aec8ac8dfc445c37a58f04b2e78 |
| test/fixtures/compiler_entrypoint/windows_pty_launch_probe/main.spl | 1dad7d011a79ed4fc6b5c8ab0a517a1408978f503c50f797ae806b4c89196c80 |
| test/fixtures/compiler_entrypoint/windows_pty_launch_probe/environment.spl | cff742a3fd52ba972a48ffbb4ed61be5c3b599d464caf8cb7d438ae9ad758972 |
| doc/09_report/coremux_windows_pty_launch_source_2026_10_25.md | ffd3e8cdc3e0f10c22a4d5079b053ed30d194b743af878525c0e9bcd5aaf8117 |

## P1: historical launch failure prevents discharge of proven cleanup

In frozen windows_pty_owner.spl, failed admission sets state.failed at line324
and invokes cleanup. close at line472 returns not state.failed for an already
closed record; its final return at line498 similarly requires not state.failed.
The failure flag remains sticky after a missing executable or invalid working
directory. Consequently, a record can have terminal_observed, all owned resources
released, and cleanup_proof_v1 true (lines158-162), yet every later close returns
false.

This is a production contract defect, not merely a strict fixture assertion.
smux/child_lifecycle.spl:15-20 clears retained PTY authority only when
sosix_pty_close returns true. A caller retaining an opened PTY after spawn failure
cannot discharge it under this contract. This is a source call-chain conclusion;
configured spawn is not claimed to have produced an observed smux runtime failure.

The native probe's close_proven (main.spl:32-37) correctly requires both successful
close and the cleanup proof. Its expected missing executable/cwd rows at77-82
therefore expose the contradiction instead of passing clean resource release.

Required correction: distinguish historical admission/I/O error from proven
terminal resource completion. Preserve the original spawn error and retained
failed handles. Do not report successful close for pending I/O, unobserved process
termination, unreleased pointers/handles, or an unresolved release failure.
Do not weaken close_proven to hide the defect. The author reports a shared
completion predicate correction in progress; v2 review remains pending.

## P2: supported Unicode sizes trigger quadratic traversal

windows_pty_launch_config.spl:21-32 counts UTF16 units using char_code_at for
successive scalar ordinals. The native implementation in runtime_native.c:
4173-4226 has an ASCII shortcut, but its Unicode path at4208-4225 walks from the
beginning for each ordinal. A supported large Unicode environment value therefore
incurs quadratic work before launching. The reused
windows_process_owner.spl:185-207 UTF16 conversion repeats that traversal, so
changing only the first validator would leave the end-to-end launch problem.

This is a source complexity finding, not a measured latency claim. A one-MiB
input cap does not establish acceptable owner-thread responsiveness.
Use the canonical linear UTF8 byte/scalar facilities and bounded linear UTF16
emission, preserving existing quoting and public signatures. Keep validation
strict for truncated/invalid UTF8, surrogate encodings and out-of-range scalars.
No separate malformed-public-text exploit is claimed: this review has not
established a public invalid-text construction path. The existing ordinal runtime
decoder alone is not sufficient evidence of strict byte validation.

## Positive source findings within the reviewed scope

- Portable launch values carry Exec executable/argv or explicit Shell command,
  optional cwd, and ordered Set/Remove changes. Facades forward the complete value.
  The default unsupported backend returns an attributable error. Generic provider
  selection is retained; no application-level family root or parent mutation was
  introduced.
- Configured Exec passes a separate non-null application name and writable quoted
  command line. Shell obtains cmd.exe under GetSystemDirectoryW; COMSPEC is not
  application authority. Cwd and environment are actual CreateProcessW arguments,
  not shell prefixes. Legacy command launch retains its prior null application,
  inherited environment/cwd, and creation flags.
- The four newly declared Win32 calls have consistent Win64 pointer/integer
  signatures by source inspection and explicit unsafe ownership annotations.
  This does not qualify their emitted calling convention or actual native linkage.
- Environment preparation retains the native GetEnvironmentStringsW snapshot.
  Untouched entries, including hidden drive assignments and raw UTF16 units, are
  copied without a UTF8 round trip. Native ordinal case folding drives sorting and
  matching. Ordered changes support empty values, removal and later replacement.
  Bounds cover snapshot scanning, entry count, allocations and the final double-NUL
  block. No SetEnvironmentVariable production mutation is introduced.
- Heap pointers and environment snapshots transfer explicitly to the PTY owner.
  Failed frees retain their pointers. Child creation is suspended, Job assignment
  precedes ResumeThread, and inherited handles are disabled. Launch arguments remain
  alive until CreateProcessW has consumed them. Failed admission enters the existing
  retained cleanup/quarantine path.
- The fixtures have meaningful argv/cwd/environment/child-output and leader-exit
  assertions, perform cleanup before returning outcomes, and require an empty native
  cleanup queue. They are authored controls, not measured native behavior.

## Native evidence still required

Use an admitted Windows producer with configured generic library selection and
the real native PTY overlay. Run the nine unit scenarios and native self-child
fixture with a finite external watchdog; preserve real stdout, errors, exit status,
resource observations and hashes.

The native fixture requires a differently located launch cwd; an executable named
windows_pty_launch_probe.exe inside a path containing a space and Korean characters;
a seeded inherited SMUX_WPL_PARENT value; an actual hidden drive environment entry;
and genuinely missing negative executable/directory paths. Its poisoned COMSPEC is
a child environment change, not evidence of a poisoned parent COMSPEC experiment.

Required observations include empty/quoted/backslash/Unicode/literal argv,
explicit cwd, case-insensitive environment replacement/removal and unchanged parent
raw UTF16, shell operation despite the child COMSPEC value, rejection/cleanup of
invalid launches, actual process exit and Job-empty cleanup proof. The fixture
does not independently sample OS PID reuse; retained process/Job handles are its
termination authority. Native allocation/free/Job-assignment fault injection is
still unresolved. Do not label those negative paths executed or proven by source.

Synchronous native API calls, Unicode throughput and live backpressure need
actual bounded execution. No all-platform parity, production readiness, or runtime
PASS follows from this review.

## Primary API references

CreateProcessW documents the writable UTF16 command line, 32767-character limit,
Unicode environment flag, explicit application-name behavior and hidden drive
environment entries:
[CreateProcessW](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-createprocessw).

Native ordinal comparison and its case behavior:
[CompareStringOrdinal](https://learn.microsoft.com/en-us/windows/win32/api/stringapiset/nf-stringapiset-comparestringordinal).

Environment ordering and parent/child block behavior:
[Changing environment variables](https://learn.microsoft.com/en-us/windows/win32/procthread/changing-environment-variables).

These references were obtained through the context fetch/index tools. Primary
documentation supports the API contracts; it does not substitute for execution
of this implementation.

## Correction cycle 2: focused v2 review

STATUS: WARN / source corrections accepted; executable qualification remains NOT_RUN.
No remaining scoped P0/P1/P2 finding was identified. Thirteen unit scenarios are
authored and zero executed; the native fixture is also NOT_RUN. V1 findings and
hashes above remain historical evidence.

Both v2 manifests and all sixteen production/companion hashes matched. The
manifest's prior-review pin matched the original v1 report before this append.

- build/review/windows-pty-configured-launch-source-freeze-v2.sdn:
  f931e0207573d1ab490cff90551eaf286098956ee444dec3a43ede0c58a84839
- build/review/windows-pty-configured-launch-artifact-manifest-v2.sdn:
  7516ada804494e8d11779ff348fab8f255604b83eee09c292902d6088bac79be

| V2 path | SHA256 |
| --- | --- |
| src/lib/sys/pty_launch.spl | 1794814de109168412a33c80976d08a1f17a1428d76de7c7c2145c9fc8f09b92 |
| src/lib/sys/pty.spl | e79dd31649d941ee04bafc86c5bd68a2d39737512c53fb9364a42be921dd055d |
| src/lib/nogc_sync_mut/sosix/pty.spl | 4a15648e6fa83825d28c61a3bc6bb0b55eea24c7cc2fc0535816efbb51093ac9 |
| src/lib/nogc_async_mut/sosix/pty.spl | 334a1d03798d734026b849b634f2bae028c0d65d04f45ddc32f32965b58cfef5 |
| src/providers/windows_native/lib/sys/pty.spl | 5f3e26f4108a85bb9070d14e661877cbfe81afe2f6ec196e37c46b280fe67087 |
| src/lib/nogc_sync_mut/io/windows_pty_launch_abi.spl | 79cf67c213cdb830aab08422e626218281c83907efb631fd4dde40755c1f08d5 |
| src/lib/nogc_sync_mut/io/windows_pty_launch_config.spl | 79e899395d2273e5aeb20fd9bfbaaf79e9f676787ea7aa7570168d607d87126d |
| src/lib/nogc_sync_mut/io/windows_pty_environment_owner.spl | f1844e7bb46fb9d858da6d894f32db5d95deae29bb82036988458d7caa39f308 |
| src/lib/nogc_sync_mut/io/windows_pty_owner.spl | 6b958ac710e23a229516c5183398b115b78fdaf5aafaab8c345656c06165892b |
| src/lib/nogc_sync_mut/io/windows_process_owner.spl | 3fa1e2c4992fa160c735e7d8849a1ce187702f4ca74ed4948e15c162ca0c238b |
| src/lib/nogc_sync_mut/io/windows_process_text.spl | d440c43ab58a6cae2c251fedb76e4ad88e65bd534b3af31c1e377a2db7420d2c |
| test/01_unit/lib/io/windows_pty_launch_config_spec.spl | 080c6c0967d4fe99dbcd3bd9cc3778f591c018e33b3032de8321281fc2b0e738 |
| doc/06_spec/01_unit/lib/io/windows_pty_launch_config_spec.md | 93d5ab40a215fe897f6e4f95a102b1d6328e4cd8027c8a4a0f38b653f27a4a9a |
| test/fixtures/compiler_entrypoint/windows_pty_launch_probe/main.spl | 9f48029ee14b12a101657fdd37a8548cc27fbaf69a1e3972ad8186924c72547b |
| test/fixtures/compiler_entrypoint/windows_pty_launch_probe/environment.spl | de0c7cb69b161803b08423db1c2cbc5ab7852d37357abc326f47df4f315c8d65 |
| doc/09_report/coremux_windows_pty_launch_source_2026_10_25.md | d4f7c73c581152433bc30d2a901a76d22c4b66fa910d552f1857904f58f0b3f5 |

### P1 disposition

windows_pty_owner.spl:166 defines one cleanup-completion predicate used by
cleanup_proof_v1 and both close returns (477 and503). It requires closed state,
observed termination, no recorded release failure, released retained
arena/process/Job/thread/temporary/snapshot authority and no pending operation.
Historical state.failed no longer prevents discharge of proven completion.
The existing full native-resource release checks still establish closed state;
actual release failure remains sticky.

Original spawn/I/O diagnostics remain intact. The missing-executable/cwd fixture
still requires successful actual close AND cleanup_proof; it was not weakened.
The source contract defect is closed. Execution of failed-admission cleanup
remains a mandatory native gate.

### P2 disposition and shared caller compatibility

New windows_process_text.spl uses canonical boxed_text_bytes_checked and
utf8_bytes_valid. Counting and decoding advance a monotonic byte offset after
strict validation. Exact UTF16 allocation includes a zero terminator and checks
signed size overflow before HeapAlloc. Supplementary scalars emit surrogate
pairs; malformed input is refused before native allocation. No later fallible
native operation occurs between successful allocation and pointer transfer.
The caller still owns and releases the returned pointer.

CRT quoting copies raw bytes into a checked exactly sized array, doubling
backslashes only before a quote or the closing quote. Literal Unicode is
preserved; malformed raw bytes are preserved by quoting and refused by strict
wide admission. The existing text-returning quote API fails closed on
allocation/extraction failure. Configured launch uses the Result-returning
form and checks total command size, strict encoding and the UTF16 limit.

windows_process_owner.spl retains both exported helper signatures and delegates
only their bodies. Inspected existing process/worker/file/PTY callers check
zero wide pointers before native use. Internal NUL-separated process environment
blocks still work: the shared wide helper allows NUL content and appends a
terminator. Public configured launch fields still reject NUL. Inherited raw
UTF16 environment entries remain on their unchanged native path.

Configured command assembly now builds checked byte parts and one final array,
avoiding repeated growing-command concatenation. General process/worker command
concatenation outside this feature is unchanged; no global linearity claim is
made for all older shared callers.

Four added unit scenarios exercise malformed UTF8 classes, exact raw quote
bytes, internal/public NUL distinction, and a near-one-MiB Unicode environment
value. The native helper adds invalid-wide rejection and exact code-unit checks
for Korean text, supplementary scalar, embedded NUL and final termination.
These are meaningful authored controls, not timing, allocation-failure injection,
or native execution evidence.

### Final scope and evidence limit

This rereview covered changed/added sources and shared-helper callers, without
repeating the unchanged full v1 audit. No production edits, executable launches
or commits were made. All earlier native prerequisites and failure-injection
gaps remain. Source acceptance does not admit a provider or establish runtime
parity.
