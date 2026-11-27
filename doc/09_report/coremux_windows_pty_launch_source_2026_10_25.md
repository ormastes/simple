# Windows configured PTY launch source handoff — 2026-10-25

Status: **AUTHORED / NOT_RUN**. No compiler, build, test, helper, product or native
process was launched. No commit was created. This is not provider admission,
verification PASS, bootstrap evidence, a generated manual, or a usable-product
claim. An admitted pure-Simple producer and actual native execution are required.

## Interface and owned source

Applications import `std.sosix.pty` under explicit configured library mode.
`sosix_pty_spawn_configured_v1(handle: i32, launch: PtyLaunchV1)` returns
`Result<i64, text>`. `PtyLaunchV1` carries mode, optional cwd and ordered
environment changes. Modes are `Exec(executable, argv)` and `Shell(command)`;
changes are `Set(name, value)` and `Remove(name)`. Geometry remains in PTY open.

Production paths:

- `src/lib/sys/pty_launch.spl`: portable values.
- `src/lib/sys/pty.spl`: explicit unsupported result for the legacy runtime ABI.
- `src/lib/nogc_sync_mut/sosix/pty.spl` and
  `src/lib/nogc_async_mut/sosix/pty.spl`: generic facade reexports.
- `src/providers/windows_native/lib/sys/pty.spl`: native configured entrypoint.
- `src/lib/nogc_sync_mut/io/windows_pty_launch_config.spl`: bounded validation,
  command composition, trusted system shell and native launch storage.
- `src/lib/nogc_sync_mut/io/windows_pty_environment_owner.spl`: native environment.
- `src/lib/nogc_sync_mut/io/windows_pty_launch_abi.spl`: four narrow Win32 APIs.
- `src/lib/nogc_sync_mut/io/windows_pty_owner.spl`: retained PTY/Job admission.
- `src/lib/nogc_sync_mut/io/windows_process_text.spl`: shared checked linear
  UTF-8 byte admission, CRT quoting and UTF-16 conversion.
- `src/lib/nogc_sync_mut/io/windows_process_owner.spl`: only the existing
  quote/wide helper implementations delegate to that shared owner.

All files are below 800 lines. No smux service/API, common mux contract, wire,
client, guard, runtime C ABI or bootstrap source was edited by this lane.

## Source invariants and limits

Exec shares the process owner's CRT byte-quote implementation and
`_windows_process_wide_v1`. `CreateProcessW` receives an explicit application
and separately quoted argv; no shell reparses Exec. Executable path resolution
follows native non-NULL `lpApplicationName` rules; this API does not invent PATH
search. Shell gets `cmd.exe` from a bounded `GetSystemDirectoryW` query, ignoring
COMSPEC/PATH for shell selection, and preserves raw command text under `/D /S /C`.

Cwd goes directly to CreateProcessW. No environment changes means NULL native
inheritance without snapshot allocation. Otherwise GetEnvironmentStringsW
provides the parent block. Untouched UTF-16 units, including hidden drive keys,
are copied without decoding/re-encoding. CompareStringOrdinal with ignore-case
implements name ordering/equality; changes apply in request order. Public names
containing `=` are rejected. The parent environment is never modified.

Bounds: 256 args/changes, 1 MiB public text, 32766 command UTF-16 units, 4096
environment entries and 1048576 environment UTF-16 units. Sort comparisons are
O(n log n), change lookup is binary search, and each ordered insertion copies at
most the bounded entry list. Invalid input fails before child creation. Missing
native capability, snapshot, comparison, allocation or release returns failure.

The existing suspended creation, checked Job assignment, resume, termination
and quarantine remain authoritative. All preparation allocations and unreleased
OS snapshots stay owned on failure; failed cleanup cannot become a clean proof.
Legacy spawn retains raw-command behavior, NULL app/env/cwd and its original
creation flags. Configured spawn adds CREATE_UNICODE_ENVIRONMENT.

## Authored scenarios and required execution

`test/01_unit/lib/io/windows_pty_launch_config_spec.spl` has real value/error
assertions for REQ-WPL-001 through REQ-WPL-006, with 13 authored cases after
correction cycle 2. Its same-path manual is authored,
not docgen output.

`test/fixtures/compiler_entrypoint/windows_pty_launch_probe/{main,environment}.spl`
is an actual-child native scenario. Compile it to
`<private path containing spaces and 한글>/windows_pty_launch_probe.exe`, use the
native Windows PTY provider and explicit `--library-mode nogc-sync-mut`, and
start it from a different directory. The runner must supply an inherited native
hidden drive entry (for example `=C:`) and
`SMUX_WPL_PARENT=preserved-한글😀`. Missing setup fails rather than silently skips.
The sibling nonexistent executable/directory names must remain absent.

The scenario checks empty/quoted/trailing-slash/Unicode/literal-shell Exec
arguments, actual cwd, Unicode case replacement, empty values, Set-then-Remove,
PATH removal, inherited Unicode, every untouched native entry, parent snapshot
preservation, trusted Shell under poisoned child COMSPEC, native inheritance,
validation reuse, missing executable/cwd failure and terminal cleanup proof.
It requires child exit zero and observed output before reporting PASS.

Required next evidence: admitted producer/source/backend/provider/config/cache
identity, real SSpec counts, actual-child exit/output, cleanup receipts, bounded
startup/latency/RSS, native link/export closure for all four Win32 bindings,
existing legacy ConPTY regression, and full CoreMux provider admission. Fault
injection for allocation/native-release/Job failure is still required; the
authored negative input/create scenarios do not prove every native failure path.
Unicode argv/console/runtime behavior must be observed, not inferred from source.

## Independent review correction cycle 2

The v1 review found two concrete issues. Production `close` formerly returned
false forever after historical admission/I/O failure even once cleanup proof
was true. Both return paths now use the same terminal resource-discharge
predicate as cleanup proof. Spawn errors and failed-release history remain
unchanged. Pending requests, nonterminal jobs and failed native release cannot
report successful cleanup. The native fixture's strict close-plus-proof oracle
was not relaxed.

The prior Unicode loops called `char_code_at(ordinal)`, whose native provider
rescans from byte zero, and did not strictly validate malformed byte sequences.
The shared helper now uses canonical
`common.text_bytes.boxed_text_bytes_checked` and `utf8_bytes_valid`, then traverses
byte offsets monotonically. UTF-16 storage is sized and overflow-checked before
allocation; malformed UTF-8 is rejected before acquiring that allocation.
Internal environment NUL separators are supported; public fields reject NUL.
Untouched inherited UTF-16 still bypasses all text conversion.

CRT quoting uses two byte passes and one sized output buffer, preserving exact
raw bytes until wide admission rejects malformed data. The configured command
builder combines quoted byte arrays into one checked buffer and propagates
allocation errors. The historical text-returning quote API fails closed on
allocation error because its unchanged signature cannot return `Err`.

Shared-helper caller impact is limited to the existing process owner's path,
file/digest and process-admission conversion calls, `windows_worker_launcher`,
the PTY open/legacy/configured spawn paths, and the new environment/fixture
owners. Valid quoting and embedded-NUL behavior are preserved. Other process
owner code, including its old environment sorting policy, was not rewritten;
there is no claim that its entire launch pipeline is now linear.

New controls cover malformed UTF-8 classes, raw quoting preservation, internal
NUL, near-1MiB multibyte acceptance, native NULL-on-invalid wide conversion and
exact UTF-16 surrogate/terminator output. Source complexity is improved; actual
startup time, latency, RSS and native benchmarks remain **NOT_RUN**. Existing
public bounds were not reduced. The temporary command expansion ceiling cannot
exclude a command that satisfies the original 32766 UTF-16-unit limit.
