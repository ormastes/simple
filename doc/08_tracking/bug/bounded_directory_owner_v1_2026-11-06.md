# Bounded directory observation V1

The legacy `rt_readdir` eagerly allocates the entire listing. Checking its count
in Simple cannot impose an allocation budget. That compatibility API is unchanged.
The additive canonical `std.nogc_sync_mut.io.directory_entries_bounded_v1` returns
only complete bounded snapshots or explicit errors. Traversal, sorting and hashing
policy remain in Simple.

## ABI and ownership

`rt_directory_list_bounded_v1(path, entries, name_bytes)` takes one tagged text
argument plus two i64 limits. A positive generation token owns a complete snapshot;
negative results mean invalid input (-1), entry quota (-2), name quota (-3), I/O
(-4), unsupported (-5), allocation (-6), nofollow/type refusal (-7), invalid UTF-8
name (-8), or exhausted live-owner quota (-9). No truncated snapshot is returned.
Count/kind/size/name accessors validate the token under the owner registry lock.
Free consumes once; stale/reused generations cannot access freed storage. Names
are copied under the lock; invalid name access yields empty text and scalar
accessors reject it. Safe callers never expose raw tokens.

The hard bounds are 65536 entries and 16 MiB total name allocations INCLUDING NUL
bytes, plus one fixed metadata array of `max_entries * sizeof(entry)` and one
fixed owner record. Admission precedes allocations. The generation registry has
64 slots including in-flight allocations, imposing a finite concurrent-owner
ceiling. There is no process-global observation scratch. Entry kind is 1 regular,
2 directory, 3 symlink, 4 other; size is observed metadata, not retained identity.

`directory_path_probe_v1` uses the same owner, returning kind 0 only for ENOENT.
Other failures are errors. Listing opens the final directory with O_NOFOLLOW and
uses fstatat(..., AT_SYMLINK_NOFOLLOW) for names. Trailing separators are stripped
except filesystem root so a final symlink cannot evade nofollow. Ancestor
components must be trusted; neither metadata nor listing is a hostile-ancestor
transaction. Consumers still use bounded nofollow content reads and compare size.

## Providers and evidence

The identical implementation header is included by mutually exclusive
runtime_core_exports.c and runtime.c. Their legacy listing layouts remain
unchanged. runtime.h, Simple externs and Rust codegen signatures agree on tagged
text. Linux, macOS and FreeBSD have the POSIX implementation. Windows/other hosts
and the Rust interpreter explicitly return unsupported for the new capability;
this is NOT platform qualification. No Rust seed was executed.

Initial native C selfcheck PASS on Darwin arm64; added trailing-slash symlink
regression then reran once after that implementation change: PASS. It exercises
real empty/small/over-budget directories, names-before-allocation accounting,
regular/symlink metadata and cycle refusal, missing/error distinction, injected
allocation and close failures, complete EOF, stale/double-free refusal and all
64 live owners. Tagged strings are test ABI shims; filesystem calls and the
provider implementation are real. Simple facade tests remain AUTHORED / NOT_RUN.
All other platform executions remain NOT_RUN. This bounded observation component
does not certify the overall source-analysis or compiler-memory goal.

## Captured static integration evidence

The first limited two-provider C checker run reported 458 PASS /122 FAIL /
24 UNTESTED across unrelated legacy rows, and did not discover public definitions
inside the shared implementation header. It is NOT an overall PASS. Complete
output: `/tmp/check-rt-c-contract-compile.py.bounded-directory-v1.log`.
Public wrappers were then made explicit in both provider C files, leaving one
shared static implementation. The native selfcheck now compiles the actual
runtime_core_exports.c provider (with tagged text test shims) and passed after
that integration change.

The exact seven new symbols were then checked with the existing C contract
checker against both providers: **14 PASS /0 FAIL /0 UNTESTED**, compile only,
current Darwin arm64 host. Log: `/tmp/directory-bounded-v1-exact-contract.log`.
This does not classify or waive the unrelated broad-matrix failures.

Pointer/reference mapping: PASS, 265 checked edges, no new findings; host mapping:
PASS, 875 edges, no new gaps, SimpleOS UNKNOWN. Logs:
`/tmp/check-rt-pointer-ref-map.py.bounded-directory-v1-wrappers.log` and
`/tmp/check-rt-host-map.py.bounded-directory-v1-wrappers.log`. The seven symbols
are now visible to the source maps. Mapping still does not imply Windows support.
OS directory enumeration has its own fixed buffered DIR state in addition to
caller-budgeted entry metadata and copied names; no whole-directory materializing
API is called by the bounded owner. Unsupported-host and interpreter branches
are explicit failures, not successful empty observations.

## Review precision and new controls

Complete means enumeration reached EOF and closed successfully. It is NOT a
point-in-time atomic namespace snapshot: concurrent directory mutation can change
which names are observed without generating a syscall error. This owner provides
bounded observation, not a filesystem transaction or hostile-filesystem sandbox.
O_NOFOLLOW protects only the final opened directory component; ancestors are not
retained and must be trusted against replacement. Entry metadata is observed via
the retained directory FD, but subsequent path-based traversal/content opens have
their own race and trusted-ancestor assumptions.

The native test now offers `--new-controls`: deterministic test-only readdir
failure after one real entry (no partial success, all allocations freed and DIR
closed), plus concurrent accessor/free/generation-reuse stress. Fault injection
exists only through a compile-time test hook; production defaults directly to
readdir, with no runtime configuration knob. No unchanged ABI/maps were rerun.

New-controls execution: PASS on Darwin arm64 with the actual core-C provider.
The test runs one reader thread through 20000 accessor rounds concurrently with
2000 owner create/free/reuse iterations. The deterministic readdir-error control
fails after one non-dot entry, checks zero outstanding tracked allocations and
one closed DIR, and receives I/O failure rather than empty/partial success.
Two test harness build issues (argument forwarded to compiler, missing errno
include) were corrected before the successful execution. No unchanged native
cases, ABI matrix, pointer map or host map were rerun. This stress execution does
not prove all schedules or other hosts; Simple facade execution remains NOT_RUN.
