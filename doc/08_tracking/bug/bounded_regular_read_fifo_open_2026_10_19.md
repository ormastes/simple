# Bounded regular-file reads can block opening an unwritten FIFO

Status: source repair authored; compile and runtime qualification **UNRUN**.
Severity: P1 (unbounded wait before the regular-file admission check).
Scope/base: `work/phase3-canonical-cas-publication-20261019`, `fe1bb38b5d2`.

Related caller defect: [Canonical CAS publication winner verification](canonical_cas_publication_unverified_winner_2026_10_19.md).
Its winner-read path exposes this separate raw-provider FIFO defect; the parent
CAS implementation and CAS11 artifacts remain unchanged by this repair.

## Failure and requirement

A path intended for a regular receipt or CAS object can name a FIFO. Opening it
read-only before checking its opened descriptor waits for a writer; the existing
same-descriptor regular-file check is never reached. A byte ceiling does not
bound that wait. Reject a FIFO without a writer through the existing refusal
contract, while preserving the ordinary-file bounds, content, and handle rules.

## Actual owners and source selection evidence

| Provider | Entry points / selection evidence |
|---|---|
| `src/runtime/runtime_native.c`, `rt_read_regular_no_follow_buffer` | Shared by `rt_file_read_regular_no_follow_bounded` and its `_bytes` sibling. The source header identifies the LLVM native runtime bridge; `src/compiler/70.backend/backend/llvm_backend.spl:395` declares the text ABI. `scripts/bootstrap/materialize-source-packet.py:180` includes this native provider in source packets. Existing real-provider selfchecks include `src/runtime/test/rt_bounded_read_allocation_selfcheck.c`. |
| `src/runtime/runtime.c`, `rt_file_read_regular_no_follow_bounded` | Text-only provider; `src/compiler/80.driver/driver_api_project_build.spl:134` selects this translation unit for its C++ project-build runtime object. This file does not define the bounded bytes twin. |
| `src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs`, `rt_read_regular_no_follow_buffer` | Shared by two exported `#[no_mangle]` runtime ABI entry points. `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:2173` and the following entry register both names. |
| `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`, `open_regular_no_follow` | Exactly two callers, the bounded text and bytes extern implementations. `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1526` registers text and the following registration registers bytes. |

`src/lib/nogc_sync_mut/io/file_ops.spl:105` and `:135` are pure-Simple
facades; they delegate to these raw ABI owners. A facade precheck cannot repair
the kernel open and would introduce a pathname race. The table establishes
source wiring, **not** which artifact is running elsewhere: no live executable,
archive, cache, or build was inspected or modified for this repair.

## Narrow repair and preserved behavior

Add `O_NONBLOCK` to those four Unix opens. C still calls `fstat` on the opened
descriptor and Rust still calls `file.metadata()` on the opened `File`. All
nonregular modes are refused before reading. `O_NOFOLLOW` and `O_CLOEXEC` remain.
No pathname `lstat` precheck, changed error code, or new nil representation is
introduced. Ordinary regular-file I/O ignores the nonblocking open flag.

The C shared helper still reaches `done`/`close(fd)` on nonregular refusal; the
compatibility C provider closes directly; Rust drops its owned `File` on return.
Bounds, post-stat growth detection, NUL/count handling, empty-file behavior,
existing Rust UTF-8 validation, and Windows branches are untouched. C and Rust
already differ in some diagnostics and text-validation behavior; this patch
does not claim to harmonize those pre-existing contracts. Device refusal follows
the unchanged same-handle regular-file predicate; no device runtime test is
included because every regression fixture must stay within the private root.

## Authored regression (not executed)

`src/runtime/test/rt_bounded_read_fifo_selfcheck.c` links the actual C ABI owner;
it contains no copy of the bounded-read algorithm and no mocked open/stat/read.
It creates a private `mkdtemp` directory under an explicit scratch parent,
mode-0600 FIFO/regular files, an empty file, and a relative symlink. No writer
opens the FIFO. Every fixture is removed after the cases finish.

Seven cases per lane: unwritten FIFO at positive and zero limits; exact counted
UTF-8 plus embedded NUL content; empty file at zero limit; oversize, symlink, and
directory refusals. Each case forks. The child resets/unblocks SIGALRM and sets
a two-second alarm; the parent separately uses a three-second monotonic deadline,
SIGKILL, and waitpid. A signal, timeout, nonzero exit, wrong diagnostic, wrong nil,
or incorrect returned bytes is a failure. The old provider is expected to fail
the two FIFO cases within the deadlines; this expectation is source-derived,
not an executed baseline result. `NDEBUG` is rejected at compile time.

## Deferred exact test plan and artifact authority

1. Root selects a fresh isolated output/scratch directory and a provider build
   receipt. Record source commit/patch hash, compiler/version, target, complete
   provider compile/link commands, runtime object/archive hashes and link map.
   Never substitute a live frozen build or mutate a shared cache. Source-only
   admission here does not authorize a build or run in this repair session.
2. Compile the harness object with these flags, from the repository root:

   ```sh
   cc -std=c11 -O2 -g -Wall -Wextra -Werror -c \
     src/runtime/test/rt_bounded_read_fifo_selfcheck.c \
     -o "$FIFO_OUT/native-probe.o"
   cc -std=c11 -O2 -g -Wall -Wextra -Werror -DTEXT_ONLY -c \
     src/runtime/test/rt_bounded_read_fifo_selfcheck.c \
     -o "$FIFO_OUT/compat-probe.o"
   ```

3. Link `native-probe.o` to the admitted actual `runtime_native.c` object and
   its recorded dependency closure; link `compat-probe.o` to the admitted actual
   `runtime.c` object and its recorded string/support dependency closure. Reuse
   the exact provider receipt's target/ABI flags and system libraries, replacing
   only the test entry object/output. Emit a link map and confirm each tested
   bounded-read symbol resolves to the intended object. No extracted helper,
   replacement extern, duplicate-symbol allowance, or unqualified mixed runtime
   is acceptable. Receipt-dependent link inputs cannot be named truthfully until
   root selects those artifacts; there is no complete standalone link claim.
4. Run each linked executable exactly once with the scratch parent as its sole
   argument, additionally guarded by `timeout --kill-after=2s 60s` on Linux.
   Native expected result: exit 0, **14/14** cases. Compatibility expected result:
   exit 0, **7/7** cases. Record stdout/stderr, duration, and process exit. For a
   baseline witness, link the same harness against the pre-fix selected provider:
   require nonzero exit specifically from bounded FIFO timeout/signal failures,
   with the ordinary controls succeeding. Baseline runs remain unexecuted here.
5. Rust changes are source-parity repairs only. This C harness does not qualify
   Rust RuntimeValue ABI or Rust interpreter behavior. An explicitly authorized
   Rust-provider run must use that provider's own ABI/runner and a process deadline;
   no Rust seed/test execution occurs in this lane.

## Evidence boundary

Only source inspection and bounded diff/scope checks are authorized in this lane.
Compilation, kernel behavior, full suites, source439 rebuild, Simple CAS11,
MCP/LSP, cross-host qualification, and release are **UNRUN**. The parent owns the
combined qualification report at
`doc/09_report/compiler/canonical_cas_fifo_qualification_2026_10_19.md`.
