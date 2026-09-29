# Rust SimpleOS PAL filesystem policy migration blocker

Status: blocked before policy migration; static review only (2026-08-26).

## Current production link

`src/os/port/rust/build.shs` links Rust programs with `-lsimpleos_c` and no
Pure Simple object or archive. `src/os/libc/Makefile` builds that archive only
from its listed C and assembly sources. The offline Cargo path likewise names a
SimpleOS sysroot, but does not establish a Pure Simple policy archive in the
PAL link. Consequently an `@export("C")` policy function would be unreachable,
and declaring it from Rust would turn a currently linkable PAL into an
undefined-symbol consumer.

The live `open(2)` ABI accepts already-resolved POSIX flags. Moving only flag
selection to the kernel would require a new request ABI and would change the
existing C/POSIX boundary, so it is not a minimal policy-only migration.

## Prerequisite

Choose and establish one non-circular production carrier before migrating
`OpenOptions` policy:

1. Produce a freestanding, no-runtime Pure Simple object containing only the
   scalar filesystem-policy exports, archive it into the Rust sysroot, and link
   it before `libsimpleos_c.a`; or
2. Define a general generated-Pure-Simple policy archive for foreign-language
   PALs and make the Rust sysroot/build own its symbol-closure verification.

Either carrier must prove all target architectures, must not import heap or
runtime services, and must keep the existing `open(path, flags, mode)` C ABI.
The policy interface can then be scalar and O(1): six boolean option inputs and
one integer flag result, plus scalar operation/result inputs and one stable
error-kind result. Rust retains `Path`/`OsStr`, `CString`, and `io::Error`
adaptation; C retains only POSIX/syscall adaptation.

## Independently safe repairs in this lane

The Rust `RawStat` adapter was shorter than C `struct stat`, allowing `stat` to
overwrite it. It now mirrors the fixed-width C layout and has compile-time
size/alignment/offset assertions. `create_new` now owns independent state,
emits `O_CREAT | O_EXCL`, and suppresses `O_TRUNC`, matching exclusive-create
precedence. Both the live patch tree and the authored libstd patch are aligned.

## Frozen parity obligations

`test/fixtures/os/port/rust/simpleos_fs_policy_parity_vectors.sdn` freezes the
request/result corpus for the eventual Rust adapter, C oracle adapter, and
canonical Pure Simple policy. It is explicitly authored-unexecuted and makes no
parity, coverage, or MC/DC completion claim. Execution sources must not be
added until the production Pure Simple carrier exists, because doing so would
otherwise duplicate the policy merely to produce green tests.

