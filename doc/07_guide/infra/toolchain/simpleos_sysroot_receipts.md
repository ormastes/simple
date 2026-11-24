# SimpleOS sysroot provenance receipts

The canonical sysroot builders publish `share/simpleos/sysroot-receipt.sdn`
only after successful compilation and archive composition. They capture owned
source/header inputs before compilation and require the same inputs afterward.
Fresh object generations prevent mtime reuse or leftover objects from entering
an archive. The x86_64 Makefile runs in isolated staging with explicit CC/AR
overrides; its expanded CFLAGS/ASFLAGS are retained.

The receipt binds target, recipe and receipt-owner hashes, source-input ledger,
compiler/archiver identities, build flags, CRT, libc archive and artifact/member
ledgers. The adjacent files are `sysroot-inputs.sdn`, `sysroot-artifacts.sdn`,
`sysroot-members.sdn` and `sysroot-build-flags.txt`. Member hashes record build
provenance; SDK consumers validate immutable archive bytes without requiring
the producer's archiver. The scope is owned libc/runtime inputs, not optional
vendored C++ libraries. This is not a signed third-party attestation.

SDK consumption checks target, current required source/recipe identity and
installed artifact hashes. It does **not** require a local copy of the original
compiler or archiver: a prebuilt cross-host SDK remains consumable. Builder
reuse additionally checks current compiler, archiver and flag bytes. There is
no whole-HEAD pin, timestamp admission or existence-only archive admission.

`check-cross-compile-matrix.shs` refuses missing or stale SimpleOS SDK receipts
before compiling tools; it never silently rebuilds the sysroot. Explicitly build
a fresh target sysroot using its canonical builder. Output-root overrides are
`SIMPLEOS_SYSROOT` for the generic x64 builder, `SIMPLEOS_SYSROOT_AARCH64`,
`SIMPLEOS_SYSROOT_RISCV64` and `SIMPLEOS_SYSROOT_32` for the dedicated builders.
Preserve existing qualified archives and retain receipts alongside new outputs.

`stdio_source_profile` records the x64 fd-preserving FileWrite-32 source profile
or the other architectures' legacy serial profile. Both remain execution
unqualified: every receipt says `runtime_qualification: none`. Source provenance
does not establish guest output capture, descriptor ABI correctness, complete
runtime closure, tool execution, or stage admission. The pure-Simple core
archive is a separate compiler-produced input, not this libc receipt.

Focused guard regression:
`sh test/01_unit/os/port/simpleos_sysroot_receipt_test.shs`. It builds a real
small Clang ELF32/archive fixture and tests missing/stale/tampered provenance,
foreign producer paths and stricter builder reuse. It does not execute a guest
or qualify a SimpleOS SDK.

The pure-Simple validator `simpleos_sysroot_receipt.spl` also guards canonical
native-build userland links before engine selection, including the x64 special
route shared by lld and the internal linker. Explicit x64 CRT/libc overrides
must retain the validated SDK's byte identities. Arbitrary caller linker scripts
remain supported as distinct caller inputs. Their actual path/hash and the SDK
receipt identity are compared before and after each fresh link. Both native and
internal engines share this binding.
Caller runtime archives are bound separately without claiming SDK ownership. Shared user links require the
`libsimpleos_all.a` aggregate in the artifact/member ledgers; x64 requires its
default SDK `libsimple_runtime.a`. An installed but unlisted aggregate cannot
become a checked link input. Compiler-produced external simple-core overrides
require separate caller admission; they are not artifacts qualified by this SDK
receipt.

The validator uses the common SDN parser, bounded no-follow reads and native
file hashes, with no process launches, local
CC/AR probing, globbing or source-tree scans. Only declared ledger entries are
read. Metadata reads are limited to 32 KiB per receipt, 2 MiB per ledger and
2048 entries; CRT header inspection is limited to a 1 MiB object.

This backend source and its focused `.spl` regression still need execution on
an admitted runtime. Shell guard evidence does not establish backend execution
or full SDK invalidation admission. The separately produced simple-core archive
also needs its own compiler admission; this receipt does not qualify it.

SimpleOS authoritative link receipt lookup **and publication are disabled**
until custom linker-script dependency closure (including INCLUDE/INPUT/GROUP/
SEARCH_DIR) and the exact selected generated-entry compiler/link engine are
proven. Every SimpleOS request still checks SDK artifacts and actual caller
inputs, then links fresh. Non-SimpleOS link caching is unchanged. No authoritative SimpleOS output cache receipt is published.
