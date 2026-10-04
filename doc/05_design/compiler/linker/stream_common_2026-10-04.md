# COMMON symbols in retained streamed ELF links

Base: `63d5f8b20208c92275cfb4c9a105a26b2b51b774`; date: 2026-10-04.
Owner/session: linker_research; worktree
`C:/dev/simple-item4-stream-common-docs-20261004`; branch
`work/item4-stream-common-docs-20261004`; target release/1.0.
Public streaming APIs remain unchanged. Simple execution is UNRUN.

## Local gap and implementation contract

At the integration base, `elf/stream_inputs.spl` rejects SHN_COMMON (65522) with
GNU-unique/TLS/IFUNC symbols. Its charged, cancellable retained-file scans already
own archive selection and global lookup. `elf/stream_layout.spl` computes
placement by rescanning selected metadata with only segment summaries resident.
The new implementation belongs to those owners and their stream emission/type
support, not a resident symbol dictionary or an uncharged archive pass.

Resolution precedence is strong regular definition, then global COMMON, then
regular weak definition. Coalesce selected COMMON declarations using independent
maximum size and maximum alignment; the record containing one maximum need not
contain the other. Keep a deterministic first-common owner/table/ordinal as the
canonical allocation identity, so repeated references allocate once. Strong
regular definitions override tentative allocation; duplicate strong regular
definitions still fail. Do not broaden TLS/IFUNC or GNU-unique admission.

Allocate canonical common records in a synthetic aligned zero-filled RW tail.
Check alignment, overflow and output limits before growth. Symbol resolution and
relocation consumers must use those actual allocated addresses. Include common
bytes in the output plan and emit zeros in existing bounded windows. Preserve
the explicit mutable-owner transitions and retained handle cleanup on failure.

Every rescan and decoded record consumes the existing scan budget and observes
cancellation. Auxiliary state may be constant per scan; that does not make the
algorithm constant-time. This is a source-level bounded-window implementation,
not measured RSS or whole-job resource enforcement. Keep UnsupportedBudget at
the external admission boundary until enforcement exists.

## Primary domain evidence

[GNU BFD 2.42, archive symbol processing](https://sourceware.org/binutils/docs-2.42/bfd.pdf)
describes pulling a real non-common definition for an undefined or common
symbol. Its worked backend example is a.out, so it alone does not prove every
ELF archive edge case.

[Oracle archive processing](https://docs.oracle.com/en/operating-systems/solaris/oracle-solaris/11.4/linkers-libraries/archive-processing.html)
describes tentative-to-data extraction; [Oracle symbol resolution](https://docs.oracle.com/en/operating-systems/solaris/oracle-solaris/11.4/linkers-libraries/simple-resolutions.html)
gives global definitions precedence over weak definitions and regular
definitions over tentative declarations of equivalent binding.

LLD is not an interchangeable oracle for tentative-triggered extraction:
[LLVM D122450](https://reviews.llvm.org/D122450?id=419176) changed its default to
`--no-fortran-common`; [upstream removal](https://lists.llvm.org/pipermail/llvm-commits/Week-of-Mon-20260907/2029757.html)
subsequently removed that switch. These primary sources were searched on
2026-10-04. The implementation contract below follows the directly observed GNU
ELF behavior, not a presumed LLD default.

## Executed external fixture oracle

One experiment used WSL Ubuntu GNU ld (Binutils) **2.46**, GNU `as --64`, `ar rcs`
and `readelf -sW`; artifacts remain under this worktree's
`build/common-oracle`. This executed external assembler/linker tools only.
No Simple runtime was built or invoked.

Inputs: root `_start: ret` plus `.comm x,8,8`; strong member defines x as an
8-byte initialized object and `strong_marker`; common member has
`.comm x,32,32` and `common_marker`; weak member defines an initialized weak x
and `weak_marker`. A separate root contains a real undefined `.quad x`.
Member-only markers distinguish extraction from coincidentally equal values.

| Link inputs | Observed GNU result |
| --- | --- |
| common root + strong archive | strong marker present, x in data, size 8 |
| common root + larger common archive | common marker absent, x size 8 in BSS |
| common root + weak archive | weak marker absent, x size 8 in BSS |
| undefined root + common archive | common marker present, x size 32 in BSS |
| common root + direct weak object | weak marker present because directly selected; x remains global common allocation, size 8 |

Thus tentative demand extracts a strong regular definition, but not weak or
common-only members. True unresolved demand can extract a COMMON member.
A common member selected for another unresolved symbol contributes its common
declarations to normal coalescing. Weak undefined references alone do not create
strong archive demand.

At the integration base, fast `elf/archive_closure.spl:62` excludes COMMON
candidates even for real undefined demand. This conflicts with the fourth
experiment; root has authored the fast-path correction and parity regression.
Streaming ownership does
not silently absorb the fast-engine source file.

## Test-first acceptance

Use real assembled objects and archives through the retained streaming job,
with fast-engine comparison where their supported contracts overlap. Inspect
relocated addresses, aligned RW extent and zero bytes independently; image layout
differences do not require byte-identical complete files unless both writers
promise the same layout. Cover reversed common declarations with independent
size/alignment maxima, repeated references, strong override, weak precedence,
all four archive cases above, invalid alignment, overflow/output budget,
scan exhaustion, cancellation and cleanup. Guard setup and byte ranges explicitly.

Runtime owns the stream source slice, acceptance owns fixtures/spec/manual,
research owns this design and source review, and root owns fast parity repair
and common integration ledger. Sidecars: N/A. Authored tests, source review and
external GNU evidence do not replace Simple runtime, coverage, full compiler,
performance or generated-manual evidence for Phase 4.
