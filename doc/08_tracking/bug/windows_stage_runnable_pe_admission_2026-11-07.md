# Windows stage runnability guard misses PE executables

Status: fix-implemented-verification-pending. Windows host regression passed;
independent source review approved. Production-stage verification is pending.
Parent: `windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02`.
The parent remains OPEN: this child does not fix extern census evidence or
the unresolved-runtime-symbol guard's platform oracle.

## Current Windows-specific failure

Base release: `9e7e7a526edb43ab29171d920449367e5fd48127`.
Isolated source: `D:/dev/simple-windows-stripped-symbol-guard-20261107`.
The existing guard's Windows private selftest exited 2, with only 6/11
fixtures correct. Raw output is retained at
`D:/dev/simple-windows-stripped-symbol-evidence-20261107/runnable-before.log`.

The guard enumerates tracked `bootstrap/**/simple` but omits the Windows
`simple.exe` name. It recognizes a DOS MZ prefix as generic `pe`, without
checking the PE signature or COFF architecture, while host format/triple
recognition has no MSYS/Git Bash/Cygwin Windows branch. Its POSIX executable
permission check also precedes foreign-format classification: MSYS cannot
apply POSIX chmod expectations to foreign blobs and shebang files on NTFS.
The legacy selftest consequently reports foreign/native/skip fixtures
incorrectly and cannot admit any scan on this Windows host.

## Focused repair

Extract the existing three format/host/triple helpers into
`scripts/check/lib/stage-binary-platform.shs`, retaining Unix branches.
Add Windows host formats/triples and decode DOS e_lfanew, the PE signature,
and the complete COFF header before choosing x86-64, ARM64, i386, or other.
Malformed PE headers are named offenders, never foreign skips.

The guard now enumerates `simple.exe` too. Foreign-format, malformed-header,
and unscoped-native classification precede the platform-dependent executable
permission check. Actual native probes remain the final runnability evidence.
Windows selftest headers use PE/COFF rather than ELF, and the unexecutable
fixture models an unexecutable file rather than an unsupported NTFS chmod
assumption. The guard remains below 800 lines.

## Tests and evidence boundary

`scripts/check/check-stage-binaries-runnable-windows.ps1` builds private tiny
native C programs with the installed host compiler, stripped of COFF symbols.
These are guard fixtures, never Simple compilers or bootstrap producers.
The checker verifies that `nm` yields no defined symbols, then invokes the
production guard once on a private Git index containing positive/negative
native PE fixtures, a foreign-machine header mutation, a malformed PE, and
an unscoped executable. The expected result includes six actual native
invocations, four named offenders, and one explicit foreign skip.

The foreign architecture control changes only COFF machine bytes: it does
not claim to turn x86-64 code into an executable ARM64 program. PE header
classification is not complete loader validation; only actual host execution
proves runnability. Partial PE export sets are never substituted for complete
defined-symbol evidence.

The private host regression passed: the production guard's legacy selftest
reported 11/11 fixtures correct; the combined stripped-PE scan executed six
native invocations, named four intended offenders, and explicitly skipped
one foreign-machine control. The symbol reader succeeded with an empty
defined-symbol result before the fixture was called stripped. Raw logs and
the receipt remain under
`D:/dev/simple-windows-stripped-symbol-evidence-20261107/native-after/`.
This validates the host guard's controls, not any Simple compiler's behavior.

Independent reviewer `/root/astra_linker_final` approved the four-file child
repair with no blocking/P0/P1 findings and inspected the retained before/after
logs, native invocation counts and successful symbol-reader evidence. The
source/program/tool identities are recorded in `qualification.sdn` beside the
raw logs. i386/ARM64 host execution and actual Simple stage artifacts are not
qualified by these x86-64 Windows fixture results.

No seed, admitted self-hosted producer, live bootstrap source, shared cache,
or another lane's runtime is executed or changed. Source landing must retain
`fix-implemented-verification-pending` until appropriate owner verification;
no compiler/bootstrap admission or complete parent-bug fix is claimed.
